defmodule ElixirSense.Providers.Hover.Docs do
  @moduledoc false
  alias ElixirSense.Core.Applications
  alias ElixirSense.Core.Binding
  alias ElixirSense.Core.BuiltinAttributes
  alias ElixirSense.Core.BuiltinFunctions
  alias ElixirSense.Core.BuiltinTypes
  require ElixirSense.Core.Introspection, as: Introspection
  alias ElixirSense.Core.Metadata
  alias ElixirSense.Core.Normalized.Code, as: NormalizedCode
  alias ElixirSense.Core.Normalized.Typespec
  alias ElixirSense.Core.ReservedWords
  alias ElixirSense.Core.State
  alias ElixirSense.Core.SurroundContext
  alias ElixirSense.Core.State.ModFunInfo
  alias ElixirSense.Core.TypeInfo
  alias ElixirSense.Core.TypePresentation
  alias ElixirSense.Core.Parser

  @type markdown :: String.t()

  @type module_doc :: %{kind: :module, docs: markdown, metadata: map, module: module()}

  @type function_doc :: %{
          kind: :function | :macro,
          module: module(),
          function: atom(),
          arity: non_neg_integer(),
          args: list(String.t()),
          metadata: map(),
          specs: list(String.t()),
          docs: markdown()
        }

  @type type_doc :: %{
          kind: :type,
          module: module() | nil,
          type: atom(),
          arity: non_neg_integer(),
          args: list(String.t()),
          metadata: map(),
          spec: String.t(),
          docs: markdown()
        }

  @type variable_doc :: %{
          name: String.t(),
          kind: :variable,
          # Rendered inferred type (best-effort), or nil when nothing useful.
          type: String.t() | nil
        }

  @type attribute_doc :: %{
          name: String.t(),
          kind: :attribute,
          docs: markdown()
        }

  @type keyword_doc :: %{
          name: String.t(),
          kind: :keyword,
          docs: markdown()
        }

  @type doc :: module_doc | function_doc | type_doc | variable_doc | attribute_doc | keyword_doc

  @type position :: {pos_integer, pos_integer}
  @type range :: %{begin: position, end: position}
  @type docs_info :: %{docs: [doc], range: range}

  @builtin_functions BuiltinFunctions.all()
                     |> Enum.map(&elem(&1, 0))
                     |> Kernel.--([:exception, :message])

  @spec docs(String.t(), pos_integer, pos_integer, keyword()) :: docs_info | nil
  def docs(code, line, column, options \\ []) do
    case ElixirSense.Core.SurroundContext.Toxic.surround_context(code, {line, column}) do
      :none ->
        nil

      %{begin: begin_pos, end: end_pos} = context ->
        # HEEx files contain HTML tags whose `>` is tokenized by the Elixir
        # lexer (and by toxic2) as the comparison operator `>`, which surfaces
        # `Kernel.>/2` on hover. That documentation is never useful at an HTML
        # tag boundary, so detect the HTML-tag case and return nil early.
        if html_tag_gt?(code, line, column) do
          nil
        else
          metadata =
            Keyword.get_lazy(options, :metadata, fn ->
              Parser.parse_string(code, true, false, {line, column})
            end)

          env =
            Metadata.get_cursor_env(metadata, {line, column}, {begin_pos, end_pos})

          case all(context, env, metadata) do
            [] ->
              nil

            list ->
              %{
                docs: list,
                range: %{
                  begin: begin_pos,
                  end: end_pos
                }
              }
          end
        end
    end
  end

  # Detects whether the character at `{line, column}` (1-based) is the `>`
  # that closes an HTML tag in a HEEx / HTML-EEx template, as opposed to the
  # Elixir comparison operator `>`.
  #
  # HEEx HTML tags (`<header ...>`, `</header>`, `<.link ...>`, `<:slot ...>`)
  # are tokenized by both the Elixir lexer and toxic2 as Elixir code, so their
  # closing `>` is classified as the `>` operator and surfaces `Kernel.>/2` on
  # hover — never useful. We scan the line up to the cursor tracking the depth
  # of Elixir containers (`()`, `{}`, `[]`); when the cursor `>` sits at depth 0
  # and the nearest unmatched `<` to its left opens an HTML tag name (an ASCII
  # identifier, `.link`, `:slot`, `/header`, ...), it is a tag closer.
  defp html_tag_gt?(code, line, column) do
    line_str = code |> String.split("\n") |> Enum.at(line - 1, "")
    prefix = String.slice(line_str, 0, column)

    String.ends_with?(prefix, ">") and
      (bare_gt_line?(prefix) or tag_closer?(String.to_charlist(prefix)))
  end

  # True when `prefix` is only whitespace followed by a single `>` — the
  # closing `>` of a multi-line HTML tag on its own line. In HEEx this is never
  # the Elixir `>` operator (which would need a left operand on the same line).
  defp bare_gt_line?(prefix) do
    String.trim(prefix) == ">"
  end

  # Scans `chars` (line start up to and including the cursor `>`). Returns true
  # when the trailing `>` closes an HTML tag rather than being the `>` operator.
  # A `>` inside `{...}` / `(...)` / `[...]` (e.g. a guard `when x > 0` inside an
  # attribute expression) is not mistaken for a tag closer because it sits at a
  # non-zero container depth. The last `<` at depth 0 must be followed by a tag
  # name: an identifier, `.component`, `:slot`, or `/closing`.
  defp tag_closer?(chars) do
    # State: {depth, in_string, last_lt_index}
    # in_string: nil | quote_char | {:esc, quote_char} (after backslash)
    {depth, _in_string, last_lt_index} =
      Enum.reduce(Enum.with_index(chars), {0, nil, nil}, fn
        # Inside a string: a backslash escapes the next char.
        {?\\, _i}, {d, q, lt} when q != nil ->
          {d, {:esc, q}, lt}

        {_c, _i}, {d, {:esc, q}, lt} ->
          {d, q, lt}

        {c, _i}, {d, q, lt} when q != nil and c == q ->
          {d, nil, lt}

        {_c, _i}, {d, q, lt} when q != nil ->
          {d, q, lt}

        # Not in a string: track containers and tag openers.
        {c, _i}, {0, nil, lt} when c in ~c"({[" ->
          # Enter a container at depth 0. Keep the pending `<`: if we return
          # to depth 0 before the cursor, it is still the tag opener.
          {1, nil, lt}

        {c, _i}, {d, nil, lt} when c in ~c"({[" ->
          {d + 1, nil, lt}

        {c, _i}, {d, nil, lt} when c in ~c")]}" and d > 0 ->
          {d - 1, nil, lt}

        {?<, i}, {0, nil, _} ->
          {0, nil, i}

        {c, _i}, {d, nil, lt} when c in ~c"'" ->
          {d, ?', lt}

        {c, _i}, {d, nil, lt} when c in ~c"\"" ->
          {d, ?", lt}

        _, acc ->
          acc
      end)

    depth == 0 and last_lt_index != nil and
      tag_name?(Enum.drop(chars, last_lt_index + 1))
  end

  # True when the charlist starts with an HTML tag name: an ASCII letter or `_`
  # (standard tag like `header`), `.`/`:` (component/slot like `.link`/`:slot`),
  # or `/` (closing tag like `/header`) immediately followed by an identifier.
  defp tag_name?([?/ | rest]), do: tag_name?(rest)
  defp tag_name?([?. | rest]), do: identifier_head?(rest)
  defp tag_name?([?: | rest]), do: identifier_head?(rest)
  defp tag_name?([c | _]) when c in ?a..?z or c in ?A..?Z or c == ?_, do: true
  defp tag_name?(_), do: false

  defp identifier_head?([c | _]) when c in ?a..?z or c in ?A..?Z or c in ?0..?9 or c == ?_,
    do: true

  defp identifier_head?(_), do: false

  defp all(
         context,
         %State.Env{
           module: module
         } = env,
         metadata
       ) do
    binding_env = Binding.from_env(env, metadata, context.begin)

    type = SurroundContext.to_binding(context.context, module)

    case type do
      nil ->
        nil

      {:keyword, keyword} ->
        docs = ReservedWords.docs(keyword)

        %{
          name: Atom.to_string(keyword),
          kind: :keyword,
          docs: docs
        }

      {:attribute, attribute} ->
        docs = BuiltinAttributes.docs(attribute) || ""

        %{
          name: Atom.to_string(attribute),
          kind: :attribute,
          docs: docs
        }

      {:variable, variable, version} ->
        var_info = Metadata.find_var(metadata, variable, version, context.begin)

        if var_info != nil do
          rendered_type =
            case TypePresentation.render_hint(binding_env, var_info) do
              {:ok, text} -> text
              :skip -> nil
            end

          %{
            name: Atom.to_string(variable),
            kind: :variable,
            type: rendered_type
          }
        else
          mod_fun_docs(
            {nil, variable},
            context,
            binding_env,
            env,
            metadata
          )
        end

      _ ->
        mod_fun_docs(
          type,
          context,
          binding_env,
          env,
          metadata
        )
    end
    |> List.wrap()
  end

  defp mod_fun_docs(
         {mod, fun},
         context,
         binding_env,
         env,
         metadata
       ) do
    actual =
      {Binding.expand(binding_env, mod), fun}
      |> expand(env.aliases)
      |> Introspection.actual_mod_fun(
        env,
        metadata.mods_funs_to_positions,
        metadata.types,
        context.begin,
        false
      )

    case actual do
      {mod, fun, true, kind} ->
        {line, column} = context.end
        call_arity = Metadata.get_call_arity(metadata, mod, fun, line, column) || :any
        get_all_docs({mod, fun, call_arity}, metadata, env, kind)

      _ ->
        nil
    end
  end

  def get_all_docs({mod, nil, _}, metadata, _env, :mod_fun) do
    doc_info =
      metadata.mods_funs_to_positions
      |> Enum.find_value(fn
        {{^mod, nil, nil}, fun_info = %ModFunInfo{}} ->
          %{
            kind: :module,
            module: mod,
            metadata: fun_info.meta,
            docs: fun_info.doc
          }

        _ ->
          false
      end)

    if doc_info == nil do
      get_module_docs(mod)
    else
      doc_info
    end
  end

  def get_all_docs({mod, fun, arity}, metadata, env, :mod_fun) do
    doc_infos =
      metadata.mods_funs_to_positions
      |> Enum.filter(fn
        {{^mod, ^fun, a}, fun_info} when not is_nil(a) and fun not in @builtin_functions ->
          default_args = fun_info.params |> Enum.at(-1) |> Introspection.count_defaults()

          Introspection.matches_arity_with_defaults?(a, default_args, arity)

        _ ->
          false
      end)
      |> Enum.sort_by(fn {{^mod, ^fun, a}, _fun_info} -> a end)
      |> Enum.map(fn {{^mod, ^fun, a}, fun_info} ->
        kind = ModFunInfo.get_category(fun_info)

        fun_args_text =
          fun_info.params
          |> List.last()
          |> Enum.with_index()
          |> Enum.map(&(&1 |> Introspection.param_to_var()))

        specs =
          case metadata.specs[{mod, fun, a}] do
            nil ->
              []

            %State.SpecInfo{specs: specs} ->
              specs |> Enum.reverse()
          end

        meta = fun_info.meta

        behaviour_implementation =
          Metadata.get_module_behaviours(metadata, env, mod)
          |> Enum.find_value(fn behaviour ->
            if Introspection.is_callback(behaviour, fun, a, metadata) do
              behaviour
            end
          end)

        case behaviour_implementation do
          nil ->
            %{
              kind: kind,
              module: mod,
              function: fun,
              arity: a,
              args: fun_args_text,
              metadata: meta,
              specs: specs,
              docs: fun_info.doc
            }

          behaviour ->
            meta = Map.merge(meta, %{implementing: behaviour})

            case metadata.specs[{behaviour, fun, a}] do
              %State.SpecInfo{} = spec_info ->
                specs =
                  spec_info.specs
                  |> Enum.reject(&String.starts_with?(&1, "@spec"))
                  |> Enum.reverse()

                {callback_doc, callback_meta} =
                  case metadata.mods_funs_to_positions[{behaviour, fun, a}] do
                    nil ->
                      {spec_info.doc, spec_info.meta}

                    def_info ->
                      # in case of protocol implementation get doc and meta from def
                      {def_info.doc, def_info.meta}
                  end

                %{
                  kind: kind,
                  module: mod,
                  function: fun,
                  arity: a,
                  args: fun_args_text,
                  metadata: callback_meta |> Map.merge(meta),
                  specs: specs,
                  docs: callback_doc
                }

              nil ->
                callback_docs_entry =
                  NormalizedCode.callback_documentation(behaviour)
                  |> Enum.find_value(fn
                    {{^fun, ^a}, doc} -> doc
                    _ -> false
                  end)

                case callback_docs_entry do
                  nil ->
                    # pass meta with implementing flag to trigger looking for specs in behaviour module
                    # assume there is a typespec for behaviour module
                    specs = [
                      Introspection.get_spec_as_string(
                        mod,
                        fun,
                        a,
                        State.ModFunInfo.get_category(fun_info),
                        meta
                      )
                    ]

                    %{
                      kind: kind,
                      module: mod,
                      function: fun,
                      arity: a,
                      args: fun_args_text,
                      metadata: meta,
                      specs: specs,
                      docs: ""
                    }

                  {_, docs, callback_meta, mime_type} ->
                    app = Applications.get_application(behaviour)
                    docs = docs |> NormalizedCode.extract_docs(mime_type, behaviour, app)
                    # as of OTP 25 erlang callback doc entry does not have signature in meta
                    # pass meta with implementing flag to trigger looking for specs in behaviour module
                    # assume there is a typespec for behaviour module
                    specs = [
                      Introspection.get_spec_as_string(
                        mod,
                        fun,
                        a,
                        State.ModFunInfo.get_category(fun_info),
                        meta
                      )
                    ]

                    %{
                      kind: kind,
                      module: mod,
                      function: fun,
                      arity: a,
                      args: fun_args_text,
                      metadata: callback_meta |> Map.merge(meta),
                      specs: specs,
                      docs: docs || ""
                    }
                end
            end
        end
      end)

    if doc_infos == [] do
      get_func_docs(mod, fun, arity)
    else
      doc_infos
    end
  end

  def get_all_docs({mod, fun, arity}, metadata, _env, :type) do
    doc_infos =
      metadata.types
      |> Enum.filter(fn
        {{^mod, ^fun, a}, _type_info} when not is_nil(a) ->
          Introspection.matches_arity?(a, arity)

        _ ->
          false
      end)
      |> Enum.sort_by(fn {{_mod, _fun, a}, _type_info} -> a end)
      |> Enum.map(fn {{_mod, _fun, a}, type_info} ->
        args = type_info.args |> List.last()

        spec =
          case type_info.kind do
            :opaque -> "@opaque #{fun}(#{args})"
            _ -> List.last(type_info.specs)
          end

        %{
          kind: :type,
          module: mod,
          type: fun,
          arity: a,
          args: args,
          metadata: type_info.meta,
          spec: spec,
          docs: type_info.doc
        }
      end)

    if doc_infos == [] do
      get_type_docs(mod, fun, arity)
    else
      doc_infos
    end
  end

  @spec get_module_docs(atom) ::
          nil | module_doc()
  def get_module_docs(mod) when is_atom(mod) do
    case NormalizedCode.get_docs(mod, :moduledoc) do
      {_line, text, metadata} ->
        %{
          kind: :module,
          module: mod,
          metadata: metadata,
          docs: text || ""
        }

      _ ->
        if Code.ensure_loaded?(mod) do
          app = Applications.get_application(mod)

          %{
            kind: :module,
            module: mod,
            metadata: %{app: app},
            docs: ""
          }
        end
    end
  end

  # TODO spec
  @spec get_func_docs(nil | module, atom, non_neg_integer | :any) :: list(function_doc())
  def get_func_docs(mod, fun, arity)
      when mod != nil and fun in @builtin_functions do
    for {f, a} <- BuiltinFunctions.all(), f == fun, Introspection.matches_arity?(a, arity) do
      spec = BuiltinFunctions.get_specs({f, a})
      args = BuiltinFunctions.get_args({f, a})
      docs = BuiltinFunctions.get_docs({f, a})

      metadata = %{builtin: true}

      %{
        kind: :function,
        module: mod,
        function: fun,
        arity: a,
        args: args,
        metadata: metadata,
        specs: spec,
        docs: docs
      }
    end
  end

  def get_func_docs(mod, fun, call_arity) do
    case NormalizedCode.get_docs(mod, :docs) do
      nil ->
        # no docs, fallback to typespecs
        get_func_docs_from_typespec(mod, fun, call_arity)

      docs ->
        results =
          for {{f, arity}, _, kind, args, text, metadata} <- docs,
              f == fun,
              Introspection.matches_arity_with_defaults?(
                arity,
                Map.get(metadata, :defaults, 0),
                call_arity
              ) do
            fun_args_text =
              Introspection.get_fun_args_from_doc_or_typespec(mod, f, arity, args, metadata)

            %{
              kind: kind,
              module: mod,
              function: fun,
              arity: arity,
              args: fun_args_text,
              metadata: metadata,
              specs: Introspection.get_specs_text(mod, fun, arity, kind, metadata),
              docs: text || ""
            }
          end

        case results do
          [] ->
            get_func_docs_from_typespec(mod, fun, call_arity)

          other ->
            other
        end
    end
  end

  defp get_func_docs_from_typespec(mod, fun, call_arity) do
    # TypeInfo.get_function_specs does fallback to behaviours
    function_specs = TypeInfo.get_function_specs(mod, fun, call_arity)
    app = Applications.get_application(mod)

    results =
      for {behaviour, specs} <- function_specs, {{_name, arity}, [params | _]} <- specs do
        meta =
          if behaviour do
            %{implementing: behaviour}
          else
            %{}
          end

        fun_args_text = TypeInfo.extract_params(params)

        %{
          kind: :function,
          module: mod,
          function: fun,
          arity: arity,
          args: fun_args_text,
          metadata: meta |> Map.put(:app, app),
          specs: Introspection.get_specs_text(mod, fun, arity, :function, meta),
          docs: ""
        }
      end

    case results do
      [] ->
        # no docs and no typespecs
        get_func_docs_from_module_info(mod, fun, call_arity)

      other ->
        other
    end
  end

  defp get_func_docs_from_module_info(mod, fun, call_arity) do
    # it is not worth doing fallback to behaviours here
    # we'll not get much more useful info

    # provide dummy docs basing on module_info(:exports)
    for {f, {arity, _kind}} <- Introspection.get_exports(mod),
        f == fun,
        Introspection.matches_arity?(arity, call_arity) do
      fun_args_text =
        if arity == 0, do: [], else: Enum.map(1..arity, fn _ -> "term" end)

      metadata =
        if {f, arity} in BuiltinFunctions.erlang_builtin_functions(mod) do
          %{builtin: true, app: :erts}
        else
          # TODO remove this fallback?
          app = Applications.get_application(mod)
          %{app: app}
        end

      %{
        kind: :function,
        module: mod,
        function: fun,
        arity: arity,
        args: fun_args_text,
        metadata: metadata,
        specs: Introspection.get_specs_text(mod, fun, arity, :function, metadata),
        docs: ""
      }
    end
  end

  @spec get_type_docs(nil | module, atom, non_neg_integer | :any) :: list(type_doc())
  defp get_type_docs(nil, fun, arity) do
    for info <- BuiltinTypes.get_builtin_type_info(fun),
        Introspection.matches_arity?(length(info.params), arity) do
      {spec, args} =
        case info do
          %{signature: signature, params: params} ->
            {"@type #{signature}", Enum.map(params, &(&1 |> Atom.to_string()))}

          %{spec: spec_ast, params: params} ->
            {TypeInfo.format_type_spec_ast(spec_ast, :type),
             Enum.map(params, &(&1 |> Atom.to_string()))}

          _ ->
            {"@type #{fun}()", []}
        end

      %{
        kind: :type,
        module: nil,
        type: fun,
        arity: length(info.params),
        args: args,
        metadata: %{builtin: true},
        spec: spec,
        docs: info.doc
      }
    end
  end

  defp get_type_docs(mod, fun, arity) do
    docs =
      (NormalizedCode.get_docs(mod, :type_docs) || [])
      |> Enum.filter(fn {{name, n_args}, _, _, _, _} ->
        name == fun and Introspection.matches_arity?(n_args, arity)
      end)
      |> Enum.sort_by(fn {{_, n_args}, _, _, _, _} -> n_args end)

    case docs do
      [] ->
        # TODO remove this fallback?
        app = Applications.get_application(mod)

        for {kind, {name, _type, args}} = typedef <- Typespec.get_types(mod),
            name == fun,
            Introspection.matches_arity?(length(args), arity),
            kind in [:type, :opaque, :nominal] do
          spec = TypeInfo.format_type_spec(typedef)

          type_args = Enum.map(args, &(&1 |> elem(2) |> Atom.to_string()))

          %{
            kind: :type,
            module: mod,
            type: fun,
            arity: length(args),
            args: type_args,
            metadata: %{app: app},
            spec: spec,
            docs: ""
          }
        end

      docs ->
        for {{f, arity}, _, _, text, metadata} <- docs, f == fun do
          spec =
            mod
            |> TypeInfo.get_type_spec(f, arity)

          {_kind, {_name, _def, args}} = spec
          type_args = Enum.map(args, &(&1 |> elem(2) |> Atom.to_string()))

          %{
            kind: :type,
            module: mod,
            type: fun,
            arity: arity,
            args: type_args,
            metadata: metadata,
            spec: TypeInfo.format_type_spec(spec),
            docs: text || ""
          }
        end
    end
  end

  def expand({{:atom, module}, func}, aliases) do
    # TODO use Macro.Env
    {Introspection.expand_alias(module, aliases), func}
  end

  def expand({nil, func}, _aliases) do
    {nil, func}
  end

  def expand({:none, func}, _aliases) do
    {nil, func}
  end

  def expand({_, _func}, _aliases) do
    {nil, nil}
  end
end
