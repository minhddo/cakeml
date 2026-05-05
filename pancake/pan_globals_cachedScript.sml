(*
  Caching of global variable (mini CSE)
*)
Theory pan_globals_cached
Ancestors
  panLang pan_common
Libs
  preamble

Definition global_var_prog_def:
  (global_var_prog (Dec v s e p) = global_var_exp e ++ global_var_prog p) ∧
  (global_var_prog (Assign vk v e) =
    case vk of
      | Local => global_var_exp e
      | Global => [v] ++ global_var_exp e) ∧
  (global_var_prog (Store e1 e2) = global_var_exp e1 ++ global_var_exp e2) ∧
  (global_var_prog (Store32 e1 e2) = global_var_exp e1 ++ global_var_exp e2) ∧
  (global_var_prog (StoreByte e1 e2) = global_var_exp e1 ++ global_var_exp e2) ∧
  (global_var_prog (Seq p1 p2) = global_var_prog p1 ++ global_var_prog p2) ∧
  (global_var_prog (If e p1 p2) = global_var_exp e ++ global_var_prog p1 ++ global_var_prog p2) ∧
  (global_var_prog (While e p) = global_var_exp e ++ global_var_prog p) ∧
  (global_var_prog (Call ctyp fn args) =
    let
      globargs = FLAT (MAP global_var_exp args)
    in
      case ctyp of
        | NONE => globargs
        | SOME (NONE, NONE) => globargs
        | SOME (SOME (vk, vn), NONE) =>
            (case vk of
              | Local => globargs
              | Global => [vn] ++ globargs)
        | SOME (NONE, SOME (ei, ev, ep)) => globargs ++ global_var_prog ep
        | SOME (SOME (vk, vn), SOME (ei, ev, ep)) =>
            (case vk of
              | Local => globargs ++ global_var_prog ep
              | Global => globargs ++ [vn] ++ global_var_prog ep)) ∧
  (global_var_prog (DecCall v s fn args p) = FLAT (MAP global_var_exp args) ++ global_var_prog p) ∧
  (global_var_prog (ExtCall fn e1 e2 e3 e4) =
    let
      g1 = global_var_exp e1;
      g2 = global_var_exp e2;
      g3 = global_var_exp e3;
      g4 = global_var_exp e4
    in
      g1 ++ g2 ++ g3 ++ g4) ∧
  (global_var_prog (Raise i e) = global_var_exp e) ∧
  (global_var_prog (Return e) = global_var_exp e) ∧
  (global_var_prog (ShMemLoad os vk vn e) =
    case vk of
      | Local => global_var_exp e
      | Global => [vn] ++ global_var_exp e) ∧
  (global_var_prog (ShMemStore os e1 e2) = global_var_exp e1 ++ global_var_exp e2) ∧
  (global_var_prog _ = [])
End

(* Rewrite global variables into their local cached variables *)
Definition global_cached_exp_def:
  (global_cached_exp (globs: mlstring |-> mlstring) (Var vk v) =
    case vk of
      | Local => Var vk v
      | Global =>
          case FLOOKUP globs v of
            | SOME vl => Var Local vl
            | NONE => Var vk v (* Cannot happen or code is unreachable *)) ∧
  (global_cached_exp globs (Struct es) = Struct (MAP (global_cached_exp globs) es)) ∧
  (global_cached_exp globs (Field i e) = Field i (global_cached_exp globs e)) ∧
  (global_cached_exp globs (Load s e) = Load s (global_cached_exp globs e)) ∧
  (global_cached_exp globs (Load32 e) = Load32 (global_cached_exp globs e)) ∧
  (global_cached_exp globs (LoadByte e) = LoadByte (global_cached_exp globs e)) ∧
  (global_cached_exp globs (Op bop es) = Op bop (MAP (global_cached_exp globs) es)) ∧
  (global_cached_exp globs (Panop pop es) = Panop pop (MAP (global_cached_exp globs) es)) ∧
  (global_cached_exp globs (Cmp c e1 e2) = Cmp c (global_cached_exp globs e1) (global_cached_exp globs e2)) ∧
  (global_cached_exp globs (Shift sh e n) = Shift sh (global_cached_exp globs e) n) ∧
  (global_cached_exp globs e = e)
End

(* Rewrite expressions containing globals into their versions with local cache
   Also returning a set of local cache variables that need to be reloaded before evaluating
   the expression
 *)
Definition rw_global_exp_def:
  rw_global_exp (globs: mlstring |-> mlstring) valids e = (set (FILTER (\x. x NOTIN valids) (global_var_exp e)), global_cached_exp globs e)
End

(* Nested assignments into a list of local variables *)
Definition nested_assign_local_def:
  nested_assign_local ls es = panLang$nested_seq (MAP2 (Assign Local) ls es)
End

(* From a set of stale global caches, make a list of Assigns to reload the caches
 *)
Definition reload_globs_cache_def:
  reload_globs_cache stale_globs globs =
    let
      alist_globs = fmap_to_alist globs;
      alist_stale = FILTER (\(g,l). g ∈ stale_globs) alist_globs;
      (globs, caches) = UNZIP alist_stale
    in
      nested_assign_local caches (MAP (Var Global) globs)
End

(* Rewrite statements containing globals into their versions with local cache
   Wrap a statement with a list of reloads (assigns) for local cache that became stale and is in
   demand in the statement, only reload a local cache right before its first usage after becoming
   stale
 *)
Definition global_cached_prog_def:
  (global_cached_prog globs valids (Dec v s e p) =
    let
      (stales, e') = rw_global_exp globs valids e;
      (valids', p') = global_cached_prog globs (valids ∪ stales) p
    in
      (valids', Seq (reload_globs_cache stales globs) (Dec v s e' p'))
  ) ∧
  (global_cached_prog globs valids (Assign vk vn e) =
    let
      (stales, e') = rw_global_exp globs valids e;
      (assign_valids, new_assign) =
        (case vk of
          | Local => (EMPTY, Assign vk vn e')
          | Global =>
              case FLOOKUP globs vn of
                | SOME vl => ({vn}, Seq (Assign vk vn e') (Assign Local vl (Var Global vn)))
                | NONE => (EMPTY, Assign vk vn e') (* Can't happen or code is unreachable *)
        )
    in
      (valids ∪ stales ∪ assign_valids, Seq (reload_globs_cache stales globs) new_assign)
  ) ∧
  (global_cached_prog globs valids (Store e1 e2) =
    let
      (stales1, e1') = rw_global_exp globs valids e1;
      (stales2, e2') = rw_global_exp globs valids e2;
      stales = stales1 ∪ stales2
    in
      (valids ∪ stales, Seq (reload_globs_cache stales globs) (Store e1' e2'))
  ) ∧
  (global_cached_prog globs valids (Store32 e1 e2) =
    let
      (stales1, e1') = rw_global_exp globs valids e1;
      (stales2, e2') = rw_global_exp globs valids e2;
      stales = stales1 ∪ stales2
    in
      (valids ∪ stales, Seq (reload_globs_cache stales globs) (Store32 e1' e2'))
  ) ∧
  (global_cached_prog globs valids (StoreByte e1 e2) =
    let
      (stales1, e1') = rw_global_exp globs valids e1;
      (stales2, e2') = rw_global_exp globs valids e2;
      stales = stales1 ∪ stales2
    in
      (valids ∪ stales, Seq (reload_globs_cache stales globs) (StoreByte e1' e2'))
  ) ∧
  (global_cached_prog globs valids (Seq p1 p2) =
    let
      (valids1, p1') = global_cached_prog globs valids p1;
      (valids2, p2') = global_cached_prog globs valids1 p2
    in
      (valids2, Seq p1' p2')
  ) ∧
  (global_cached_prog globs valids (If e p1 p2) =
    let
      (stales, e') = rw_global_exp globs valids e;
      (valids1, p1') = global_cached_prog globs (valids ∪ stales) p1;
      (valids2, p2') = global_cached_prog globs (valids ∪ stales) p2
    in
      (valids1 ∩ valids2, Seq (reload_globs_cache stales globs) (If e' p1' p2'))
  ) ∧
  (global_cached_prog globs valids (While e p) =
    let
      (stales, e') = rw_global_exp globs valids e;
      (valids', p') = global_cached_prog globs (valids ∪ stales) p
    in
      (valids', Seq (reload_globs_cache stales globs) (While e' p'))
  ) ∧
  (global_cached_prog globs valids (Call ctyp fn args) =
    let
      t = MAP (rw_global_exp globs valids) args;
      (stales_list, nargs) = UNZIP t;
      stales = FOLDL $UNION EMPTY stales_list;
      (call_valids, call_transform) =
        (case ctyp of
          | NONE => (EMPTY, Call ctyp fn nargs)
          | SOME (NONE, NONE) => (EMPTY, Call ctyp fn nargs)
          | SOME (SOME (vk, vn), NONE) =>
              (case vk of
                | Local => (EMPTY, Call ctyp fn nargs)
                | Global =>
                    case FLOOKUP globs vn of
                      | SOME vl => ({vn}, Seq (Call ctyp fn nargs) (Assign Local vl (Var Global vn)))
                      | NONE => (EMPTY, Call ctyp fn nargs))
          | SOME (NONE, SOME (ei, ev, ep)) => (EMPTY, Call (SOME (NONE, SOME (ei, ev, SND (global_cached_prog globs EMPTY ep)))) fn nargs)
          | SOME (SOME (vk, vn), SOME (ei, ev, ep)) =>
              (case vk of
                | Local => (EMPTY, Call (SOME (SOME (vk, vn), SOME (ei, ev, SND (global_cached_prog globs EMPTY ep)))) fn nargs)
                | Global =>
                    case FLOOKUP globs vn of
                      | SOME vl => ({vn}, Seq (Call (SOME (SOME (vk, vn), SOME (ei, ev, SND (global_cached_prog globs EMPTY ep)))) fn nargs)
                                       (Assign Local vl (Var Global vn)))
                      | NONE => (EMPTY, Call (SOME (SOME (vk, vn), SOME (ei, ev, SND (global_cached_prog globs EMPTY ep)))) fn nargs)
              ));
    in
      (call_valids, Seq (reload_globs_cache stales globs) call_transform)
  ) ∧
  (global_cached_prog globs valids (DecCall v s fn args p) =
    let
      t = MAP (rw_global_exp globs valids) args;
      (stales_list, nargs) = UNZIP t;
      stales = FOLDL $UNION EMPTY stales_list;
      (valids', p') = global_cached_prog globs EMPTY p;
    in
      (valids', Seq (reload_globs_cache stales globs) (DecCall v s fn nargs p'))
  ) ∧
  (global_cached_prog globs valids (ExtCall fn e1 e2 e3 e4) =
    let
      (stales1, e1') = rw_global_exp globs valids e1;
      (stales2, e2') = rw_global_exp globs valids e2;
      (stales3, e3') = rw_global_exp globs valids e3;
      (stales4, e4') = rw_global_exp globs valids e4;
      stales = stales1 ∪ stales2 ∪ stales3 ∪ stales4;
    in
      (valids ∪ stales, Seq (reload_globs_cache stales globs) (ExtCall fn e1' e2' e3' e4'))
  ) ∧
  (global_cached_prog globs valids (Raise i e) =
    let
      (stales, e') = rw_global_exp globs valids e
    in
      (valids ∪ stales, Seq (reload_globs_cache stales globs) (Raise i e'))
  ) ∧
  (global_cached_prog globs valids (Return e) =
    let
      (stales, e') = rw_global_exp globs valids e
    in
      (valids ∪ stales, Seq (reload_globs_cache stales globs) (Return e'))
  ) ∧
  (global_cached_prog globs valids (ShMemLoad os vk vn e) =
    let
      (stales, e') = rw_global_exp globs valids e;
      (shmemload_valids, new_shmemload) =
        (case vk of
          | Local => (EMPTY, ShMemLoad os vk vn e')
          | Global =>
              case FLOOKUP globs vn of
                | SOME vl => ({vn}, Seq (ShMemLoad os Local vl e') (Assign Global vn (Var Local vl)))
                | _ => (EMPTY, ShMemLoad os vk vn e')
        )
    in
      (valids ∪ stales ∪ shmemload_valids, Seq (reload_globs_cache stales globs) new_shmemload)
  ) ∧
  (global_cached_prog globs valids (ShMemStore os e1 e2) =
    let
      (stales1, e1') = rw_global_exp globs valids e1;
      (stales2, e2') = rw_global_exp globs valids e2;
      stales = stales1 ∪ stales2
    in
      (valids ∪ stales, Seq (reload_globs_cache stales globs) (ShMemStore os e1' e2'))
  ) ∧
  (global_cached_prog globs valids p = (valids, p))
End

Definition fresh_names_def:
  (fresh_names 0 names = []) ∧
  (fresh_names (SUC n) names =
    let
      first_name = fresh_name «g_cached» names
    in
      (first_name :: (fresh_names n (first_name::names))))
End

Definition globals_def:
  (globals [] = []) ∧
  (globals (Decl sh v e::ds) = ((sh, v)::(globals ds))) ∧
  (globals (Function fi::ds) = globals ds)
End

Definition zero_sh_def:
  (zero_sh One = Const 0w) ∧
  (zero_sh (Comb shs) = Struct (MAP zero_sh shs))
End

Definition nested_decs_def:
  (nested_decs sh [] [] p = p) ∧
  (nested_decs (s::sh) (v::vs) (e::es) p = Dec v s e (nested_decs sh vs es p)) ∧
  (nested_decs _ _ _ p = p)
End

Definition compile_def:
  compile gls p =
    let
      gl_names = UNZIP_SND gls;
      gl_shapes = UNZIP_FST gls;
      gl_names_in_prog = FILTER (λx. MEM x (global_var_prog p)) gl_names;
      lc_cached_names = fresh_names (LENGTH gl_names_in_prog) (var_prog p ++ gl_names);
      g_l_map = alist_to_fmap (ZIP (gl_names_in_prog, lc_cached_names));
    in
      nested_decs gl_shapes lc_cached_names (MAP zero_sh gl_shapes) (SND (global_cached_prog g_l_map EMPTY p))
End

Definition compile_prog_def:
  compile_prog decls =
    let
      globals_nsh = globals decls
    in
      MAP (λdecl.
            case decl of
              | Function fi => Function (fi with body := compile globals_nsh fi.body)
              | _ => decl) decls
End

