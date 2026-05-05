(*
  Global variable start caching
*)

Theory pan_globals_start
Ancestors
  panLang pan_common
Libs
  preamble

Definition subexp_exp_def:
  (subexp_exp r (Struct es) = Struct (MAP (subexp_exp r) es)) ∧
  (subexp_exp r (Field i e) = Field i (subexp_exp r e)) ∧
  (subexp_exp r (Load s e) = Load s (subexp_exp r e)) ∧
  (subexp_exp r (Load32 e) = Load32 (subexp_exp r e)) ∧
  (subexp_exp r (LoadByte e) = LoadByte (subexp_exp r e)) ∧
  (subexp_exp r (Op bop es) = Op bop (MAP (subexp_exp r) es)) ∧
  (subexp_exp r (Panop pop es) = Panop pop (MAP (subexp_exp r) es)) ∧
  (subexp_exp r (Cmp c e1 e2) = Cmp c (subexp_exp r e1) (subexp_exp r e2)) ∧
  (subexp_exp r (Shift sh e n) = Shift sh (subexp_exp r e) n) ∧
  (subexp_exp r e = r e)
End

Definition subexp_prog_def:
  (subexp_prog r (Dec v s e p) = Dec v s (subexp_exp r e) (subexp_prog r p)) ∧
  (subexp_prog r (Assign vk v e) = Assign vk v (subexp_exp r e)) ∧
  (subexp_prog r (Store dst src) = Store (subexp_exp r dst) (subexp_exp r src)) ∧
  (subexp_prog r (Store32 dst src) = Store32 (subexp_exp r dst) (subexp_exp r src)) ∧
  (subexp_prog r (StoreByte dst src) = StoreByte (subexp_exp r dst) (subexp_exp r src)) ∧
  (subexp_prog r (Seq p1 p2) = Seq (subexp_prog r p1) (subexp_prog r p2)) ∧
  (subexp_prog r (If e p1 p2) = If (subexp_exp r e) (subexp_prog r p1) (subexp_prog r p2)) ∧
  (subexp_prog r (While e p) = While (subexp_exp r e) (subexp_prog r p)) ∧
  (subexp_prog r (Call ctyp fname args) =
    let
      rwargs = MAP (subexp_exp r) args in
    case ctyp of
      | NONE => Call NONE fname rwargs
      | SOME (vret, NONE) => Call (SOME (vret, NONE)) fname rwargs
      | SOME (vret, SOME (ei, ev, eprog)) =>
          Call (SOME (vret, SOME (ei, ev, subexp_prog r eprog))) fname rwargs) ∧
  (subexp_prog r (DecCall v s fname args p) = DecCall v s fname (MAP (subexp_exp r) args) (subexp_prog r p)) ∧
  (subexp_prog r (ExtCall fname e1 e2 e3 e4) =
    let
      rw1 = subexp_exp r e1;
      rw2 = subexp_exp r e2;
      rw3 = subexp_exp r e3;
      rw4 = subexp_exp r e4
    in
      ExtCall fname rw1 rw2 rw3 rw4) ∧
  (subexp_prog r (Raise ei e) = Raise ei (subexp_exp r e)) ∧
  (subexp_prog r (Return e) = Return (subexp_exp r e)) ∧
  (subexp_prog r (ShMemLoad os vk v e) = ShMemLoad os vk v (subexp_exp r e)) ∧
  (subexp_prog r (ShMemStore os e1 e2) = ShMemStore os (subexp_exp r e1) (subexp_exp r e2)) ∧
  (subexp_prog r p = p)
End

Definition subst_topaddr_var_def:
  (subst_topaddr_var v TopAddr = (Var Local v)) ∧
  (subst_topaddr_var v e = e)
End

Definition topaddr_to_var_def:
  topaddr_to_var v p = subexp_prog (subst_topaddr_var v) p
End

Definition topaddr_exists_e_def:
  (topaddr_exists_e (Struct es) = EXISTS topaddr_exists_e es) ∧
  (topaddr_exists_e (Field i e) = topaddr_exists_e e) ∧
  (topaddr_exists_e (Load s e) = topaddr_exists_e e) ∧
  (topaddr_exists_e (Load32 e) = topaddr_exists_e e) ∧
  (topaddr_exists_e (LoadByte e) = topaddr_exists_e e) ∧
  (topaddr_exists_e (Op bop es) = EXISTS topaddr_exists_e es) ∧
  (topaddr_exists_e (Panop pop es) = EXISTS topaddr_exists_e es) ∧
  (topaddr_exists_e (Cmp c e1 e2) = (topaddr_exists_e e1 ∨ topaddr_exists_e e2)) ∧
  (topaddr_exists_e (Shift sh e n) = topaddr_exists_e e) ∧
  (topaddr_exists_e TopAddr = T) ∧
  (topaddr_exists_e _ = F)
End

Definition topaddr_exists_p_def:
  (topaddr_exists_p (Dec v s e p) = (topaddr_exists_e e ∨ topaddr_exists_p p)) ∧
  (topaddr_exists_p (Assign vk v e) = topaddr_exists_e e) ∧
  (topaddr_exists_p (Store e1 e2) = (topaddr_exists_e e1 ∨ topaddr_exists_e e2)) ∧
  (topaddr_exists_p (Store32 e1 e2) = (topaddr_exists_e e1 ∨ topaddr_exists_e e2)) ∧
  (topaddr_exists_p (StoreByte e1 e2) = (topaddr_exists_e e1 ∨ topaddr_exists_e e2)) ∧
  (topaddr_exists_p (Seq p1 p2) = (topaddr_exists_p p1 ∨ topaddr_exists_p p2)) ∧
  (topaddr_exists_p (If e p1 p2) = (topaddr_exists_e e ∨ topaddr_exists_p p1 ∨ topaddr_exists_p p2)) ∧
  (topaddr_exists_p (While e p) = (topaddr_exists_e e ∨ topaddr_exists_p p)) ∧
  (topaddr_exists_p (Call ctyp fn args) =
    (EXISTS topaddr_exists_e args ∨
    (case ctyp of
      | SOME (vret, SOME(ei, ev, eprog)) => topaddr_exists_p eprog
      | _ => F))) ∧
  (topaddr_exists_p (DecCall v s fn args p) = (EXISTS topaddr_exists_e args ∨ topaddr_exists_p p)) ∧
  (topaddr_exists_p (ExtCall fn e1 e2 e3 e4) = EXISTS topaddr_exists_e [e1; e2; e3; e4]) ∧
  (topaddr_exists_p (Raise i e) = topaddr_exists_e e) ∧
  (topaddr_exists_p (Return e) = topaddr_exists_e e) ∧
  (topaddr_exists_p (ShMemLoad os vk v e) = topaddr_exists_e e) ∧
  (topaddr_exists_p (ShMemStore os e1 e2) = (topaddr_exists_e e1 ∨  topaddr_exists_e e2)) ∧
  (topaddr_exists_p _ = F)
End

Definition opt_prog_def:
  opt_prog p =
    if topaddr_exists_p p then
      let
        new_name = fresh_name «cached» (var_prog p)
      in
        Dec new_name One TopAddr (topaddr_to_var new_name p)
    else
      p
End

