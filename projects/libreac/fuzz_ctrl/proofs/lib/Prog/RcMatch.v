From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcParse.
Import ListNotations.
Open Scope Z_scope.

Definition hb (l : list Z) : list byte := map (Z_to_bv 8) l.

Definition DECLS : list (list byte) := map hb [
  [1; 3; 0; 16; 130; 0; 0; 2; 2; 2; 2; 2; 1; 1; 3; 3; 3; 3; 3; 3; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 76];
  [1; 3; 0; 16; 132; 0; 0; 0; 2; 2; 1; 1; 3; 3; 3; 3; 3; 3; 3; 3; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 74];
  [1; 3; 0; 16; 132; 0; 0; 0; 2; 2; 2; 2; 2; 2; 2; 2; 1; 1; 3; 3; 0; 3; 0; 0; 0; 1; 0; 0; 0; 0; 0; 76];
  [1; 3; 0; 16; 132; 0; 0; 0; 1; 1; 1; 1; 1; 1; 1; 1; 0; 0; 3; 3; 0; 3; 0; 0; 0; 1; 0; 0; 0; 0; 0; 86];
  [1; 3; 0; 16; 132; 0; 0; 0; 2; 2; 1; 1; 1; 1; 3; 3; 3; 3; 3; 3; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 78];
  [1; 3; 0; 16; 132; 0; 0; 0; 2; 2; 2; 2; 2; 2; 1; 1; 1; 1; 3; 3; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 82];
  [1; 3; 0; 16; 132; 0; 0; 0; 1; 1; 1; 1; 1; 1; 1; 1; 3; 3; 3; 3; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 84];
  [1; 3; 0; 16; 132; 0; 0; 0; 2; 2; 2; 2; 2; 2; 2; 2; 3; 3; 3; 3; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 76];
  [1; 3; 0; 16; 132; 0; 0; 0; 2; 2; 2; 2; 2; 2; 2; 2; 2; 2; 3; 3; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 78];
  [1; 3; 0; 16; 132; 0; 0; 0; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 3; 3; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 88];
  [1; 3; 0; 16; 132; 0; 0; 0; 2; 2; 2; 2; 2; 1; 1; 1; 1; 1; 3; 3; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 83]].

Definition cm_blk (fb : list byte) : list byte := firstn 32 (skipn 18 fb).

Definition cm_gate (len : Z) (fb : list byte) : bool :=
  (50 <=? len) && (cp_v fb 12 =? 0x88) && (cp_v fb 13 =? 0x19) && (cp_v fb 16 =? 0xcd) && (cp_v fb 17 =? 0xea)
  && (fst (ctrlparse len fb) =? 9).

Fixpoint cm_find (b : list byte) (ds : list (list byte)) : option nat :=
  match ds with
  | [] => None
  | d :: ds' => if bool_decide (d = b) then Some O else option_map S (cm_find b ds')
  end.

Definition want (T len : Z) (fb : list byte) : Z :=
  if cm_gate len fb then
    match cm_find (cm_blk fb) DECLS with Some j => T + 296 * Z.of_nat j | None => 0 end
  else 0.
