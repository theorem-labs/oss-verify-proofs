(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Import AsanUbsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import PropExec AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore DepotSymSeg.
Unset Lia Cache. Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2S. Import SEG.
Open Scope Z_scope.

Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
Section WithFP1. Context {FP : PropExec.FPState}.

Definition D : Z := 0x189898.      (* [comment removed for export] *)
Definition SSA : Z := 0x179888.    (* [comment removed for export] *)
Definition ACEILZ : Z := 0x7fff7f800000.
Definition KHI : Z := 0x5fc000.      (* [comment removed for export] *)
Definition PUT_PC : Z := 0x71f34.
Definition PUT_RET : Z := 0x721a8.
Definition PC_HASHED : Z := 0x72054.
Definition PC_LOOP : Z := 0x72074.

Definition allvars : list expr := Eval cbv in (ELit 0 :: map EVar (seq 1 31)).
Fixpoint setregs (l : list (nat * expr)) (sr : list expr) : list expr :=
  match l with [] => sr | (i, e) :: r => setregs r (sr_upd sr i e) end.

(* [comment removed for export] *)
Definition srA (s : Z) : list expr := setregs [(11%nat, ELit s)] allvars.
Definition knA : list kentry :=
  [ KAlign (EVar 2) 16; KRange (EVar 2) ACEILZ (2^47); KWr (SA (EVar 2) (-272)) (ELit 272)
  ; KAlign (EVar 10) 8; KRange (EVar 10) ACEILZ (2^47)
  ; KWord (SA (EVar 10) 0) 8 (EVar 40); KWord (SA (EVar 10) 8) 8 (EVar 41)
  ; KDisj (SA (EVar 10) 0) (ELit 16) (SA (EVar 2) (-272)) (ELit 272)
  ; KImg 0x10000 0x30000 ].
(* [comment removed for export] *)
Definition frameA (s : Z) : list kentry :=
  [ KWord (SA (EVar 2) (-96)) 8 (ELit s); KWord (SA (EVar 2) (-104)) 8 (EVar 10)
  ; KWord (SA (EVar 2) (-88)) 8 (EVar 25); KWord (SA (EVar 2) (-80)) 8 (EVar 24); KWord (SA (EVar 2) (-72)) 8 (EVar 23)
  ; KWord (SA (EVar 2) (-64)) 8 (EVar 22); KWord (SA (EVar 2) (-56)) 8 (EVar 21); KWord (SA (EVar 2) (-48)) 8 (EVar 20)
  ; KWord (SA (EVar 2) (-40)) 8 (EVar 19); KWord (SA (EVar 2) (-32)) 8 (EVar 18); KWord (SA (EVar 2) (-24)) 8 (EVar 9)
  ; KWord (SA (EVar 2) (-16)) 8 (EVar 8); KWord (SA (EVar 2) (-8)) 8 (EVar 1) ].
Definition runA (s : Z) := sym_exec ASEGS 3000 true [PC_HASHED] scr_nil (SS PUT_PC (srA s) [] knA 64%nat) [].
(* [comment removed for export] *)
Definition osrA1 : list expr := ltac:(let v := eval vm_compute in (let '(st, _, _) := runA 1 in s_regs st) in exact v).
Definition osrA2 : list expr := ltac:(let v := eval vm_compute in (let '(st, _, _) := runA 2 in s_regs st) in exact v).
Definition GA (s : Z) (osr : list expr) : seg :=
  SEGM PUT_PC (srA s) knA 64%nat scr_nil 3000%nat [PC_HASHED] PC_HASHED osr (frameA s) [(EVar 2, -104, 0)] [].
Definition GA1 := GA 1 osrA1.
Definition GA2 := GA 2 osrA2.
Lemma GA1_ok : seg_sound ASEGS GA1. Proof. apply seg_sound_by_check. vm_compute. reflexivity. Qed.
Lemma GA2_ok : seg_sound ASEGS GA2. Proof. apply seg_sound_by_check. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma GA1_x18 : nth 18 osrA1 (ELit 0) = EAlu ALU_ADD (EAlu ALU_SRL (EMd M_MUL (ELit 17592186044416) (nth 19 osrA1 (ELit 0))) (ELit 42)) (ELit D).
Proof. apply expr_eqb_eq. vm_compute. reflexivity. Qed.
Lemma GA2_x18 : nth 18 osrA2 (ELit 0) = EAlu ALU_ADD (EAlu ALU_SRL (EMd M_MUL (ELit 17592186044416) (nth 19 osrA2 (ELit 0))) (ELit 42)) (ELit D).
Proof. apply expr_eqb_eq. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Definition ga_regs_chk (osr : list expr) : bool :=
  (expr_eqb (nth 1 osr (ELit 0)) (EVar 1) && expr_eqb (nth 2 osr (ELit 0)) (EAlu ALU_ADD (EVar 2) (ELit (-112)))
   && expr_eqb (nth 3 osr (ELit 0)) (EVar 3) && expr_eqb (nth 4 osr (ELit 0)) (EVar 4)
   && expr_eqb (nth 8 osr (ELit 0)) (ELit 0) && expr_eqb (nth 9 osr (ELit 0)) (ELit D)
   && expr_eqb (nth 13 osr (ELit 0)) (ELit 0x400000)
   && expr_eqb (nth 23 osr (ELit 0)) (ELit 0x7fffffff)
   && expr_eqb (nth 26 osr (ELit 0)) (EVar 26) && expr_eqb (nth 27 osr (ELit 0)) (EVar 27))%bool.
Lemma GA1_regs : ga_regs_chk osrA1 = true. Proof. vm_compute. reflexivity. Qed.
Lemma GA2_regs : ga_regs_chk osrA2 = true. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition srB : list expr := setregs [(9%nat, ELit D); (13%nat, ELit 0x400000); (23%nat, ELit 0x7fffffff); (8%nat, ELit 0)] allvars.
Definition knB : list kentry :=
  [ KWord (SA (EVar 18) 0) 4 (EVar 40); KRange (EVar 40) 0 65534; KRange (EVar 18) D (D + 4194300); KAlign (EVar 18) 4 ].
Definition runB := sym_exec ASEGS 100 true [PC_LOOP] scr_nil (SS PC_HASHED srB [] knB 64%nat) [].
Definition osrB : list expr := ltac:(let v := eval vm_compute in (let '(st, _, _) := runB in s_regs st) in exact v).
Definition GB : seg := SEGM PC_HASHED srB knB 64%nat scr_nil 100%nat [PC_LOOP] PC_LOOP osrB [] [] [].
Lemma GB_ok : seg_sound ASEGS GB. Proof. apply seg_sound_by_check. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition frameL (sz : expr) : list kentry :=
  [ KWord (SA (EVar 2) 104) 8 (EVar 33); KWord (SA (EVar 2) 96) 8 (EVar 34); KWord (SA (EVar 2) 88) 8 (EVar 35)
  ; KWord (SA (EVar 2) 80) 8 (EVar 36); KWord (SA (EVar 2) 72) 8 (EVar 37); KWord (SA (EVar 2) 64) 8 (EVar 38)
  ; KWord (SA (EVar 2) 56) 8 (EVar 39); KWord (SA (EVar 2) 48) 8 (EVar 42); KWord (SA (EVar 2) 40) 8 (EVar 43)
  ; KWord (SA (EVar 2) 32) 8 (EVar 54); KWord (SA (EVar 2) 24) 8 (EVar 55)
  ; KWord (SA (EVar 2) 16) 8 sz; KWord (SA (EVar 2) 8) 8 (EVar 44)
  ; KAlign (EVar 2) 16; KRange (EVar 2) ACEILZ (2^47); KWr (SA (EVar 2) (-160)) (ELit 272) ].
Definition srL : list expr :=
  setregs [(9%nat, ELit D); (22%nat, ELit 65535); (23%nat, ELit 2147483647); (24%nat, ELit (D + 0x400010));
           (20%nat, ELit (D + 0x400008)); (8%nat, ELit 0)] allvars.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition NB : expr := EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 11)) (EVar 47).
Definition knL : list kentry :=
  frameL (EVar 56) ++
  [ KRange (EVar 11) 1 65534
  ; KWord (SA (ELit 0) (D + 0x400010)) 8 (EVar 47); KRange (EVar 47) KHI (2^47 - 2^20); KAlign (EVar 47) 4096
  ; KWr (SA (EVar 47) 0) (ELit 1048576)
  ; KWord (SA NB 0) 8 (EVar 52); KWord (SA NB 8) 4 (EVar 53); KRange (EVar 53) 0 65534 ].
Definition runL (dirs : list bool) :=
  sym_exec ASEGS 3000 true [PC_LOOP; PUT_RET] (SCR dirs [] []) (SS PC_LOOP srL [] knL 64%nat) [].
Definition osrLF : list expr := ltac:(let v := eval vm_compute in (let '(st, _, _) := runL [false] in s_regs st) in exact v).
Definition osrLC : list expr := ltac:(let v := eval vm_compute in (let '(st, _, _) := runL [true] in s_regs st) in exact v).
Definition GLF : seg := SEGM PC_LOOP srL knL 64%nat (SCR [false] [] []) 3000%nat [PC_LOOP; PUT_RET] PUT_RET osrLF [] []
                          [SCBr false BC_NE (EVar 19) (EVar 52)].
Definition GLC : seg := SEGM PC_LOOP srL knL 64%nat (SCR [true] [] []) 3000%nat [PC_LOOP; PUT_RET] PC_LOOP osrLC [] []
                          [SCBr true BC_NE (EVar 19) (EVar 52)].
Lemma GLF_ok : seg_sound ASEGS GLF. Proof. apply seg_sound_by_check. vm_compute. reflexivity. Qed.
Lemma GLC_ok : seg_sound ASEGS GLC. Proof. apply seg_sound_by_check. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition srE : list expr := setregs [(11%nat, ELit 0)] srL.
Definition knE (s : Z) : list kentry :=
  frameL (ELit s) ++
  [ KWord (SA (EVar 18) 0) 4 (EVar 25); KRange (EVar 25) 0 65534; KRange (EVar 18) D (D + 4194300); KAlign (EVar 18) 4
  ; KWord (SA (ELit 0) (D + 0x400000)) 4 (EVar 45); KRange (EVar 45) 0 65533
  ; KWord (SA (ELit 0) (D + 0x400010)) 8 (EVar 47); KRange (EVar 47) KHI (2^47 - 2^20); KAlign (EVar 47) 4096
  ; KWr (SA (EVar 47) 0) (ELit 1048576)
  ; KWord (SA (ELit 0) SSA) 8 (EVar 46); KRange (EVar 46) 0 507; KWord (SA (ELit 0) (SSA + 24)) 4 (EVar 46)
  ; KWord (SA (ELit 0) (SSA + 16)) 8 (EVar 48); KRange (EVar 48) KHI (2^47 - 2^23); KAlign (EVar 48) 4096
  ; KWr (SA (EVar 48) 0) (ELit 4096)
  ; KWr (SA (ELit 0) D) (ELit 0x400018); KWr (SA (ELit 0) SSA) (ELit 32)
  ; KWord (SA (EVar 44) 0) 8 (EVar 40); KWord (SA (EVar 44) 8) 8 (EVar 41); KAlign (EVar 44) 8; KRange (EVar 44) ACEILZ (2^47)
  ; KDisj (SA (EVar 44) 0) (ELit 16) (SA (EVar 2) (-160)) (ELit 272)
  (* [comment removed for export] *)
  ; KDisj (SA (EVar 47) 0) (ELit 1048576) (SA (EVar 2) (-160)) (ELit 272)
  ; KDisj (SA (EVar 48) 0) (ELit 4096) (SA (EVar 2) (-160)) (ELit 272)
  ; KDisj (SA (EVar 47) 0) (ELit 1048576) (SA (EVar 44) 0) (ELit 16)
  ; KDisj (SA (EVar 48) 0) (ELit 4096) (SA (EVar 44) 0) (ELit 16)
  ; KDisj (SA (EVar 47) 0) (ELit 1048576) (SA (EVar 48) 0) (ELit 4096)
  ; KImg 0x10000 0x30000 ].
Definition runE (s : Z) := sym_exec ASEGS 5000 true [PUT_RET] scr_nil (SS PC_LOOP srE [] (knE s) 64%nat) [].
Definition osrE1 : list expr := ltac:(let v := eval vm_compute in (let '(st, _, _) := runE 1 in s_regs st) in exact v).
Definition osrE2 : list expr := ltac:(let v := eval vm_compute in (let '(st, _, _) := runE 2 in s_regs st) in exact v).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition NBn : expr := EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 45)) (EVar 47).
Definition FBt : expr := EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 46)) (EVar 48).
Definition oknE : list kentry :=
  [ KWord (SA (EVar 18) 0) 4 (EAlu ALU_ADD (EVar 45) (ELit 1))
  ; KWord (SA NBn 24) 4 (EVar 25)
  ; KWord (SA (ELit 0) (D + 0x400000)) 4 (EAlu ALU_ADD (EVar 45) (ELit 1))   (* [comment removed for export] *)
  ; KWord (SA (ELit 0) SSA) 8 (EAlu ALU_ADD (EVar 46) (ELit 3))
  ; KWord (SA (ELit 0) (SSA + 24)) 4 (EAlu ALU_ADD (EVar 46) (ELit 3))
  ; KWord (SA (ELit 0) (D + 0x400010)) 8 (EVar 47)
  ; KWord (SA (ELit 0) (SSA + 16)) 8 (EVar 48) ].
Definition fpE (s : Z) : list fp_item :=
  [ (EVar 2, -112, 0); (EVar 18, 0, 4); (ELit 0, SSA, SSA + 8); (ELit 0, SSA + 24, SSA + 28)
  ; (ELit 0, D + 0x400000, D + 0x400004); (NBn, 16, 32); (FBt, 0, 8 + 8 * s) ].
Definition GE (s : Z) (osr : list expr) (okn : list kentry) : seg :=
  SEGM PC_LOOP srE (knE s) 64%nat scr_nil 5000%nat [PUT_RET] PUT_RET osr okn (fpE s) [].
(* [comment removed for export] *)
Definition oknE1 : list kentry := Eval cbv in
  (map (fun K => match K with
                 | KWord (SA (ELit 0) a) 8 (EAlu ALU_ADD (EVar 46) (ELit 3)) => KWord (SA (ELit 0) a) 8 (EAlu ALU_ADD (EVar 46) (ELit 2))
                 | KWord (SA (ELit 0) a) 4 (EAlu ALU_ADD (EVar 46) (ELit 3)) => KWord (SA (ELit 0) a) 4 (EAlu ALU_ADD (EVar 46) (ELit 2))
                 | _ => K end) oknE).
Definition GE1 := GE 1 osrE1 oknE1.
Definition GE2 := GE 2 osrE2 oknE.
Lemma GE1_ok : seg_sound ASEGS GE1. Proof. apply seg_sound_by_check. vm_compute. reflexivity. Qed.
Lemma GE2_ok : seg_sound ASEGS GE2. Proof. apply seg_sound_by_check. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition osrA (s : Z) : list expr := if Z.eqb s 1 then osrA1 else osrA2.
Lemma GA_ok : forall s, s = 1 \/ s = 2 -> seg_sound ASEGS (GA s (osrA s)).
Proof. intros s [-> | ->]; [exact GA1_ok | exact GA2_ok]. Qed.
(* [comment removed for export] *)
Definition x18_form (h : expr) : expr := EAlu ALU_ADD (EAlu ALU_SRL (EMd M_MUL (ELit 17592186044416) h) (ELit 42)) (ELit D).
Lemma GA_x18 : forall s, s = 1 \/ s = 2 -> nth 18 (osrA s) (ELit 0) = x18_form (nth 19 (osrA s) (ELit 0)).
Proof. intros s [-> | ->]; [exact GA1_x18 | exact GA2_x18]. Qed.
Lemma GA_regs : forall s, s = 1 \/ s = 2 -> ga_regs_chk (osrA s) = true.
Proof. intros s [-> | ->]; [exact GA1_regs | exact GA2_regs]. Qed.

Definition osrE (s : Z) : list expr := if Z.eqb s 1 then osrE1 else osrE2.
Definition oknEs (s : Z) : list kentry := if Z.eqb s 1 then oknE1 else oknE.
Lemma GE_ok : forall s, s = 1 \/ s = 2 -> seg_sound ASEGS (GE s (osrE s) (oknEs s)).
Proof. intros s [-> | ->]; [exact GE1_ok | exact GE2_ok]. Qed.
(* [comment removed for export] *)
Definition ge_regs_chk (osr : list expr) : bool :=
  (expr_eqb (nth 1 osr (ELit 0)) (EVar 33) && expr_eqb (nth 2 osr (ELit 0)) (EAlu ALU_ADD (EVar 2) (ELit 112))
   && expr_eqb (nth 3 osr (ELit 0)) (EVar 3) && expr_eqb (nth 4 osr (ELit 0)) (EVar 4)
   && expr_eqb (nth 8 osr (ELit 0)) (EVar 34) && expr_eqb (nth 9 osr (ELit 0)) (EVar 35)
   && expr_eqb (nth 10 osr (ELit 0)) (EAlu ALU_ADD (EVar 45) (ELit 1))
   && expr_eqb (nth 18 osr (ELit 0)) (EVar 36) && expr_eqb (nth 19 osr (ELit 0)) (EVar 37)
   && expr_eqb (nth 20 osr (ELit 0)) (EVar 38) && expr_eqb (nth 21 osr (ELit 0)) (EVar 39)
   && expr_eqb (nth 22 osr (ELit 0)) (EVar 42) && expr_eqb (nth 23 osr (ELit 0)) (EVar 43)
   && expr_eqb (nth 24 osr (ELit 0)) (EVar 54) && expr_eqb (nth 25 osr (ELit 0)) (EVar 55)
   && expr_eqb (nth 26 osr (ELit 0)) (EVar 26) && expr_eqb (nth 27 osr (ELit 0)) (EVar 27))%bool.
Lemma GE_regs : forall s, s = 1 \/ s = 2 -> ge_regs_chk (osrE s) = true.
Proof. intros s [-> | ->]; vm_compute; reflexivity. Qed.
Lemma GLF_regs : ge_regs_chk (sr_upd osrLF 10 (EAlu ALU_ADD (EVar 45) (ELit 1))) = true /\ nth 10 osrLF (ELit 0) = EVar 11.
Proof. split; [vm_compute; reflexivity | reflexivity]. Qed.
(* [comment removed for export] *)
Lemma GB_regs :
  nth 11 osrB (ELit 0) = nth 25 osrB (ELit 0)
  /\ (forallb (fun i => expr_eqb (nth i osrB (ELit 0)) (nth i srB (ELit 0))) [1;2;3;4;8;9;18;19;21;22;23;26;27]%nat = true)
  /\ nth 24 osrB (ELit 0) = ELit (D + 0x400010) /\ nth 20 osrB (ELit 0) = ELit (D + 0x400008).
Proof. repeat split; vm_compute; reflexivity. Qed.
Lemma GLC_regs :
  nth 11 osrLC (ELit 0) = EVar 53
  /\ (forallb (fun i => expr_eqb (nth i osrLC (ELit 0)) (nth i srL (ELit 0))) [1;2;3;4;8;9;18;19;20;22;23;24;25;26;27]%nat = true).
Proof. split; [reflexivity | vm_compute; reflexivity]. Qed.
(* [comment removed for export] *)
Lemma oknEs_shape : forall s, s = 1 \/ s = 2 ->
  oknEs s = [ KWord (SA (EVar 18) 0) 4 (EAlu ALU_ADD (EVar 45) (ELit 1))
            ; KWord (SA NBn 24) 4 (EVar 25)
            ; KWord (SA (ELit 0) (D + 0x400000)) 4 (EAlu ALU_ADD (EVar 45) (ELit 1))
            ; KWord (SA (ELit 0) SSA) 8 (EAlu ALU_ADD (EVar 46) (ELit (s + 1)))
            ; KWord (SA (ELit 0) (SSA + 24)) 4 (EAlu ALU_ADD (EVar 46) (ELit (s + 1)))
            ; KWord (SA (ELit 0) (D + 0x400010)) 8 (EVar 47)
            ; KWord (SA (ELit 0) (SSA + 16)) 8 (EVar 48) ].
Proof. intros s [-> | ->]; reflexivity. Qed.
End WithFP1.

