(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Require OSSVerify.Proofs.fast_float.from_chars.lib.Ox.F112_004.   (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng AxBits.

Module AXF_dec.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_G := EVar 32.
Definition e_idx := EVar 33.
Definition e_W := EVar 34.
Definition e_avail := EVar 35.
Definition e_freed := EVar 36.
Definition e_sp0 := EVar 37.
Definition e_canary := EVar 38.
Definition e_csz := EVar 39.
Definition e_nxt := EVar 40.
Definition e_bnc := EVar 41.
Definition e_usg := EVar 42.
Definition STK := SA e_sp0 (-1024).
Definition SC := EAlu ALU_SRL (EMd M_MUL (ELit 4503599627370496) e_W) (ELit 58).
Definition SC2 := EMd M_MUL (ELit 2) SC.
Definition SC8 := EMd M_MUL (ELit 8) SC.
Definition TB1 := EAlu ALU_AND (EAlu ALU_SRL e_W (ELit 5)) (ELit 126).
Definition sr_dec := (sr_upd (sr_upd (sr_upd sr_id 2 (e_sp0)) 10 (e_G)) 11 (e_idx)).
Definition kn_dec : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KWr STK (ELit 1024);
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange e_idx 0 31;
    KRange e_avail 0 (2^32-1);
    KRange e_freed 0 (2^32-1);
    KRange SC 0 63;
    KRange SC2 0 126;
    KRange SC8 0 504;
    KRange TB1 0 126;
    KWord (SA e_G 24) 4 e_avail;
    KWord (SA e_G 28) 4 e_freed;
    KWord (SA e_G 32) 8 e_W;
    KWord (SA e_G 8) 8 e_nxt;
    KWord (SA TB1 98984) 2 e_csz;
    KWord (SA SC2 98984) 2 e_csz;
    KWord (SA SC 614977) 1 e_bnc;
    KWord (SA SC8 614568) 8 e_usg;
    KWord (SA (ELit 0) 0x63da0) 8 (ELit 0x95e40);
    KWord (SA (ELit 0) 0x95e40) 8 e_canary;
    KDisj STK (ELit 1024) (SA e_G 0) (ELit 40);
    KDisj STK (ELit 1024) (SA TB1 98984) (ELit 2);
    KDisj STK (ELit 1024) (SA SC2 98984) (ELit 2);
    KDisj STK (ELit 1024) (SA SC 614977) (ELit 1);
    KDisj STK (ELit 1024) (SA SC8 614568) (ELit 8) ].
Definition scr_dec : scripts := SCR [] [] [].
Definition ss_dec := SS 0x518d0 sr_dec [] kn_dec 43.
Definition RUN_dec := sym_exec SEGS 200 true [0x519e4; 0x51a2c] scr_dec ss_dec [].

Definition scr_dE2 : scripts := SCR [false; true] [] [].
Definition RES_dE2 := Eval vm_compute in sym_exec SEGS 200 true [0x519e4; 0x51a2c] scr_dE2 ss_dec [].
Lemma RES_dE2_ok : sym_exec SEGS 200 true [0x519e4; 0x51a2c] scr_dE2 (SS 0x518d0 sr_dec [] kn_dec 43) [] = RES_dE2.
Proof. vm_compute. reflexivity. Qed.

Definition scr_dG2 : scripts := SCR [false; false; false; true; true] [] [].
Definition RES_dG2 := Eval vm_compute in sym_exec SEGS 200 true [0x519e4; 0x51a2c] scr_dG2 ss_dec [].
Lemma RES_dG2_ok : sym_exec SEGS 200 true [0x519e4; 0x51a2c] scr_dG2 (SS 0x518d0 sr_dec [] kn_dec 43) [] = RES_dG2.
Proof. vm_compute. reflexivity. Qed.

Definition scr_dG3b : scripts := SCR [false; false; false; false; true; false; true] [] [].
Definition RES_dG3b := Eval vm_compute in sym_exec SEGS 200 true [0x519e4; 0x51a2c] scr_dG3b ss_dec [].
Lemma RES_dG3b_ok : sym_exec SEGS 200 true [0x519e4; 0x51a2c] scr_dG3b (SS 0x518d0 sr_dec [] kn_dec 43) [] = RES_dG3b.
Proof. vm_compute. reflexivity. Qed.

Definition scr_dG4b : scripts := SCR [false; false; false; false; true; false; false; true] [] [].
Definition RES_dG4b := Eval vm_compute in sym_exec SEGS 200 true [0x519e4; 0x51a2c] scr_dG4b ss_dec [].
Lemma RES_dG4b_ok : sym_exec SEGS 200 true [0x519e4; 0x51a2c] scr_dG4b (SS 0x518d0 sr_dec [] kn_dec 43) [] = RES_dG4b.
Proof. vm_compute. reflexivity. Qed.

Definition scr_dG5b : scripts := SCR [false; false; false; false; true; false; false; false; true] [] [].
Definition RES_dG5b := Eval vm_compute in sym_exec SEGS 200 true [0x519e4; 0x51a2c] scr_dG5b ss_dec [].
Lemma RES_dG5b_ok : sym_exec SEGS 200 true [0x519e4; 0x51a2c] scr_dG5b (SS 0x518d0 sr_dec [] kn_dec 43) [] = RES_dG5b.
Proof. vm_compute. reflexivity. Qed.

Definition scr_dE4b : scripts := SCR [false; false; false; false; true; false; false; false; false; true] [] [].
Definition RES_dE4b := Eval vm_compute in sym_exec SEGS 200 true [0x519e4; 0x51a2c] scr_dE4b ss_dec [].
Lemma RES_dE4b_ok : sym_exec SEGS 200 true [0x519e4; 0x51a2c] scr_dE4b (SS 0x518d0 sr_dec [] kn_dec 43) [] = RES_dE4b.
Proof. vm_compute. reflexivity. Qed.

Definition scr_dE5b : scripts := SCR [false; false; false; false; true; false; false; false; false; false; true] [] [].
Definition RES_dE5b := Eval vm_compute in sym_exec SEGS 200 true [0x519e4; 0x51a2c] scr_dE5b ss_dec [].
Lemma RES_dE5b_ok : sym_exec SEGS 200 true [0x519e4; 0x51a2c] scr_dE5b (SS 0x518d0 sr_dec [] kn_dec 43) [] = RES_dE5b.
Proof. vm_compute. reflexivity. Qed.

Definition scr_dG6b : scripts := SCR [false; false; false; false; true; false; false; false; false; false; false] [] [].
Definition RES_dG6b := Eval vm_compute in sym_exec SEGS 200 true [0x519e4; 0x51a2c] scr_dG6b ss_dec [].
Lemma RES_dG6b_ok : sym_exec SEGS 200 true [0x519e4; 0x51a2c] scr_dG6b (SS 0x518d0 sr_dec [] kn_dec 43) [] = RES_dG6b.
Proof. vm_compute. reflexivity. Qed.

Definition scr_dG1a : scripts := SCR [false; false; false; false; false; true; true] [] [].
Definition RES_dG1a := Eval vm_compute in sym_exec SEGS 200 true [0x519e4; 0x51a2c] scr_dG1a ss_dec [].
Lemma RES_dG1a_ok : sym_exec SEGS 200 true [0x519e4; 0x51a2c] scr_dG1a (SS 0x518d0 sr_dec [] kn_dec 43) [] = RES_dG1a.
Proof. vm_compute. reflexivity. Qed.

Definition scr_dG3a : scripts := SCR [false; false; false; false; false; true; false; true] [] [].
Definition RES_dG3a := Eval vm_compute in sym_exec SEGS 200 true [0x519e4; 0x51a2c] scr_dG3a ss_dec [].
Lemma RES_dG3a_ok : sym_exec SEGS 200 true [0x519e4; 0x51a2c] scr_dG3a (SS 0x518d0 sr_dec [] kn_dec 43) [] = RES_dG3a.
Proof. vm_compute. reflexivity. Qed.

Definition scr_dG4a : scripts := SCR [false; false; false; false; false; true; false; false; true] [] [].
Definition RES_dG4a := Eval vm_compute in sym_exec SEGS 200 true [0x519e4; 0x51a2c] scr_dG4a ss_dec [].
Lemma RES_dG4a_ok : sym_exec SEGS 200 true [0x519e4; 0x51a2c] scr_dG4a (SS 0x518d0 sr_dec [] kn_dec 43) [] = RES_dG4a.
Proof. vm_compute. reflexivity. Qed.

Definition scr_dG5a : scripts := SCR [false; false; false; false; false; true; false; false; false; true] [] [].
Definition RES_dG5a := Eval vm_compute in sym_exec SEGS 200 true [0x519e4; 0x51a2c] scr_dG5a ss_dec [].
Lemma RES_dG5a_ok : sym_exec SEGS 200 true [0x519e4; 0x51a2c] scr_dG5a (SS 0x518d0 sr_dec [] kn_dec 43) [] = RES_dG5a.
Proof. vm_compute. reflexivity. Qed.

Definition scr_dE4a : scripts := SCR [false; false; false; false; false; true; false; false; false; false; true] [] [].
Definition RES_dE4a := Eval vm_compute in sym_exec SEGS 200 true [0x519e4; 0x51a2c] scr_dE4a ss_dec [].
Lemma RES_dE4a_ok : sym_exec SEGS 200 true [0x519e4; 0x51a2c] scr_dE4a (SS 0x518d0 sr_dec [] kn_dec 43) [] = RES_dE4a.
Proof. vm_compute. reflexivity. Qed.

Definition scr_dG6a : scripts := SCR [false; false; false; false; false; true; false; false; false; false; false; false] [] [].
Definition RES_dG6a := Eval vm_compute in sym_exec SEGS 200 true [0x519e4; 0x51a2c] scr_dG6a ss_dec [].
Lemma RES_dG6a_ok : sym_exec SEGS 200 true [0x519e4; 0x51a2c] scr_dG6a (SS 0x518d0 sr_dec [] kn_dec 43) [] = RES_dG6a.
Proof. vm_compute. reflexivity. Qed.
End AXF_dec.

Module AXF_decz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AxMng AxBits MngZ.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngZ OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_dec.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Record dec_pre (regs : bvmap 5 word) (m : word -> option byte) (G idx W avail freed sp0 canary csz nxt bnc usg : Z) : Prop := {
  dp_R10 : getr regs 10 = wa G ; dp_R11 : getr regs 11 = wa idx ; dp_R2 : getr regs 2 = wa sp0 ;
  dp_Rsp : 2^20 <= sp0 <= 2^47 ; dp_Asp : sp0 mod 16 = 0 ; dp_HSTK : stk_ok SEGS m (wa sp0) 1024 ;
  dp_RG : 1 <= G <= 2^63-1 ; dp_AG : G mod 8 = 0 ; dp_RW : 0 <= W <= 2^64-1 ; dp_Ridx : 0 <= idx <= 31 ;
  dp_Rav : 0 <= avail <= 2^32-1 ; dp_Rfr : 0 <= freed <= 2^32-1 ; dp_Rcan : 0 <= canary <= 2^64-1 ;
  dp_Rcsz : 0 <= csz <= 65535 ; dp_Rnxt : 0 <= nxt <= 2^64-1 ; dp_Rbnc : 0 <= bnc <= 255 ; dp_Rusg : 0 <= usg <= 2^64-1 ;
  dp_Mav : rdn SEGS m (wa (G + 24)) 4 = Some (word_to_le_bytes 4 (wa avail)) ;
  dp_Mfr : rdn SEGS m (wa (G + 28)) 4 = Some (word_to_le_bytes 4 (wa freed)) ;
  dp_MW : rdn SEGS m (wa (G + 32)) 8 = Some (word_to_le_bytes 8 (wa W)) ;
  dp_Mnx : rdn SEGS m (wa (G + 8)) 8 = Some (word_to_le_bytes 8 (wa nxt)) ;
  dp_Mcsz : rdn SEGS m (wa (98984 + 2 * SCW W)) 2 = Some (word_to_le_bytes 2 (wa csz)) ;
  dp_Mbnc : rdn SEGS m (wa (614977 + SCW W)) 1 = Some (word_to_le_bytes 1 (wa bnc)) ;
  dp_Musg : rdn SEGS m (wa (614568 + 8 * SCW W)) 8 = Some (word_to_le_bytes 8 (wa usg)) ;
  dp_Mgot : rdn SEGS m (wa 408992) 8 = Some (word_to_le_bytes 8 (wa 0x95e40)) ;
  dp_Mcan : rdn SEGS m (wa 613952) 8 = Some (word_to_le_bytes 8 (wa canary)) ;
  dp_DSG : G + 40 <= sp0 - 1024 ;
  dp_sc : SCW W <= 47 ;
  dp_free : Z.land W 32 <> 0 ;
  dp_A : Z.testbit avail idx = false ; dp_F : Z.testbit freed idx = false
}.

Section DEC.
Context {fx : FPState}.

Definition E_dec (regs : bvmap 5 word) (G idx W avail freed sp0 canary csz nxt bnc usg : Z) : env :=
  Env (reg_ev regs (fun n => wa (nth (n - 32) [G; idx; W; avail; freed; sp0; canary; csz; nxt; bnc; usg] 0))) (fun _ => []).

#[using="Type"] Lemma dec_setup : forall regs m G idx W avail freed sp0 canary csz nxt bnc usg,
  dec_pre regs m G idx W avail freed sp0 canary csz nxt bnc usg ->
  regs_ok (E_dec regs G idx W avail freed sp0 canary csz nxt bnc usg) sr_dec regs /\
  know_ok SEGS (E_dec regs G idx W avail freed sp0 canary csz nxt bnc usg) m kn_dec.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G idx W avail freed sp0 canary csz nxt bnc usg DP.
  destruct DP as [R10 R11 R2 Rsp Asp HSTK RG AG RW Ridx Rav Rfr Rcan Rcsz Rnxt Rbnc Rusg Mav Mfr MW Mnx Mcsz Mbnc Musg Mgot Mcan DSG Fsc Ffree A2 A3].
  set (E := E_dec regs G idx W avail freed sp0 canary csz nxt bnc usg).
  assert (Z32 : bv_unsigned (ev E 32) = G) by exact (u_wa_small _ (rng64 _ _ _ RG eq_refl)).
  assert (Z33 : bv_unsigned (ev E 33) = idx) by exact (u_wa_small _ (rng64 _ _ _ Ridx eq_refl)).
  assert (Z34 : bv_unsigned (ev E 34) = W) by exact (u_wa_small _ (rng64 _ _ _ RW eq_refl)).
  assert (Z35 : bv_unsigned (ev E 35) = avail) by exact (u_wa_small _ (rng64 _ _ _ Rav eq_refl)).
  assert (Z36 : bv_unsigned (ev E 36) = freed) by exact (u_wa_small _ (rng64 _ _ _ Rfr eq_refl)).
  assert (Z37 : bv_unsigned (ev E 37) = sp0) by exact (u_wa_small _ (rng64 _ _ _ Rsp eq_refl)).
  assert (Z38 : bv_unsigned (ev E 38) = canary) by exact (u_wa_small _ (rng64 _ _ _ Rcan eq_refl)).
  assert (Z39 : bv_unsigned (ev E 39) = csz) by exact (u_wa_small _ (rng64 _ _ _ Rcsz eq_refl)).
  assert (Z40 : bv_unsigned (ev E 40) = nxt) by exact (u_wa_small _ (rng64 _ _ _ Rnxt eq_refl)).
  assert (Z41 : bv_unsigned (ev E 41) = bnc) by exact (u_wa_small _ (rng64 _ _ _ Rbnc eq_refl)).
  assert (Z42 : bv_unsigned (ev E 42) = usg) by exact (u_wa_small _ (rng64 _ _ _ Rusg eq_refl)).
  split.
  { apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E sr_id regs 2); [apply regs_ok_id|] |] |].
    - rewrite R2. reflexivity.
    - rewrite R10. reflexivity.
    - rewrite R11. reflexivity. }
  assert (RSC : 0 <= SCW W <= 63) by (apply SCW_range; clear - RW; lia).
  assert (ETB : Z.land (Z.shiftr W 5 mod 2^64) 126 = 2 * SCW W) by (apply TB1_SCW; clear - RW; lia).
  unfold know_ok, kn_dec.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m e_sp0 (wa sp0) 1024); [reflexivity | exact HSTK | rewrite u_wa_small by (clear - Rsp; lia); clear - Rsp; lia])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot e_G e_idx e_W e_avail e_freed e_sp0 e_canary e_csz e_nxt e_bnc e_usg STK SC SC2 SC8 TB1 a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range W _ _ RW eq_refl eq_refl), ?(mod64_of_range sp0 _ _ Rsp eq_refl eq_refl),
               ?(mod64_of_range G _ _ RG eq_refl eq_refl), ?(mod64_of_range idx _ _ Ridx eq_refl eq_refl),
               ?(mod64_of_range avail _ _ Rav eq_refl eq_refl), ?(mod64_of_range freed _ _ Rfr eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * W) mod 2^64) 58) with (SCW W).
  all: rewrite ?ETB.
  all: rewrite ?(Z.mod_small (2 * SCW W) (2^64)) by (clear - RSC; lia).
  all: rewrite ?(Z.mod_small (8 * SCW W) (2^64)) by (clear - RSC; lia).
  all: rewrite ?(Z.mod_small (SCW W) (2^64)) by (clear - RSC; lia).
  all: try assumption.
  all: try (rewrite Z.add_comm; assumption).
  all: try (clear - Rsp; lia).
  all: try (clear - RSC; lia).
  all: try (clear - Rsp RSC; lia).
  all: try (clear - Rsp DSG RG; lia).
Qed.

Definition dec_ok (G idx W avail freed csz nxt bnc usg : Z) : bool :=
  (Z.lor avail freed + 2^idx =? 2^(Z.land W 31 + 1) - 1) &&
  ((Z.shiftr W 12 =? 0) ||
   (if Z.land W 31 =? 0 then 4096 * Z.shiftr W 12 + -16 <? 16 * csz else false) ||
   negb (nxt =? G) || (31 <? (SCW W + -7) mod 2^64) || (bnc <? 100) ||
   (negb (usg <? 9 * Z.land W 31 + 9) && negb (18 <? Z.land W 31))).

Definition dec_mem (m : word -> option byte) (regs : bvmap 5 word) (sp0 canary : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
    (wa (sp0 - 8)) (word_to_le_bytes 8 (getr regs 1))) (wa (sp0 - 16)) (word_to_le_bytes 8 (getr regs 8)))
    (wa (sp0 - 24)) (word_to_le_bytes 8 (getr regs 9))) (wa (sp0 - 32)) (word_to_le_bytes 8 (getr regs 18)))
    (wa (sp0 - 40)) (word_to_le_bytes 8 (getr regs 19))) (wa (sp0 - 48)) (word_to_le_bytes 8 (wa canary)).

(* [comment removed for export] *)
Definition dec_post (R regs : bvmap 5 word) (G idx W avail freed sp0 : Z) : Prop :=
  getr R 10 = wa G /\ getr R 11 = wa (bv_swrap 32 (2^idx)) /\ getr R 12 = wa (SCW W) /\
  getr R 13 = wa (bv_swrap 32 (Z.lor avail freed)) /\ getr R 9 = wa 0x95e40 /\ getr R 2 = wa (sp0 - 96) /\
  (forall n, In n [3;4;8;19;20;21;22;23;24;25;26;27]%nat -> getr R (Z_to_bv 5 (Z.of_nat n)) = getr regs (Z_to_bv 5 (Z.of_nat n))).

#[using="Type"] Lemma land31_mod : forall W, 0 <= W -> Z.land W 31 mod 2^64 = Z.land W 31.
Proof. LiaFast.lf_pins LiaFast.u0. intros W H. pose proof (land31_bound W H). apply Z.mod_small. lia. Qed.
#[using="Type"] Lemma land31x9_mod : forall W, 0 <= W -> (9 * Z.land W 31 + 9) mod 2^64 = 9 * Z.land W 31 + 9.
Proof. LiaFast.lf_pins LiaFast.u0. intros W H. pose proof (land31_bound W H). apply Z.mod_small. lia. Qed.
#[using="Type"] Lemma land32_mod : forall W, 0 <= W -> Z.land W 32 mod 2^64 = Z.land W 32.
Proof. LiaFast.lf_pins LiaFast.u0. intros W H. apply Z.mod_small. split; [apply Z.land_nonneg; lia|].
  destruct (Z.eq_dec (Z.land W 32) 0) as [->|Hnz]; [lia|].
  assert (0 < Z.land W 32) by (pose proof (proj2 (Z.land_nonneg W 32) (or_introl H)); lia).
  pose proof (Z.log2_land W 32 H ltac:(lia)) as Hl. change (Z.log2 32) with 5 in Hl.
  pose proof (Z.log2_spec (Z.land W 32) ltac:(lia)) as [_ Hs].
  assert (Z.log2 (Z.land W 32) <= 5) by lia.
  apply (Z.lt_le_trans _ (2 ^ Z.succ (Z.log2 (Z.land W 32)))); [exact Hs|]. apply (Z.le_trans _ (2^6)); [apply Z.pow_le_mono_r; lia | lia]. Qed.
#[using="Type"] Lemma shr12_mod : forall W, 0 <= W < 2^64 -> Z.shiftr W 12 mod 2^64 = Z.shiftr W 12.
Proof. LiaFast.lf_pins LiaFast.u0. intros W H. apply Z.mod_small. split; [apply Z.shiftr_nonneg; lia|]. rewrite Z.shiftr_div_pow2 by lia.
  apply Z.div_lt_upper_bound; [lia|]. change (2^12 * 2^64) with (2^76). lia. Qed.
#[using="Type"] Lemma scw_mod : forall W, 0 <= W -> SCW W mod 2^64 = SCW W.
Proof. LiaFast.lf_pins LiaFast.u0. intros W H. pose proof (SCW_range W H). apply Z.mod_small. lia. Qed.
#[using="Type"] Lemma ext1_mod : forall b, 0 <= b <= 255 -> ext_Z false 0 1 b mod 2^64 = b.
Proof. LiaFast.lf_pins LiaFast.u0. intros b H. unfold ext_Z. cbn -[Z.pow]. change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r.
  rewrite Z.mod_small by (change (2 ^ (8 * 1)) with 256; lia). rewrite Z.mod_small by lia. reflexivity. Qed.

#[using="Type"] Lemma stride_mod : forall W, 0 <= W < 2^64 -> (Z.shiftr W 12 =? 0) = false -> (4096 * Z.shiftr W 12 + -16) mod 2^64 = 4096 * Z.shiftr W 12 + -16.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros W H H2. apply Z.eqb_neq in H2. pose proof (shr12_mod W H) as E. pose proof (Z.shiftr_nonneg W 12) as Hn.
  assert (Z.shiftr W 12 < 2^52) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_lt_upper_bound; [lia|]; change (2^12 * 2^52) with (2^64); lia).
  apply Z.mod_small. lia.
Qed.
#[using="Type"] Lemma ext2_mod : forall c, 0 <= c <= 65535 -> (16 * ext_Z false 0 2 c) mod 2^64 = 16 * c.
Proof. LiaFast.lf_pins LiaFast.u0. intros c H. unfold ext_Z. cbn -[Z.pow]. change (2 ^ (8 * Z.of_nat 0)) with 1. rewrite Z.div_1_r.
  rewrite (Z.mod_small c) by (change (2 ^ (8 * 2)) with 65536; lia). apply Z.mod_small. lia. Qed.

Ltac dec_atoms DP E :=
  let R10 := fresh "R10" in let R11 := fresh "R11" in let R2 := fresh "R2" in let Rsp := fresh "Rsp" in let Asp := fresh "Asp" in
  let HSTK := fresh "HSTK" in let RG := fresh "RG" in let AG := fresh "AG" in let RW := fresh "RW" in let Ridx := fresh "Ridx" in
  let Rav := fresh "Rav" in let Rfr := fresh "Rfr" in let Rcan := fresh "Rcan" in let Rcsz := fresh "Rcsz" in let Rnxt := fresh "Rnxt" in
  let Rbnc := fresh "Rbnc" in let Rusg := fresh "Rusg" in let Fsc := fresh "Fsc" in let Ffree := fresh "Ffree" in
  let A2 := fresh "A2" in let A3 := fresh "A3" in
  destruct DP as [R10 R11 R2 Rsp Asp HSTK RG AG RW Ridx Rav Rfr Rcan Rcsz Rnxt Rbnc Rusg _ _ _ _ _ _ _ _ _ _ Fsc Ffree A2 A3].

Ltac dsc_rw :=
  match goal with
  | H : bv_unsigned (ev ?E ?n) = ?v |- context [bv_unsigned (ev ?E ?n)] => rewrite H
  end.
Ltac dsc_mod :=
  match goal with
  | H : ?lo <= ?x <= ?hi |- context [?x mod 2^64] => rewrite (mod64_of_range x lo hi H eq_refl eq_refl)
  end.
Ltac DSCS :=
  repeat (first [apply Forall_nil | apply Forall_cons]);
  apply sc_br_z; cbn [zeval edenot]; repeat dsc_rw;
  rewrite ?br_eq_z, ?br_ne_z, ?br_geu_z, ?br_ltu_z; repeat dsc_mod; litmods;
  change (Z.shiftr ((4503599627370496 * ?W) mod 2^64) 58) with (SCW W);
  repeat match goal with
  | H : 0 <= ?W |- context [Z.land ?W 31 mod 2^64] => rewrite (land31_mod W H)
  | H : 0 <= ?W |- context [(9 * Z.land ?W 31 + 9) mod 2^64] => rewrite (land31x9_mod W H)
  | H : 0 <= ?W |- context [Z.land ?W 32 mod 2^64] => rewrite (land32_mod W H)
  | H : 0 <= ?W < 2^64 |- context [Z.shiftr ?W 12 mod 2^64] => rewrite (shr12_mod W H)
  | H : 0 <= ?W |- context [SCW ?W mod 2^64] => rewrite (scw_mod W H)
  | H : 0 <= ?b <= 255 |- context [ext_Z false 0 1 ?b mod 2^64] => rewrite (ext1_mod b H)
  | H : 0 <= ?W < 2^64, H2 : (Z.shiftr ?W 12 =? 0) = false |- context [(4096 * Z.shiftr ?W 12 + -16) mod 2^64] => rewrite (stride_mod W H H2)
  | H : 0 <= ?c <= 65535 |- context [(16 * ext_Z false 0 2 ?c) mod 2^64] => rewrite (ext2_mod c H)
  end;
  first [ reflexivity | assumption | (apply negb_true_iff; assumption) | (apply negb_false_iff; assumption) | idtac ].

Definition LOG_dec := Eval cbv in s_log (fst (fst RES_dG2)).
Definition REGS_dG2 := Eval cbv in s_regs (fst (fst RES_dG2)).

#[using="Type"] Lemma dec_log_eq : forall regs m G idx W avail freed sp0 canary csz nxt bnc usg,
  2^20 <= sp0 <= 2^47 -> 0 <= canary <= 2^64-1 ->
  mem_denot (E_dec regs G idx W avail freed sp0 canary csz nxt bnc usg) m LOG_dec = dec_mem m regs sp0 canary.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G idx W avail freed sp0 canary csz nxt bnc usg Rsp Rcan.
  set (E := E_dec regs G idx W avail freed sp0 canary csz nxt bnc usg).
  assert (Z37 : bv_unsigned (ev E 37) = sp0) by exact (u_wa_small _ (rng64 _ _ _ Rsp eq_refl)).
  assert (Z38 : bv_unsigned (ev E 38) = canary) by exact (u_wa_small _ (rng64 _ _ _ Rcan eq_refl)).
  cbn [mem_denot LOG_dec]. unfold dec_mem.
  repeat (apply (f_equal3 wbytes)); try reflexivity.
  all: try (rewrite adenot_z; cbn [zeval edenot]; rewrite ?Z37; f_equal; ring).
  all: try (cbn [edenot]; change (ev E 38) with (wa canary); reflexivity).
Qed.

#[using="Type"] Lemma dec_r11 : forall regs G idx W avail freed sp0 canary csz nxt bnc usg, 0 <= idx <= 31 ->
  edenot (E_dec regs G idx W avail freed sp0 canary csz nxt bnc usg) (EAluw ALU_SLL (ELit 1) (EVar 33)) = wa (bv_swrap 32 (2^idx)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs G idx W avail freed sp0 canary csz nxt bnc usg Ridx. rewrite zeval_sound. cbn [zeval edenot].
  change (bv_unsigned (ev (E_dec regs G idx W avail freed sp0 canary csz nxt bnc usg) 33)) with (bv_unsigned (wa idx)).
  rewrite (u_wa_small idx) by (clear - Ridx; lia). litmods. rewrite (Z.mod_small idx 32) by (clear - Ridx; lia).
  rewrite Z.shiftl_1_l. reflexivity.
Qed.
#[using="Type"] Lemma dec_r12 : forall regs G idx W avail freed sp0 canary csz nxt bnc usg, 0 <= W <= 2^64-1 ->
  edenot (E_dec regs G idx W avail freed sp0 canary csz nxt bnc usg) SC = wa (SCW W).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs G idx W avail freed sp0 canary csz nxt bnc usg RW. rewrite zeval_sound. cbn [zeval edenot SC e_W].
  change (bv_unsigned (ev (E_dec regs G idx W avail freed sp0 canary csz nxt bnc usg) 34)) with (bv_unsigned (wa W)).
  rewrite (u_wa_small W) by (clear - RW; lia). litmods. reflexivity.
Qed.
#[using="Type"] Lemma dec_r13 : forall regs G idx W avail freed sp0 canary csz nxt bnc usg, 0 <= avail <= 2^32-1 -> 0 <= freed <= 2^32-1 ->
  edenot (E_dec regs G idx W avail freed sp0 canary csz nxt bnc usg) (EAlu ALU_OR (EExt true 0 4 (EVar 35)) (EExt true 0 4 (EVar 36)))
  = wa (bv_swrap 32 (Z.lor avail freed)).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs G idx W avail freed sp0 canary csz nxt bnc usg Rav Rfr. rewrite zeval_sound. cbn [zeval edenot].
  change (bv_unsigned (ev (E_dec regs G idx W avail freed sp0 canary csz nxt bnc usg) 35)) with (bv_unsigned (wa avail)).
  change (bv_unsigned (ev (E_dec regs G idx W avail freed sp0 canary csz nxt bnc usg) 36)) with (bv_unsigned (wa freed)).
  rewrite (u_wa_small avail) by (clear - Rav; lia). rewrite (u_wa_small freed) by (clear - Rfr; lia).
  rewrite ?(Z.mod_small avail (2^64)) by (clear - Rav; lia). rewrite ?(Z.mod_small freed (2^64)) by (clear - Rfr; lia).
  rewrite !ext4_swrap, sx32_lor. apply wa_eqm. rewrite Z.mod_mod by lia. reflexivity.
Qed.
#[using="Type"] Lemma dec_r2 : forall regs G idx W avail freed sp0 canary csz nxt bnc usg, 2^20 <= sp0 <= 2^47 ->
  edenot (E_dec regs G idx W avail freed sp0 canary csz nxt bnc usg) (EAlu ALU_ADD (EVar 37) (ELit (-96))) = wa (sp0 - 96).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs G idx W avail freed sp0 canary csz nxt bnc usg Rsp. rewrite zeval_sound. cbn [zeval edenot].
  change (bv_unsigned (ev (E_dec regs G idx W avail freed sp0 canary csz nxt bnc usg) 37)) with (bv_unsigned (wa sp0)).
  rewrite (u_wa_small sp0) by (clear - Rsp; lia). reflexivity.
Qed.

Ltac dec_pc :=
  unfold dec_ok; repeat match goal with H : ?c = true |- context [?c] => rewrite H | H : ?c = false |- context [?c] => rewrite H end;
  cbn [andb orb negb].

Ltac srg HR' := rewrite (HR' _); lazymatch goal with |- edenot _ (sr_get ?l ?r) = _ => let t := eval vm_compute in (sr_get l r) in change (sr_get l r) with t end.

Ltac dpath RES RESok HR HK E m rom regs sp0 canary :=
  let R := fresh "R" in let HR' := fresh "HR'" in let Hms := fresh "Hms" in
  destruct (run_sound SEGS 200 [0x519e4; 0x51a2c] _ 0x518d0 sr_dec kn_dec 43 _ _ _ E m rom regs RESok HR HK) as (R & HR' & _ & Hms);
  [ cbn [RES fst snd]; DSCS
  | exists R; split;
    [ cbn [RES fst snd s_pc s_log] in Hms; dec_pc;
      lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (dec_mem m regs sp0 canary) with M; [exact Hms|] end;
      refine (dec_log_eq regs m _ _ _ _ _ sp0 canary _ _ _ _ _ _); assumption
    | cbn [RES fst snd s_regs] in HR'; clear Hms; split; [|dec_pc; first [ (intros _; srg HR'; reflexivity) | (intros Hc; discriminate) ] ]; unfold dec_post;
      split; [srg HR'; reflexivity|]; split; [srg HR'; apply dec_r11; assumption|];
      split; [srg HR'; apply dec_r12; assumption|]; split; [srg HR'; apply dec_r13; assumption|];
      split; [srg HR'; reflexivity|]; split; [srg HR'; apply dec_r2; assumption|];
      let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn; cbn [In] in Hn;
      repeat (destruct Hn as [<-|Hn]; [rewrite (HR' _); reflexivity|]); destruct Hn ] ].

#[using="Type"] Theorem dec_arm : forall regs m rom G idx W avail freed sp0 canary csz nxt bnc usg,
  dec_pre regs m G idx W avail freed sp0 canary csz nxt bnc usg ->
  exists R, msteps SEGS (mkst regs (wa 0x518d0) m rom)
              (mkst R (wa (if dec_ok G idx W avail freed csz nxt bnc usg then 0x519e4 else 0x51a2c)) (dec_mem m regs sp0 canary) rom)
         /\ dec_post R regs G idx W avail freed sp0 /\ (dec_ok G idx W avail freed csz nxt bnc usg = true -> getr R 18 = wa 0x95ed8).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G idx W avail freed sp0 canary csz nxt bnc usg DP.
  destruct (dec_setup regs m G idx W avail freed sp0 canary csz nxt bnc usg DP) as [HR HK].
  set (E := E_dec regs G idx W avail freed sp0 canary csz nxt bnc usg) in *.
  destruct DP as [R10 R11 R2 Rsp Asp HSTK RG AG RW Ridx Rav Rfr Rcan Rcsz Rnxt Rbnc Rusg Mav Mfr MW Mnx Mcsz Mbnc Musg Mgot Mcan DSG Fsc Ffree A2 A3].
  assert (Z32 : bv_unsigned (ev E 32) = G) by exact (u_wa_small _ (rng64 _ _ _ RG eq_refl)).
  assert (Z33 : bv_unsigned (ev E 33) = idx) by exact (u_wa_small _ (rng64 _ _ _ Ridx eq_refl)).
  assert (Z34 : bv_unsigned (ev E 34) = W) by exact (u_wa_small _ (rng64 _ _ _ RW eq_refl)).
  assert (Z35 : bv_unsigned (ev E 35) = avail) by exact (u_wa_small _ (rng64 _ _ _ Rav eq_refl)).
  assert (Z36 : bv_unsigned (ev E 36) = freed) by exact (u_wa_small _ (rng64 _ _ _ Rfr eq_refl)).
  assert (Z37 : bv_unsigned (ev E 37) = sp0) by exact (u_wa_small _ (rng64 _ _ _ Rsp eq_refl)).
  assert (Z38 : bv_unsigned (ev E 38) = canary) by exact (u_wa_small _ (rng64 _ _ _ Rcan eq_refl)).
  assert (Z39 : bv_unsigned (ev E 39) = csz) by exact (u_wa_small _ (rng64 _ _ _ Rcsz eq_refl)).
  assert (Z40 : bv_unsigned (ev E 40) = nxt) by exact (u_wa_small _ (rng64 _ _ _ Rnxt eq_refl)).
  assert (Z41 : bv_unsigned (ev E 41) = bnc) by exact (u_wa_small _ (rng64 _ _ _ Rbnc eq_refl)).
  assert (Z42 : bv_unsigned (ev E 42) = usg) by exact (u_wa_small _ (rng64 _ _ _ Rusg eq_refl)).
  assert (Rav32 : 0 <= avail < 2^32) by (clear - Rav; lia).
  assert (Rfr32 : 0 <= freed < 2^32) by (clear - Rfr; lia).
  assert (RW0 : 0 <= W) by (clear - RW; lia).
  assert (RW64 : 0 <= W < 2^64) by (clear - RW; lia).
  assert (CALL : (bv_swrap 32 (Z.lor (ext_Z true 0 4 avail mod 2^64) (ext_Z true 0 4 freed mod 2^64) + bv_swrap 32 (Z.shiftl 1 (idx mod 32))) mod 2^64
                   =? bv_swrap 32 (bv_swrap 32 (Z.shiftl 2 (W mod 32)) + -1) mod 2^64)
                 = (Z.lor avail freed + 2^idx =? 2^(Z.land W 31 + 1) - 1)).
  { rewrite (Z.mod_small idx 32) by (clear - Ridx; lia). exact (all_cond_z avail freed idx W Rav32 Rfr32 Ridx RW0 A2 A3). }
  assert (CFREE : (Z.land W 32 =? 0) = false) by (apply Z.eqb_neq; exact Ffree).
  assert (CSC : (47 <? SCW W) = false) by (apply Z.ltb_ge; exact Fsc).
  destruct (Z.lor avail freed + 2^idx =? 2^(Z.land W 31 + 1) - 1) eqn:Call.
  2:{ dpath RES_dE2 RES_dE2_ok HR HK E m rom regs sp0 canary. }
  destruct (Z.shiftr W 12 =? 0) eqn:Cml.
  { dpath RES_dG2 RES_dG2_ok HR HK E m rom regs sp0 canary. }
  destruct (Z.land W 31 =? 0) eqn:Cl.
  - destruct (4096 * Z.shiftr W 12 + -16 <? 16 * csz) eqn:Cst.
    { dpath RES_dG1a RES_dG1a_ok HR HK E m rom regs sp0 canary. }
    destruct (nxt =? G) eqn:Cn.
    2:{ dpath RES_dG3a RES_dG3a_ok HR HK E m rom regs sp0 canary. }
    destruct (31 <? (SCW W + -7) mod 2^64) eqn:Cb.
    { dpath RES_dG4a RES_dG4a_ok HR HK E m rom regs sp0 canary. }
    destruct (bnc <? 100) eqn:Cbn.
    { dpath RES_dG5a RES_dG5a_ok HR HK E m rom regs sp0 canary. }
    destruct (usg <? 9 * Z.land W 31 + 9) eqn:Cu.
    { dpath RES_dE4a RES_dE4a_ok HR HK E m rom regs sp0 canary. }
    assert (C18 : (18 <? Z.land W 31) = false) by (apply Z.eqb_eq in Cl; rewrite Cl; reflexivity).
    { dpath RES_dG6a RES_dG6a_ok HR HK E m rom regs sp0 canary. }
  - assert (Cst : (16 * csz <? 16 * csz) = false) by (apply Z.ltb_ge; lia).
    destruct (nxt =? G) eqn:Cn.
    2:{ dpath RES_dG3b RES_dG3b_ok HR HK E m rom regs sp0 canary. }
    destruct (31 <? (SCW W + -7) mod 2^64) eqn:Cb.
    { dpath RES_dG4b RES_dG4b_ok HR HK E m rom regs sp0 canary. }
    destruct (bnc <? 100) eqn:Cbn.
    { dpath RES_dG5b RES_dG5b_ok HR HK E m rom regs sp0 canary. }
    destruct (usg <? 9 * Z.land W 31 + 9) eqn:Cu.
    { dpath RES_dE4b RES_dE4b_ok HR HK E m rom regs sp0 canary. }
    destruct (18 <? Z.land W 31) eqn:C18.
    { dpath RES_dE5b RES_dE5b_ok HR HK E m rom regs sp0 canary. }
    { dpath RES_dG6b RES_dG6b_ok HR HK E m rom regs sp0 canary. }
Qed.
End DEC.
End AXF_decz.

Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxMng OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_eez.AXF_decz.

Module AXF_ee.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_G := EVar 32.
Definition e_idx := EVar 33.
Definition e_sc := EVar 34.
Definition e_avail := EVar 35.
Definition e_freed := EVar 36.
Definition e_sp0 := EVar 37.
Definition e_canary := EVar 38.
Definition e_H := EVar 39.
Definition e_ra := EVar 40.
Definition e_s0 := EVar 41.
Definition e_s1 := EVar 42.
Definition e_s2 := EVar 43.
Definition e_s3 := EVar 44.
Definition STK := SA e_sp0 (-1024).
Definition ACT := EMd M_MUL (ELit 8) e_sc.
Definition sr_ee := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 2 (EAlu ALU_ADD e_sp0 (ELit (-96)))) 9 (ELit 0x95e40)) 10 (e_G)) 11 (EAluw ALU_SLL (ELit 1) e_idx)) 12 (e_sc)) 13 (EAlu ALU_OR (EExt true 0 4 e_avail) (EExt true 0 4 e_freed))).
Definition kn_ee : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KWr STK (ELit 1024);
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange e_idx 0 31;
    KRange e_sc 0 47;
    KRange ACT 0 376;
    KRange e_avail 0 (2^32-1);
    KRange e_freed 0 (2^32-1);
    KWord (SA e_G 28) 4 e_freed;
    KWord (SA ACT 614184) 8 e_H;
    KWord (SA e_sp0 (-8)) 8 e_ra;
    KWord (SA e_sp0 (-16)) 8 e_s0;
    KWord (SA e_sp0 (-24)) 8 e_s1;
    KWord (SA e_sp0 (-32)) 8 e_s2;
    KWord (SA e_sp0 (-40)) 8 e_s3;
    KWord (SA e_sp0 (-48)) 8 e_canary;
    KWord (SA (ELit 0) 0x95e40) 8 e_canary;
    KWr (SA e_G 28) (ELit 4);
    KDisj STK (ELit 1024) (SA e_G 0) (ELit 40);
    KDisj STK (ELit 1024) (SA ACT 614184) (ELit 8);
    KDisj STK (ELit 1024) (SA (ELit 0) 0x95e40) (ELit 8);
    KDisj (SA e_G 0) (ELit 40) (SA (ELit 0) 0x95e40) (ELit 8) ].
Definition scr_ee : scripts := SCR [] [] [].
Definition ss_ee := SS 0x51a2c sr_ee [] kn_ee 45.
Definition RUN_ee := sym_exec SEGS 200 true [] scr_ee ss_ee [].

Definition scr_ee1 : scripts := SCR [true; false; false] [] [].
Definition RES_ee1 := Eval vm_compute in sym_exec SEGS 200 true [] scr_ee1 ss_ee [].
Lemma RES_ee1_ok : sym_exec SEGS 200 true [] scr_ee1 (SS 0x51a2c sr_ee [] kn_ee 45) [] = RES_ee1.
Proof. vm_compute. reflexivity. Qed.

Definition scr_ee2 : scripts := SCR [false; true; false; false] [] [].
Definition RES_ee2 := Eval vm_compute in sym_exec SEGS 200 true [] scr_ee2 ss_ee [].
Lemma RES_ee2_ok : sym_exec SEGS 200 true [] scr_ee2 (SS 0x51a2c sr_ee [] kn_ee 45) [] = RES_ee2.
Proof. vm_compute. reflexivity. Qed.
End AXF_ee.


Module AXF_ee3.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_G := EVar 32.
Definition e_idx := EVar 33.
Definition e_sc := EVar 34.
Definition e_avail := EVar 35.
Definition e_freed := EVar 36.
Definition e_sp0 := EVar 37.
Definition e_canary := EVar 38.
Definition e_ra := EVar 40.
Definition e_s0 := EVar 41.
Definition e_s1 := EVar 42.
Definition e_s2 := EVar 43.
Definition e_s3 := EVar 44.
Definition STK := SA e_sp0 (-1024).
Definition ACT := EMd M_MUL (ELit 8) e_sc.
Definition sr_ee3 := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 2 (EAlu ALU_ADD e_sp0 (ELit (-96)))) 9 (ELit 0x95e40)) 10 (e_G)) 11 (EAluw ALU_SLL (ELit 1) e_idx)) 12 (e_sc)) 13 (EAlu ALU_OR (EExt true 0 4 e_avail) (EExt true 0 4 e_freed))).
Definition kn_ee3 : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KWr STK (ELit 1024);
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange e_idx 0 31;
    KRange e_sc 0 47;
    KRange ACT 0 376;
    KRange e_avail 0 (2^32-1);
    KRange e_freed 0 (2^32-1);
    KWord (SA e_G 28) 4 e_freed;
    KWord (SA ACT 614184) 8 (ELit 0);
    KWord (SA e_G 0) 8 (ELit 0);
    KWord (SA e_G 8) 8 (ELit 0);
    KWord (SA e_sp0 (-8)) 8 e_ra;
    KWord (SA e_sp0 (-16)) 8 e_s0;
    KWord (SA e_sp0 (-24)) 8 e_s1;
    KWord (SA e_sp0 (-32)) 8 e_s2;
    KWord (SA e_sp0 (-40)) 8 e_s3;
    KWord (SA e_sp0 (-48)) 8 e_canary;
    KWord (SA (ELit 0) 0x95e40) 8 e_canary;
    KWr (SA e_G 0) (ELit 16);
    KWr (SA e_G 28) (ELit 4);
    KWr (SA ACT 614184) (ELit 8);
    KDisj STK (ELit 1024) (SA e_G 0) (ELit 40);
    KDisj STK (ELit 1024) (SA ACT 614184) (ELit 8);
    KDisj STK (ELit 1024) (SA (ELit 0) 0x95e40) (ELit 8);
    KDisj (SA e_G 0) (ELit 40) (SA (ELit 0) 0x95e40) (ELit 8);
    KDisj (SA e_G 0) (ELit 40) (SA ACT 614184) (ELit 8);
    KDisj (SA ACT 614184) (ELit 8) (SA (ELit 0) 0x95e40) (ELit 8) ].
Definition scr_ee3 : scripts := SCR [] [] [].
Definition ss_ee3 := SS 0x51a2c sr_ee3 [] kn_ee3 45.
Definition RUN_ee3 := sym_exec SEGS 200 true [] scr_ee3 ss_ee3 [].

Definition scr_pee3 : scripts := SCR [false; false; false; false] [] [].
Definition RES_pee3 := Eval vm_compute in sym_exec SEGS 200 true [] scr_pee3 ss_ee3 [].
Lemma RES_pee3_ok : sym_exec SEGS 200 true [] scr_pee3 (SS 0x51a2c sr_ee3 [] kn_ee3 45) [] = RES_pee3.
Proof. vm_compute. reflexivity. Qed.
End AXF_ee3.


Module AXF_ee4.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_G := EVar 32.
Definition e_idx := EVar 33.
Definition e_sc := EVar 34.
Definition e_avail := EVar 35.
Definition e_freed := EVar 36.
Definition e_sp0 := EVar 37.
Definition e_canary := EVar 38.
Definition e_H := EVar 39.
Definition e_HP := EVar 45.
Definition e_ra := EVar 40.
Definition e_s0 := EVar 41.
Definition e_s1 := EVar 42.
Definition e_s2 := EVar 43.
Definition e_s3 := EVar 44.
Definition STK := SA e_sp0 (-1024).
Definition ACT := EMd M_MUL (ELit 8) e_sc.
Definition sr_ee4 := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 2 (EAlu ALU_ADD e_sp0 (ELit (-96)))) 9 (ELit 0x95e40)) 10 (e_G)) 11 (EAluw ALU_SLL (ELit 1) e_idx)) 12 (e_sc)) 13 (EAlu ALU_OR (EExt true 0 4 e_avail) (EExt true 0 4 e_freed))).
Definition kn_ee4 : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KWr STK (ELit 1024);
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange e_idx 0 31;
    KRange e_sc 0 47;
    KRange ACT 0 376;
    KRange e_avail 0 (2^32-1);
    KRange e_freed 0 (2^32-1);
    KRange e_H 1 (2^63-1);
    KRange e_HP 1 (2^63-1);
    KWord (SA e_G 28) 4 e_freed;
    KWord (SA ACT 614184) 8 e_H;
    KWord (SA e_G 0) 8 (ELit 0);
    KWord (SA e_G 8) 8 (ELit 0);
    KWord (SA e_H 0) 8 e_HP;
    KWord (SA e_sp0 (-8)) 8 e_ra;
    KWord (SA e_sp0 (-16)) 8 e_s0;
    KWord (SA e_sp0 (-24)) 8 e_s1;
    KWord (SA e_sp0 (-32)) 8 e_s2;
    KWord (SA e_sp0 (-40)) 8 e_s3;
    KWord (SA e_sp0 (-48)) 8 e_canary;
    KWord (SA (ELit 0) 0x95e40) 8 e_canary;
    KWr (SA e_G 0) (ELit 16);
    KWr (SA e_G 28) (ELit 4);
    KWr (SA e_H 0) (ELit 8);
    KWr (SA e_HP 8) (ELit 8);
    KDisj STK (ELit 1024) (SA e_G 0) (ELit 40);
    KDisj STK (ELit 1024) (SA ACT 614184) (ELit 8);
    KDisj STK (ELit 1024) (SA (ELit 0) 0x95e40) (ELit 8);
    KDisj STK (ELit 1024) (SA e_H 0) (ELit 40);
    KDisj STK (ELit 1024) (SA e_HP 0) (ELit 40);
    KDisj (SA e_G 0) (ELit 40) (SA (ELit 0) 0x95e40) (ELit 8);
    KDisj (SA e_G 0) (ELit 40) (SA ACT 614184) (ELit 8);
    KDisj (SA e_G 0) (ELit 40) (SA e_H 0) (ELit 40);
    KDisj (SA e_G 0) (ELit 40) (SA e_HP 0) (ELit 40);
    KDisj (SA e_H 0) (ELit 40) (SA (ELit 0) 0x95e40) (ELit 8);
    KDisj (SA e_HP 0) (ELit 40) (SA (ELit 0) 0x95e40) (ELit 8);
    KDisj (SA e_H 0) (ELit 40) (SA ACT 614184) (ELit 8);
    KDisj (SA e_HP 0) (ELit 40) (SA ACT 614184) (ELit 8) ].
Definition scr_ee4 : scripts := SCR [] [] [].
Definition ss_ee4 := SS 0x51a2c sr_ee4 [] kn_ee4 46.
Definition RUN_ee4 := sym_exec SEGS 200 true [] scr_ee4 ss_ee4 [].

Definition scr_pee4 : scripts := SCR [false; false; false; false; false] [] [].
Definition RES_pee4 := Eval vm_compute in sym_exec SEGS 200 true [] scr_pee4 ss_ee4 [].
Lemma RES_pee4_ok : sym_exec SEGS 200 true [] scr_pee4 (SS 0x51a2c sr_ee4 [] kn_ee4 46) [] = RES_pee4.
Proof. vm_compute. reflexivity. Qed.
End AXF_ee4.

Import ListNotations AX2 AX2S.

Module AXF_dq0.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_G := EVar 32.
Definition e_sc := EVar 33.
Definition e_sp0 := EVar 34.
Definition STK := SA e_sp0 (-1024).
Definition sr_dq0 := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 2 (EAlu ALU_ADD e_sp0 (ELit (-96)))) 9 (ELit 0x95e40)) 10 (e_G)) 12 (e_sc)) 18 (ELit 0x95ed8)).
Definition kn_dq0 : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KWr STK (ELit 1024);
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange e_sc 0 63;
    KWord (SA e_G 8) 8 (ELit 0);
    KDisj STK (ELit 1024) (SA e_G 0) (ELit 40) ].
Definition scr_dq0 : scripts := SCR [] [] [].
Definition ss_dq0 := SS 0x519e4 sr_dq0 [] kn_dq0 35.
Definition RUN_dq0 := sym_exec SEGS 100 true [0x51af8] scr_dq0 ss_dq0 [].

Definition scr_pdq0 : scripts := SCR [false] [] [].
Definition RES_pdq0 := Eval vm_compute in sym_exec SEGS 100 true [0x51af8] scr_pdq0 ss_dq0 [].
Lemma RES_pdq0_ok : sym_exec SEGS 100 true [0x51af8] scr_pdq0 (SS 0x519e4 sr_dq0 [] kn_dq0 35) [] = RES_pdq0.
Proof. vm_compute. reflexivity. Qed.
End AXF_dq0.

Module AXF_dq0z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section DQ0.
Context {fx : FPState}.

Definition VALS_dq0 (G sc sp0 : Z) : list Z := [G; sc; sp0].

Record dq0_pre (regs : bvmap 5 word) (m : word -> option byte) (G sc sp0 : Z) : Prop := {
  dq0_R2 : getr regs 2 = wa (sp0 + -96) ;
  dq0_R9 : getr regs 9 = wa 613952 ;
  dq0_R10 : getr regs 10 = wa G ;
  dq0_R12 : getr regs 12 = wa sc ;
  dq0_R18 : getr regs 18 = wa 614104 ;
  dq0_HSTK : stk_ok SEGS m (wa sp0) 1024 ;
  dq0_rng_G : 1 <= G <= 2^63-1 ;
  dq0_rng_sc : 0 <= sc <= 63 ;
  dq0_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  dq0_ka1 : sp0 mod 16 = 0 ;
  dq0_ka4 : G mod 8 = 0 ;
  dq0_kw6 : rdn SEGS m (wa (G + 8)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  dq0_kd7 : sp0 + -1024 + 1024 <= G + 0 \/ G + 0 + 40 <= sp0 + -1024
}.


#[using="Type"] Lemma dq0_setup : forall regs m G sc sp0, dq0_pre regs m G sc sp0 ->
  regs_ok (Ez regs (VALS_dq0 G sc sp0)) AXF_dq0.sr_dq0 regs /\ know_ok SEGS (Ez regs (VALS_dq0 G sc sp0)) m AXF_dq0.kn_dq0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G sc sp0 P. destruct P as [dq0_R2 dq0_R9 dq0_R10 dq0_R12 dq0_R18 dq0_HSTK dq0_rng_G dq0_rng_sc dq0_rng_sp0 dq0_ka1 dq0_ka4 dq0_kw6 dq0_kd7].
  set (E := Ez regs (VALS_dq0 G sc sp0)).
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_dq0.sr_dq0.
    apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 2); [apply regs_ok_id|]|]|]|]|].
    - rewrite dq0_R2, zeval_sound. cbn [zeval edenot AXF_dq0.e_G AXF_dq0.e_sc AXF_dq0.e_sp0 AXF_dq0.STK]. rewrite ?Z32, ?Z33, ?Z34. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite dq0_R9. reflexivity.
    - rewrite dq0_R10. reflexivity.
    - rewrite dq0_R12. reflexivity.
    - rewrite dq0_R18. reflexivity. }
  unfold know_ok, AXF_dq0.kn_dq0.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_dq0.e_sp0 (wa sp0) 1024); [reflexivity | assumption | rewrite u_wa_small by lia; lia])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_dq0.e_G AXF_dq0.e_sc AXF_dq0.e_sp0 AXF_dq0.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range G _ _ dq0_rng_G eq_refl eq_refl), ?(mod64_of_range sc _ _ dq0_rng_sc eq_refl eq_refl), ?(mod64_of_range sp0 _ _ dq0_rng_sp0 eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - dq0_rng_G dq0_rng_sc dq0_rng_sp0 dq0_ka1 dq0_ka4; lia).
  all: first [(clear - dq0_rng_G dq0_rng_sc dq0_rng_sp0 dq0_ka1 dq0_ka4 dq0_kd7; lia) | lia].
Qed.


Definition dq0_mem_pdq0 (m : word -> option byte) (regs : bvmap 5 word) (G sc sp0 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem dq0_pdq0 : forall regs m rom G sc sp0, dq0_pre regs m G sc sp0 ->
  scs_denot SEGS m (Ez regs (VALS_dq0 G sc sp0)) (snd (fst AXF_dq0.RES_pdq0)) ->
  exists R, msteps SEGS (mkst regs (wa 0x519e4) m rom) (mkst R (wa 0x51af8) (dq0_mem_pdq0 m regs G sc sp0) rom) /\
    getr R 2 = wa (sp0 + -96) /\ getr R 9 = wa 613952 /\ getr R 10 = wa G /\ getr R 12 = wa sc /\ getr R 13 = wa 0 /\ getr R 18 = wa 614104 /\ (forall k, In k [1; 3; 4; 5; 6; 7; 8; 11; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G sc sp0 P Hsc. destruct (dq0_setup regs m G sc sp0 P) as [HR HK].
  set (E := Ez regs (VALS_dq0 G sc sp0)) in *. destruct P as [dq0_R2 dq0_R9 dq0_R10 dq0_R12 dq0_R18 dq0_HSTK dq0_rng_G dq0_rng_sc dq0_rng_sp0 dq0_ka1 dq0_ka4 dq0_kw6 dq0_kd7].
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x51af8] AXF_dq0.scr_pdq0 0x519e4 AXF_dq0.sr_dq0 AXF_dq0.kn_dq0 35 _ _ _ E m rom regs AXF_dq0.RES_pdq0_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_dq0.RES_pdq0 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (dq0_mem_pdq0 m regs G sc sp0) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold dq0_mem_pdq0. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End DQ0.
End AXF_dq0z.

Module AXF_dq1.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_G := EVar 32.
Definition e_sc := EVar 33.
Definition e_sp0 := EVar 34.
Definition STK := SA e_sp0 (-1024).
Definition ACT := EMd M_MUL (ELit 8) e_sc.
Definition sr_dq1 := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 2 (EAlu ALU_ADD e_sp0 (ELit (-96)))) 9 (ELit 0x95e40)) 10 (e_G)) 12 (e_sc)) 18 (ELit 0x95ed8)).
Definition kn_dq1 : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KWr STK (ELit 1024);
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange e_sc 0 47;
    KRange ACT 0 376;
    KWord (SA e_G 8) 8 e_G;
    KWord (SA ACT 614184) 8 e_G;
    KWr (SA e_G 0) (ELit 16);
    KWr (SA ACT 614184) (ELit 8);
    KDisj STK (ELit 1024) (SA e_G 0) (ELit 40);
    KDisj STK (ELit 1024) (SA ACT 614184) (ELit 8);
    KDisj (SA e_G 0) (ELit 40) (SA ACT 614184) (ELit 8) ].
Definition scr_dq1 : scripts := SCR [] [] [].
Definition ss_dq1 := SS 0x519e4 sr_dq1 [] kn_dq1 35.
Definition RUN_dq1 := sym_exec SEGS 100 true [0x51af8] scr_dq1 ss_dq1 [].

Definition scr_pdq1 : scripts := SCR [false; false; false] [] [].
Definition RES_pdq1 := Eval vm_compute in sym_exec SEGS 100 true [0x51af8] scr_pdq1 ss_dq1 [].
Lemma RES_pdq1_ok : sym_exec SEGS 100 true [0x51af8] scr_pdq1 (SS 0x519e4 sr_dq1 [] kn_dq1 35) [] = RES_pdq1.
Proof. vm_compute. reflexivity. Qed.
End AXF_dq1.

Module AXF_dq1z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section DQ1.
Context {fx : FPState}.

Definition VALS_dq1 (G sc sp0 : Z) : list Z := [G; sc; sp0].

Record dq1_pre (regs : bvmap 5 word) (m : word -> option byte) (G sc sp0 : Z) : Prop := {
  dq1_R2 : getr regs 2 = wa (sp0 + -96) ;
  dq1_R9 : getr regs 9 = wa 613952 ;
  dq1_R10 : getr regs 10 = wa G ;
  dq1_R12 : getr regs 12 = wa sc ;
  dq1_R18 : getr regs 18 = wa 614104 ;
  dq1_HSTK : stk_ok SEGS m (wa sp0) 1024 ;
  dq1_rng_G : 1 <= G <= 2^63-1 ;
  dq1_rng_sc : 0 <= sc <= 47 ;
  dq1_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  dq1_ka1 : sp0 mod 16 = 0 ;
  dq1_ka4 : G mod 8 = 0 ;
  dq1_kr6 : 0 <= 8 * sc <= 376 ;
  dq1_kw7 : rdn SEGS m (wa (G + 8)) 8 = Some (word_to_le_bytes 8 (wa G)) ;
  dq1_kw8 : rdn SEGS m (wa (8 * sc + 614184)) 8 = Some (word_to_le_bytes 8 (wa G)) ;
  dq1_kwr9 : forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS m (wa (G + 0 + d)) k = true ;
  dq1_kwr10 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (8 * sc + 614184 + d)) k = true ;
  dq1_kd11 : sp0 + -1024 + 1024 <= G + 0 \/ G + 0 + 40 <= sp0 + -1024 ;
  dq1_kd12 : sp0 + -1024 + 1024 <= 8 * sc + 614184 \/ 8 * sc + 614184 + 8 <= sp0 + -1024 ;
  dq1_kd13 : G + 0 + 40 <= 8 * sc + 614184 \/ 8 * sc + 614184 + 8 <= G + 0
}.


#[using="Type"] Lemma dq1_setup : forall regs m G sc sp0, dq1_pre regs m G sc sp0 ->
  regs_ok (Ez regs (VALS_dq1 G sc sp0)) AXF_dq1.sr_dq1 regs /\ know_ok SEGS (Ez regs (VALS_dq1 G sc sp0)) m AXF_dq1.kn_dq1.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G sc sp0 P. destruct P as [dq1_R2 dq1_R9 dq1_R10 dq1_R12 dq1_R18 dq1_HSTK dq1_rng_G dq1_rng_sc dq1_rng_sp0 dq1_ka1 dq1_ka4 dq1_kr6 dq1_kw7 dq1_kw8 dq1_kwr9 dq1_kwr10 dq1_kd11 dq1_kd12 dq1_kd13].
  set (E := Ez regs (VALS_dq1 G sc sp0)).
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_dq1.sr_dq1.
    apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 2); [apply regs_ok_id|]|]|]|]|].
    - rewrite dq1_R2, zeval_sound. cbn [zeval edenot AXF_dq1.e_G AXF_dq1.e_sc AXF_dq1.e_sp0 AXF_dq1.STK AXF_dq1.ACT]. rewrite ?Z32, ?Z33, ?Z34. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite dq1_R9. reflexivity.
    - rewrite dq1_R10. reflexivity.
    - rewrite dq1_R12. reflexivity.
    - rewrite dq1_R18. reflexivity. }
  unfold know_ok, AXF_dq1.kn_dq1.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_dq1.e_sp0 (wa sp0) 1024); [reflexivity | assumption | rewrite u_wa_small by lia; lia])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_dq1.e_G AXF_dq1.e_sc AXF_dq1.e_sp0 AXF_dq1.STK AXF_dq1.ACT a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range G _ _ dq1_rng_G eq_refl eq_refl), ?(mod64_of_range sc _ _ dq1_rng_sc eq_refl eq_refl), ?(mod64_of_range sp0 _ _ dq1_rng_sp0 eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply dq1_kwr9 | apply dq1_kwr10]; assumption).
  all: try (clear - dq1_rng_G dq1_rng_sc dq1_rng_sp0 dq1_ka1 dq1_ka4 dq1_kr6; lia).
  all: first [(clear - dq1_rng_G dq1_rng_sc dq1_rng_sp0 dq1_ka1 dq1_ka4 dq1_kr6 dq1_kd11; lia) | (clear - dq1_rng_G dq1_rng_sc dq1_rng_sp0 dq1_ka1 dq1_ka4 dq1_kr6 dq1_kd12; lia) | (clear - dq1_rng_G dq1_rng_sc dq1_rng_sp0 dq1_ka1 dq1_ka4 dq1_kr6 dq1_kd13; lia) | lia].
Qed.


Definition dq1_mem_pdq1 (m : word -> option byte) (regs : bvmap 5 word) (G sc sp0 : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (m) (wa (8 * sc + 614184)) (word_to_le_bytes 8 (wa 0))) (wa (G + 0)) (word_to_le_bytes 8 (wa 0))) (wa (G + 8)) (word_to_le_bytes 8 (wa 0)).

#[using="Type"] Theorem dq1_pdq1 : forall regs m rom G sc sp0, dq1_pre regs m G sc sp0 ->
  scs_denot SEGS m (Ez regs (VALS_dq1 G sc sp0)) (snd (fst AXF_dq1.RES_pdq1)) ->
  exists R, msteps SEGS (mkst regs (wa 0x519e4) m rom) (mkst R (wa 0x51af8) (dq1_mem_pdq1 m regs G sc sp0) rom) /\
    getr R 2 = wa (sp0 + -96) /\ getr R 9 = wa 613952 /\ getr R 10 = wa G /\ getr R 11 = wa 0 /\ getr R 12 = wa G /\ getr R 13 = wa 0 /\ getr R 18 = wa 614104 /\ (forall k, In k [1; 3; 4; 5; 6; 7; 8; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G sc sp0 P Hsc. destruct (dq1_setup regs m G sc sp0 P) as [HR HK].
  set (E := Ez regs (VALS_dq1 G sc sp0)) in *. destruct P as [dq1_R2 dq1_R9 dq1_R10 dq1_R12 dq1_R18 dq1_HSTK dq1_rng_G dq1_rng_sc dq1_rng_sp0 dq1_ka1 dq1_ka4 dq1_kr6 dq1_kw7 dq1_kw8 dq1_kwr9 dq1_kwr10 dq1_kd11 dq1_kd12 dq1_kd13].
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x51af8] AXF_dq1.scr_pdq1 0x519e4 AXF_dq1.sr_dq1 AXF_dq1.kn_dq1 35 _ _ _ E m rom regs AXF_dq1.RES_pdq1_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_dq1.RES_pdq1 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (dq1_mem_pdq1 m regs G sc sp0) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold dq1_mem_pdq1. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End DQ1.
End AXF_dq1z.

Module AXF_dq2.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_G := EVar 32.
Definition e_sc := EVar 33.
Definition e_sp0 := EVar 34.
Definition e_NX := EVar 35.
Definition e_PR := EVar 36.
Definition e_NMEM := EVar 37.
Definition e_AIDXB := EVar 38.
Definition e_NFR := EVar 39.
Definition STK := SA e_sp0 (-1024).
Definition ACT := EMd M_MUL (ELit 8) e_sc.
Definition sr_dq2 := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 2 (EAlu ALU_ADD e_sp0 (ELit (-96)))) 9 (ELit 0x95e40)) 10 (e_G)) 12 (e_sc)) 18 (ELit 0x95ed8)).
Definition kn_dq2 : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KWr STK (ELit 1024);
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange e_sc 0 47;
    KRange ACT 0 376;
    KRange e_NX 1 (2^63-1);
    KAlign e_NX 8;
    KRange e_PR 1 (2^63-1);
    KRange e_NMEM 1 (2^63-1);
    KRange e_AIDXB 0 255;
    KRange e_NFR 0 (2^32-1);
    KWord (SA e_G 8) 8 e_NX;
    KWord (SA e_G 0) 8 e_PR;
    KWord (SA ACT 614184) 8 e_G;
    KWord (SA e_NX 24) 4 (ELit 0);
    KWord (SA e_NX 16) 8 e_NMEM;
    KWord (SA e_NMEM 8) 1 e_AIDXB;
    KWord (SA e_NX 28) 4 e_NFR;
    KWr (SA e_G 0) (ELit 16);
    KWr (SA e_PR 8) (ELit 8);
    KWr (SA e_NX 0) (ELit 8);
    KWr (SA ACT 614184) (ELit 8);
    KWr (SA e_NX 24) (ELit 8);
    KDisj STK (ELit 1024) (SA e_G 0) (ELit 40);
    KDisj STK (ELit 1024) (SA ACT 614184) (ELit 8);
    KDisj STK (ELit 1024) (SA e_PR 8) (ELit 8);
    KDisj STK (ELit 1024) (SA e_NX 0) (ELit 40);
    KDisj STK (ELit 1024) (SA e_NMEM 8) (ELit 1);
    KDisj (SA e_G 0) (ELit 40) (SA ACT 614184) (ELit 8);
    KDisj (SA e_G 0) (ELit 40) (SA e_PR 8) (ELit 8);
    KDisj (SA e_G 0) (ELit 40) (SA e_NX 0) (ELit 40);
    KDisj (SA ACT 614184) (ELit 8) (SA e_PR 8) (ELit 8);
    KDisj (SA ACT 614184) (ELit 8) (SA e_NX 0) (ELit 40);
    KDisj (SA e_PR 8) (ELit 8) (SA e_NX 16) (ELit 16);
    KDisj (SA e_NMEM 8) (ELit 1) (SA e_PR 8) (ELit 8);
    KDisj (SA e_NMEM 8) (ELit 1) (SA e_NX 0) (ELit 40);
    KDisj (SA e_NMEM 8) (ELit 1) (SA e_G 0) (ELit 40);
    KDisj (SA e_NMEM 8) (ELit 1) (SA ACT 614184) (ELit 8) ].
Definition scr_dq2 : scripts := SCR [] [] [].
Definition ss_dq2 := SS 0x519e4 sr_dq2 [] kn_dq2 40.
Definition RUN_dq2 := sym_exec SEGS 150 true [0x51af8] scr_dq2 ss_dq2 [].

Definition scr_pdq2 : scripts := SCR [false; false; false; false; false; false; false; false] [] [].
Definition RES_pdq2 := Eval vm_compute in sym_exec SEGS 150 true [0x51af8] scr_pdq2 ss_dq2 [].
Lemma RES_pdq2_ok : sym_exec SEGS 150 true [0x51af8] scr_pdq2 (SS 0x519e4 sr_dq2 [] kn_dq2 40) [] = RES_pdq2.
Proof. vm_compute. reflexivity. Qed.
End AXF_dq2.

Module AXF_dq2z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section DQ2.
Context {fx : FPState}.

Definition VALS_dq2 (G sc sp0 NX PR NMEM AIDXB NFR : Z) : list Z := [G; sc; sp0; NX; PR; NMEM; AIDXB; NFR].

Record dq2_pre (regs : bvmap 5 word) (m : word -> option byte) (G sc sp0 NX PR NMEM AIDXB NFR : Z) : Prop := {
  dq2_R2 : getr regs 2 = wa (sp0 + -96) ;
  dq2_R9 : getr regs 9 = wa 613952 ;
  dq2_R10 : getr regs 10 = wa G ;
  dq2_R12 : getr regs 12 = wa sc ;
  dq2_R18 : getr regs 18 = wa 614104 ;
  dq2_HSTK : stk_ok SEGS m (wa sp0) 1024 ;
  dq2_rng_G : 1 <= G <= 2^63-1 ;
  dq2_rng_sc : 0 <= sc <= 47 ;
  dq2_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  dq2_rng_NX : 1 <= NX <= 2^63-1 ;
  dq2_rng_PR : 1 <= PR <= 2^63-1 ;
  dq2_rng_NMEM : 1 <= NMEM <= 2^63-1 ;
  dq2_rng_AIDXB : 0 <= AIDXB <= 255 ;
  dq2_rng_NFR : 0 <= NFR <= 2^32-1 ;
  dq2_ka1 : sp0 mod 16 = 0 ;
  dq2_ka4 : G mod 8 = 0 ;
  dq2_kr6 : 0 <= 8 * sc <= 376 ;
  dq2_ka8 : NX mod 8 = 0 ;
  dq2_kw13 : rdn SEGS m (wa (G + 8)) 8 = Some (word_to_le_bytes 8 (wa NX)) ;
  dq2_kw14 : rdn SEGS m (wa (G + 0)) 8 = Some (word_to_le_bytes 8 (wa PR)) ;
  dq2_kw15 : rdn SEGS m (wa (8 * sc + 614184)) 8 = Some (word_to_le_bytes 8 (wa G)) ;
  dq2_kw16 : rdn SEGS m (wa (NX + 24)) 4 = Some (word_to_le_bytes 4 (wa 0)) ;
  dq2_kw17 : rdn SEGS m (wa (NX + 16)) 8 = Some (word_to_le_bytes 8 (wa NMEM)) ;
  dq2_kw18 : rdn SEGS m (wa (NMEM + 8)) 1 = Some (word_to_le_bytes 1 (wa AIDXB)) ;
  dq2_kw19 : rdn SEGS m (wa (NX + 28)) 4 = Some (word_to_le_bytes 4 (wa NFR)) ;
  dq2_kwr20 : forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS m (wa (G + 0 + d)) k = true ;
  dq2_kwr21 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (PR + 8 + d)) k = true ;
  dq2_kwr22 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (NX + 0 + d)) k = true ;
  dq2_kwr23 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (8 * sc + 614184 + d)) k = true ;
  dq2_kwr24 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (NX + 24 + d)) k = true ;
  dq2_kd25 : sp0 + -1024 + 1024 <= G + 0 \/ G + 0 + 40 <= sp0 + -1024 ;
  dq2_kd26 : sp0 + -1024 + 1024 <= 8 * sc + 614184 \/ 8 * sc + 614184 + 8 <= sp0 + -1024 ;
  dq2_kd27 : sp0 + -1024 + 1024 <= PR + 8 \/ PR + 8 + 8 <= sp0 + -1024 ;
  dq2_kd28 : sp0 + -1024 + 1024 <= NX + 0 \/ NX + 0 + 40 <= sp0 + -1024 ;
  dq2_kd29 : sp0 + -1024 + 1024 <= NMEM + 8 \/ NMEM + 8 + 1 <= sp0 + -1024 ;
  dq2_kd30 : G + 0 + 40 <= 8 * sc + 614184 \/ 8 * sc + 614184 + 8 <= G + 0 ;
  dq2_kd31 : G + 0 + 40 <= PR + 8 \/ PR + 8 + 8 <= G + 0 ;
  dq2_kd32 : G + 0 + 40 <= NX + 0 \/ NX + 0 + 40 <= G + 0 ;
  dq2_kd33 : 8 * sc + 614184 + 8 <= PR + 8 \/ PR + 8 + 8 <= 8 * sc + 614184 ;
  dq2_kd34 : 8 * sc + 614184 + 8 <= NX + 0 \/ NX + 0 + 40 <= 8 * sc + 614184 ;
  dq2_kd35 : PR + 8 + 8 <= NX + 16 \/ NX + 16 + 16 <= PR + 8 ;
  dq2_kd36 : NMEM + 8 + 1 <= PR + 8 \/ PR + 8 + 8 <= NMEM + 8 ;
  dq2_kd37 : NMEM + 8 + 1 <= NX + 0 \/ NX + 0 + 40 <= NMEM + 8 ;
  dq2_kd38 : NMEM + 8 + 1 <= G + 0 \/ G + 0 + 40 <= NMEM + 8 ;
  dq2_kd39 : NMEM + 8 + 1 <= 8 * sc + 614184 \/ 8 * sc + 614184 + 8 <= NMEM + 8
}.


#[using="Type"] Lemma dq2_setup : forall regs m G sc sp0 NX PR NMEM AIDXB NFR, dq2_pre regs m G sc sp0 NX PR NMEM AIDXB NFR ->
  regs_ok (Ez regs (VALS_dq2 G sc sp0 NX PR NMEM AIDXB NFR)) AXF_dq2.sr_dq2 regs /\ know_ok SEGS (Ez regs (VALS_dq2 G sc sp0 NX PR NMEM AIDXB NFR)) m AXF_dq2.kn_dq2.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G sc sp0 NX PR NMEM AIDXB NFR P. destruct P as [dq2_R2 dq2_R9 dq2_R10 dq2_R12 dq2_R18 dq2_HSTK dq2_rng_G dq2_rng_sc dq2_rng_sp0 dq2_rng_NX dq2_rng_PR dq2_rng_NMEM dq2_rng_AIDXB dq2_rng_NFR dq2_ka1 dq2_ka4 dq2_kr6 dq2_ka8 dq2_kw13 dq2_kw14 dq2_kw15 dq2_kw16 dq2_kw17 dq2_kw18 dq2_kw19 dq2_kwr20 dq2_kwr21 dq2_kwr22 dq2_kwr23 dq2_kwr24 dq2_kd25 dq2_kd26 dq2_kd27 dq2_kd28 dq2_kd29 dq2_kd30 dq2_kd31 dq2_kd32 dq2_kd33 dq2_kd34 dq2_kd35 dq2_kd36 dq2_kd37 dq2_kd38 dq2_kd39].
  set (E := Ez regs (VALS_dq2 G sc sp0 NX PR NMEM AIDXB NFR)).
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = NX) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = PR) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = NMEM) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = AIDXB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = NFR) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_dq2.sr_dq2.
    apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 2); [apply regs_ok_id|]|]|]|]|].
    - rewrite dq2_R2, zeval_sound. cbn [zeval edenot AXF_dq2.e_G AXF_dq2.e_sc AXF_dq2.e_sp0 AXF_dq2.e_NX AXF_dq2.e_PR AXF_dq2.e_NMEM AXF_dq2.e_AIDXB AXF_dq2.e_NFR AXF_dq2.STK AXF_dq2.ACT]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite dq2_R9. reflexivity.
    - rewrite dq2_R10. reflexivity.
    - rewrite dq2_R12. reflexivity.
    - rewrite dq2_R18. reflexivity. }
  unfold know_ok, AXF_dq2.kn_dq2.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_dq2.e_sp0 (wa sp0) 1024); [reflexivity | assumption | rewrite u_wa_small by lia; lia])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_dq2.e_G AXF_dq2.e_sc AXF_dq2.e_sp0 AXF_dq2.e_NX AXF_dq2.e_PR AXF_dq2.e_NMEM AXF_dq2.e_AIDXB AXF_dq2.e_NFR AXF_dq2.STK AXF_dq2.ACT a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range G _ _ dq2_rng_G eq_refl eq_refl), ?(mod64_of_range sc _ _ dq2_rng_sc eq_refl eq_refl), ?(mod64_of_range sp0 _ _ dq2_rng_sp0 eq_refl eq_refl), ?(mod64_of_range NX _ _ dq2_rng_NX eq_refl eq_refl), ?(mod64_of_range PR _ _ dq2_rng_PR eq_refl eq_refl), ?(mod64_of_range NMEM _ _ dq2_rng_NMEM eq_refl eq_refl), ?(mod64_of_range AIDXB _ _ dq2_rng_AIDXB eq_refl eq_refl), ?(mod64_of_range NFR _ _ dq2_rng_NFR eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply dq2_kwr20 | apply dq2_kwr21 | apply dq2_kwr22 | apply dq2_kwr23 | apply dq2_kwr24]; assumption).
  all: try (clear - dq2_rng_G dq2_rng_sc dq2_rng_sp0 dq2_rng_NX dq2_rng_PR dq2_rng_NMEM dq2_rng_AIDXB dq2_rng_NFR dq2_ka1 dq2_ka4 dq2_kr6 dq2_ka8; lia).
  all: first [(clear - dq2_rng_G dq2_rng_sc dq2_rng_sp0 dq2_rng_NX dq2_rng_PR dq2_rng_NMEM dq2_rng_AIDXB dq2_rng_NFR dq2_ka1 dq2_ka4 dq2_kr6 dq2_ka8 dq2_kd25; lia) | (clear - dq2_rng_G dq2_rng_sc dq2_rng_sp0 dq2_rng_NX dq2_rng_PR dq2_rng_NMEM dq2_rng_AIDXB dq2_rng_NFR dq2_ka1 dq2_ka4 dq2_kr6 dq2_ka8 dq2_kd26; lia) | (clear - dq2_rng_G dq2_rng_sc dq2_rng_sp0 dq2_rng_NX dq2_rng_PR dq2_rng_NMEM dq2_rng_AIDXB dq2_rng_NFR dq2_ka1 dq2_ka4 dq2_kr6 dq2_ka8 dq2_kd27; lia) | (clear - dq2_rng_G dq2_rng_sc dq2_rng_sp0 dq2_rng_NX dq2_rng_PR dq2_rng_NMEM dq2_rng_AIDXB dq2_rng_NFR dq2_ka1 dq2_ka4 dq2_kr6 dq2_ka8 dq2_kd28; lia) | (clear - dq2_rng_G dq2_rng_sc dq2_rng_sp0 dq2_rng_NX dq2_rng_PR dq2_rng_NMEM dq2_rng_AIDXB dq2_rng_NFR dq2_ka1 dq2_ka4 dq2_kr6 dq2_ka8 dq2_kd29; lia) | (clear - dq2_rng_G dq2_rng_sc dq2_rng_sp0 dq2_rng_NX dq2_rng_PR dq2_rng_NMEM dq2_rng_AIDXB dq2_rng_NFR dq2_ka1 dq2_ka4 dq2_kr6 dq2_ka8 dq2_kd30; lia) | (clear - dq2_rng_G dq2_rng_sc dq2_rng_sp0 dq2_rng_NX dq2_rng_PR dq2_rng_NMEM dq2_rng_AIDXB dq2_rng_NFR dq2_ka1 dq2_ka4 dq2_kr6 dq2_ka8 dq2_kd31; lia) | (clear - dq2_rng_G dq2_rng_sc dq2_rng_sp0 dq2_rng_NX dq2_rng_PR dq2_rng_NMEM dq2_rng_AIDXB dq2_rng_NFR dq2_ka1 dq2_ka4 dq2_kr6 dq2_ka8 dq2_kd32; lia) | (clear - dq2_rng_G dq2_rng_sc dq2_rng_sp0 dq2_rng_NX dq2_rng_PR dq2_rng_NMEM dq2_rng_AIDXB dq2_rng_NFR dq2_ka1 dq2_ka4 dq2_kr6 dq2_ka8 dq2_kd33; lia) | (clear - dq2_rng_G dq2_rng_sc dq2_rng_sp0 dq2_rng_NX dq2_rng_PR dq2_rng_NMEM dq2_rng_AIDXB dq2_rng_NFR dq2_ka1 dq2_ka4 dq2_kr6 dq2_ka8 dq2_kd34; lia) | (clear - dq2_rng_G dq2_rng_sc dq2_rng_sp0 dq2_rng_NX dq2_rng_PR dq2_rng_NMEM dq2_rng_AIDXB dq2_rng_NFR dq2_ka1 dq2_ka4 dq2_kr6 dq2_ka8 dq2_kd35; lia) | (clear - dq2_rng_G dq2_rng_sc dq2_rng_sp0 dq2_rng_NX dq2_rng_PR dq2_rng_NMEM dq2_rng_AIDXB dq2_rng_NFR dq2_ka1 dq2_ka4 dq2_kr6 dq2_ka8 dq2_kd36; lia) | (clear - dq2_rng_G dq2_rng_sc dq2_rng_sp0 dq2_rng_NX dq2_rng_PR dq2_rng_NMEM dq2_rng_AIDXB dq2_rng_NFR dq2_ka1 dq2_ka4 dq2_kr6 dq2_ka8 dq2_kd37; lia) | (clear - dq2_rng_G dq2_rng_sc dq2_rng_sp0 dq2_rng_NX dq2_rng_PR dq2_rng_NMEM dq2_rng_AIDXB dq2_rng_NFR dq2_ka1 dq2_ka4 dq2_kr6 dq2_ka8 dq2_kd38; lia) | (clear - dq2_rng_G dq2_rng_sc dq2_rng_sp0 dq2_rng_NX dq2_rng_PR dq2_rng_NMEM dq2_rng_AIDXB dq2_rng_NFR dq2_ka1 dq2_ka4 dq2_kr6 dq2_ka8 dq2_kd39; lia) | lia].
Qed.


Definition dq2_mem_pdq2 (m : word -> option byte) (regs : bvmap 5 word) (G sc sp0 NX PR NMEM AIDXB NFR : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (PR + 8)) (word_to_le_bytes 8 (wa NX))) (wa (NX + 0)) (word_to_le_bytes 8 (wa PR))) (wa (8 * sc + 614184)) (word_to_le_bytes 8 (wa NX))) (wa (G + 0)) (word_to_le_bytes 8 (wa 0))) (wa (G + 8)) (word_to_le_bytes 8 (wa 0))) (wa (NX + 28)) (word_to_le_bytes 4 (wa (Z.ldiff NFR (2 ^ (Z.land AIDXB 31 + 1) - 1))))) (wa (NX + 24)) (word_to_le_bytes 4 (wa (Z.land NFR (2 ^ (Z.land AIDXB 31 + 1) - 1)))).

#[using="Type"] Theorem dq2_pdq2 : forall regs m rom G sc sp0 NX PR NMEM AIDXB NFR, dq2_pre regs m G sc sp0 NX PR NMEM AIDXB NFR ->
  scs_denot SEGS m (Ez regs (VALS_dq2 G sc sp0 NX PR NMEM AIDXB NFR)) (snd (fst AXF_dq2.RES_pdq2)) ->
  exists R, msteps SEGS (mkst regs (wa 0x519e4) m rom) (mkst R (wa 0x51af8) (dq2_mem_pdq2 m regs G sc sp0 NX PR NMEM AIDXB NFR) rom) /\
    getr R 2 = wa (sp0 + -96) /\ getr R 5 = wa 0 /\ getr R 9 = wa 613952 /\ getr R 10 = wa G /\ getr R 11 = wa NX /\ getr R 13 = wa (NX + 28) /\ getr R 18 = wa 614104 /\ (forall k, In k [1; 3; 4; 6; 7; 8; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G sc sp0 NX PR NMEM AIDXB NFR P Hsc. destruct (dq2_setup regs m G sc sp0 NX PR NMEM AIDXB NFR P) as [HR HK].
  set (E := Ez regs (VALS_dq2 G sc sp0 NX PR NMEM AIDXB NFR)) in *. destruct P as [dq2_R2 dq2_R9 dq2_R10 dq2_R12 dq2_R18 dq2_HSTK dq2_rng_G dq2_rng_sc dq2_rng_sp0 dq2_rng_NX dq2_rng_PR dq2_rng_NMEM dq2_rng_AIDXB dq2_rng_NFR dq2_ka1 dq2_ka4 dq2_kr6 dq2_ka8 dq2_kw13 dq2_kw14 dq2_kw15 dq2_kw16 dq2_kw17 dq2_kw18 dq2_kw19 dq2_kwr20 dq2_kwr21 dq2_kwr22 dq2_kwr23 dq2_kwr24 dq2_kd25 dq2_kd26 dq2_kd27 dq2_kd28 dq2_kd29 dq2_kd30 dq2_kd31 dq2_kd32 dq2_kd33 dq2_kd34 dq2_kd35 dq2_kd36 dq2_kd37 dq2_kd38 dq2_kd39].
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = NX) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = PR) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = NMEM) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = AIDXB) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = NFR) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 150 [0x51af8] AXF_dq2.scr_pdq2 0x519e4 AXF_dq2.sr_dq2 AXF_dq2.kn_dq2 40 _ _ _ E m rom regs AXF_dq2.RES_pdq2_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_dq2.RES_pdq2 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (dq2_mem_pdq2 m regs G sc sp0 NX PR NMEM AIDXB NFR) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold dq2_mem_pdq2. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.
    all: try (rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; apply act_avail_le; assumption).
    all: try (rewrite zeval_sound; cbn [zeval edenot]; rewrite w_subw, w_sllw; unfold v_subw, v_sllw; rewrite ?u_wa; repeat dsc_rw; repeat dsc_mod; litmods; apply act_freed_le2; assumption).
  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End DQ2.
End AXF_dq2z.

Module AXF_dq3.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_G := EVar 32.
Definition e_sc := EVar 33.
Definition e_sp0 := EVar 34.
Definition e_NX := EVar 35.
Definition e_PR := EVar 36.
Definition e_H := EVar 37.
Definition STK := SA e_sp0 (-1024).
Definition ACT := EMd M_MUL (ELit 8) e_sc.
Definition sr_dq3 := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 2 (EAlu ALU_ADD e_sp0 (ELit (-96)))) 9 (ELit 0x95e40)) 10 (e_G)) 12 (e_sc)) 18 (ELit 0x95ed8)).
Definition kn_dq3 : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KWr STK (ELit 1024);
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange e_sc 0 47;
    KRange ACT 0 376;
    KRange e_NX 1 (2^63-1);
    KRange e_PR 1 (2^63-1);
    KWord (SA e_G 8) 8 e_NX;
    KWord (SA e_G 0) 8 e_PR;
    KWord (SA ACT 614184) 8 e_H;
    KWr (SA e_G 0) (ELit 16);
    KWr (SA e_PR 8) (ELit 8);
    KWr (SA e_NX 0) (ELit 8);
    KDisj STK (ELit 1024) (SA e_G 0) (ELit 40);
    KDisj STK (ELit 1024) (SA ACT 614184) (ELit 8);
    KDisj STK (ELit 1024) (SA e_PR 8) (ELit 8);
    KDisj STK (ELit 1024) (SA e_NX 0) (ELit 8);
    KDisj (SA e_G 0) (ELit 40) (SA ACT 614184) (ELit 8);
    KDisj (SA e_G 0) (ELit 40) (SA e_PR 8) (ELit 8);
    KDisj (SA e_G 0) (ELit 40) (SA e_NX 0) (ELit 8);
    KDisj (SA ACT 614184) (ELit 8) (SA e_PR 8) (ELit 8);
    KDisj (SA ACT 614184) (ELit 8) (SA e_NX 0) (ELit 8) ].
Definition scr_dq3 : scripts := SCR [] [] [].
Definition ss_dq3 := SS 0x519e4 sr_dq3 [] kn_dq3 38.
Definition RUN_dq3 := sym_exec SEGS 100 true [0x51af8] scr_dq3 ss_dq3 [].

Definition scr_pdq3 : scripts := SCR [false; true; true] [] [].
Definition RES_pdq3 := Eval vm_compute in sym_exec SEGS 100 true [0x51af8] scr_pdq3 ss_dq3 [].
Lemma RES_pdq3_ok : sym_exec SEGS 100 true [0x51af8] scr_pdq3 (SS 0x519e4 sr_dq3 [] kn_dq3 38) [] = RES_pdq3.
Proof. vm_compute. reflexivity. Qed.
End AXF_dq3.

Module AXF_dq3z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section DQ3.
Context {fx : FPState}.

Definition VALS_dq3 (G sc sp0 NX PR H : Z) : list Z := [G; sc; sp0; NX; PR; H].

Record dq3_pre (regs : bvmap 5 word) (m : word -> option byte) (G sc sp0 NX PR H : Z) : Prop := {
  dq3_R2 : getr regs 2 = wa (sp0 + -96) ;
  dq3_R9 : getr regs 9 = wa 613952 ;
  dq3_R10 : getr regs 10 = wa G ;
  dq3_R12 : getr regs 12 = wa sc ;
  dq3_R18 : getr regs 18 = wa 614104 ;
  dq3_HSTK : stk_ok SEGS m (wa sp0) 1024 ;
  dq3_rng_G : 1 <= G <= 2^63-1 ;
  dq3_rng_sc : 0 <= sc <= 47 ;
  dq3_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  dq3_rng_NX : 1 <= NX <= 2^63-1 ;
  dq3_rng_PR : 1 <= PR <= 2^63-1 ;
  dq3_rng_H : 0 <= H <= 2^64-1 ;
  dq3_ka1 : sp0 mod 16 = 0 ;
  dq3_ka4 : G mod 8 = 0 ;
  dq3_kr6 : 0 <= 8 * sc <= 376 ;
  dq3_kw9 : rdn SEGS m (wa (G + 8)) 8 = Some (word_to_le_bytes 8 (wa NX)) ;
  dq3_kw10 : rdn SEGS m (wa (G + 0)) 8 = Some (word_to_le_bytes 8 (wa PR)) ;
  dq3_kw11 : rdn SEGS m (wa (8 * sc + 614184)) 8 = Some (word_to_le_bytes 8 (wa H)) ;
  dq3_kwr12 : forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS m (wa (G + 0 + d)) k = true ;
  dq3_kwr13 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (PR + 8 + d)) k = true ;
  dq3_kwr14 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (NX + 0 + d)) k = true ;
  dq3_kd15 : sp0 + -1024 + 1024 <= G + 0 \/ G + 0 + 40 <= sp0 + -1024 ;
  dq3_kd16 : sp0 + -1024 + 1024 <= 8 * sc + 614184 \/ 8 * sc + 614184 + 8 <= sp0 + -1024 ;
  dq3_kd17 : sp0 + -1024 + 1024 <= PR + 8 \/ PR + 8 + 8 <= sp0 + -1024 ;
  dq3_kd18 : sp0 + -1024 + 1024 <= NX + 0 \/ NX + 0 + 8 <= sp0 + -1024 ;
  dq3_kd19 : G + 0 + 40 <= 8 * sc + 614184 \/ 8 * sc + 614184 + 8 <= G + 0 ;
  dq3_kd20 : G + 0 + 40 <= PR + 8 \/ PR + 8 + 8 <= G + 0 ;
  dq3_kd21 : G + 0 + 40 <= NX + 0 \/ NX + 0 + 8 <= G + 0 ;
  dq3_kd22 : 8 * sc + 614184 + 8 <= PR + 8 \/ PR + 8 + 8 <= 8 * sc + 614184 ;
  dq3_kd23 : 8 * sc + 614184 + 8 <= NX + 0 \/ NX + 0 + 8 <= 8 * sc + 614184
}.


#[using="Type"] Lemma dq3_setup : forall regs m G sc sp0 NX PR H, dq3_pre regs m G sc sp0 NX PR H ->
  regs_ok (Ez regs (VALS_dq3 G sc sp0 NX PR H)) AXF_dq3.sr_dq3 regs /\ know_ok SEGS (Ez regs (VALS_dq3 G sc sp0 NX PR H)) m AXF_dq3.kn_dq3.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G sc sp0 NX PR H P. destruct P as [dq3_R2 dq3_R9 dq3_R10 dq3_R12 dq3_R18 dq3_HSTK dq3_rng_G dq3_rng_sc dq3_rng_sp0 dq3_rng_NX dq3_rng_PR dq3_rng_H dq3_ka1 dq3_ka4 dq3_kr6 dq3_kw9 dq3_kw10 dq3_kw11 dq3_kwr12 dq3_kwr13 dq3_kwr14 dq3_kd15 dq3_kd16 dq3_kd17 dq3_kd18 dq3_kd19 dq3_kd20 dq3_kd21 dq3_kd22 dq3_kd23].
  set (E := Ez regs (VALS_dq3 G sc sp0 NX PR H)).
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = NX) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = PR) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = H) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_dq3.sr_dq3.
    apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 2); [apply regs_ok_id|]|]|]|]|].
    - rewrite dq3_R2, zeval_sound. cbn [zeval edenot AXF_dq3.e_G AXF_dq3.e_sc AXF_dq3.e_sp0 AXF_dq3.e_NX AXF_dq3.e_PR AXF_dq3.e_H AXF_dq3.STK AXF_dq3.ACT]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite dq3_R9. reflexivity.
    - rewrite dq3_R10. reflexivity.
    - rewrite dq3_R12. reflexivity.
    - rewrite dq3_R18. reflexivity. }
  unfold know_ok, AXF_dq3.kn_dq3.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_dq3.e_sp0 (wa sp0) 1024); [reflexivity | assumption | rewrite u_wa_small by lia; lia])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_dq3.e_G AXF_dq3.e_sc AXF_dq3.e_sp0 AXF_dq3.e_NX AXF_dq3.e_PR AXF_dq3.e_H AXF_dq3.STK AXF_dq3.ACT a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range G _ _ dq3_rng_G eq_refl eq_refl), ?(mod64_of_range sc _ _ dq3_rng_sc eq_refl eq_refl), ?(mod64_of_range sp0 _ _ dq3_rng_sp0 eq_refl eq_refl), ?(mod64_of_range NX _ _ dq3_rng_NX eq_refl eq_refl), ?(mod64_of_range PR _ _ dq3_rng_PR eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply dq3_kwr12 | apply dq3_kwr13 | apply dq3_kwr14]; assumption).
  all: try (clear - dq3_rng_G dq3_rng_sc dq3_rng_sp0 dq3_rng_NX dq3_rng_PR dq3_rng_H dq3_ka1 dq3_ka4 dq3_kr6; lia).
  all: first [(clear - dq3_rng_G dq3_rng_sc dq3_rng_sp0 dq3_rng_NX dq3_rng_PR dq3_rng_H dq3_ka1 dq3_ka4 dq3_kr6 dq3_kd15; lia) | (clear - dq3_rng_G dq3_rng_sc dq3_rng_sp0 dq3_rng_NX dq3_rng_PR dq3_rng_H dq3_ka1 dq3_ka4 dq3_kr6 dq3_kd16; lia) | (clear - dq3_rng_G dq3_rng_sc dq3_rng_sp0 dq3_rng_NX dq3_rng_PR dq3_rng_H dq3_ka1 dq3_ka4 dq3_kr6 dq3_kd17; lia) | (clear - dq3_rng_G dq3_rng_sc dq3_rng_sp0 dq3_rng_NX dq3_rng_PR dq3_rng_H dq3_ka1 dq3_ka4 dq3_kr6 dq3_kd18; lia) | (clear - dq3_rng_G dq3_rng_sc dq3_rng_sp0 dq3_rng_NX dq3_rng_PR dq3_rng_H dq3_ka1 dq3_ka4 dq3_kr6 dq3_kd19; lia) | (clear - dq3_rng_G dq3_rng_sc dq3_rng_sp0 dq3_rng_NX dq3_rng_PR dq3_rng_H dq3_ka1 dq3_ka4 dq3_kr6 dq3_kd20; lia) | (clear - dq3_rng_G dq3_rng_sc dq3_rng_sp0 dq3_rng_NX dq3_rng_PR dq3_rng_H dq3_ka1 dq3_ka4 dq3_kr6 dq3_kd21; lia) | (clear - dq3_rng_G dq3_rng_sc dq3_rng_sp0 dq3_rng_NX dq3_rng_PR dq3_rng_H dq3_ka1 dq3_ka4 dq3_kr6 dq3_kd22; lia) | (clear - dq3_rng_G dq3_rng_sc dq3_rng_sp0 dq3_rng_NX dq3_rng_PR dq3_rng_H dq3_ka1 dq3_ka4 dq3_kr6 dq3_kd23; lia) | lia].
Qed.


Definition dq3_mem_pdq3 (m : word -> option byte) (regs : bvmap 5 word) (G sc sp0 NX PR H : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (m) (wa (PR + 8)) (word_to_le_bytes 8 (wa NX))) (wa (NX + 0)) (word_to_le_bytes 8 (wa PR))) (wa (G + 0)) (word_to_le_bytes 8 (wa 0))) (wa (G + 8)) (word_to_le_bytes 8 (wa 0)).

#[using="Type"] Theorem dq3_pdq3 : forall regs m rom G sc sp0 NX PR H, dq3_pre regs m G sc sp0 NX PR H ->
  scs_denot SEGS m (Ez regs (VALS_dq3 G sc sp0 NX PR H)) (snd (fst AXF_dq3.RES_pdq3)) ->
  exists R, msteps SEGS (mkst regs (wa 0x519e4) m rom) (mkst R (wa 0x51af8) (dq3_mem_pdq3 m regs G sc sp0 NX PR H) rom) /\
    getr R 2 = wa (sp0 + -96) /\ getr R 9 = wa 613952 /\ getr R 10 = wa G /\ getr R 11 = wa ((8 * sc) + 614104) /\ getr R 12 = wa H /\ getr R 13 = wa H /\ getr R 14 = wa NX /\ getr R 18 = wa 614104 /\ (forall k, In k [1; 3; 4; 5; 6; 7; 8; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G sc sp0 NX PR H P Hsc. destruct (dq3_setup regs m G sc sp0 NX PR H P) as [HR HK].
  set (E := Ez regs (VALS_dq3 G sc sp0 NX PR H)) in *. destruct P as [dq3_R2 dq3_R9 dq3_R10 dq3_R12 dq3_R18 dq3_HSTK dq3_rng_G dq3_rng_sc dq3_rng_sp0 dq3_rng_NX dq3_rng_PR dq3_rng_H dq3_ka1 dq3_ka4 dq3_kr6 dq3_kw9 dq3_kw10 dq3_kw11 dq3_kwr12 dq3_kwr13 dq3_kwr14 dq3_kd15 dq3_kd16 dq3_kd17 dq3_kd18 dq3_kd19 dq3_kd20 dq3_kd21 dq3_kd22 dq3_kd23].
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = NX) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = PR) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = H) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x51af8] AXF_dq3.scr_pdq3 0x519e4 AXF_dq3.sr_dq3 AXF_dq3.kn_dq3 38 _ _ _ E m rom regs AXF_dq3.RES_pdq3_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_dq3.RES_pdq3 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (dq3_mem_pdq3 m regs G sc sp0 NX PR H) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold dq3_mem_pdq3. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End DQ3.
End AXF_dq3z.

Module AXF_mi0.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_sp1 := EVar 32.
Definition e_auxv := EVar 33.
Definition sr_mi0 := (sr_upd (sr_upd sr_id 2 (e_sp1)) 19 (ELit 614096)).
Definition kn_mi0 : list kentry :=
  [ KRange e_sp1 (2^20) (2^47);
    KAlign e_sp1 16;
    KRange e_auxv 8 (2^47);
    KWord (SA (ELit 0) 614112) 4 (ELit 0);
    KWord (SA (ELit 0) 613992) 8 e_auxv;
    KWr (SA e_sp1 0) (ELit 8);
    KDisj (SA e_sp1 0) (ELit 8) (SA (ELit 0) 613992) (ELit 8) ].
Definition scr_mi0 : scripts := SCR [false] [] [].
Definition ss_mi0 := SS 0x51cdc sr_mi0 [] kn_mi0 34.
Definition RUN_mi0 := sym_exec SEGS 100 true [0x51d2c] scr_mi0 ss_mi0 [].

Definition scr_pmi0 : scripts := SCR [false] [] [].
Definition RES_pmi0 := Eval vm_compute in sym_exec SEGS 100 true [0x51d2c] scr_pmi0 ss_mi0 [].
Lemma RES_pmi0_ok : sym_exec SEGS 100 true [0x51d2c] scr_pmi0 (SS 0x51cdc sr_mi0 [] kn_mi0 34) [] = RES_pmi0.
Proof. vm_compute. reflexivity. Qed.
End AXF_mi0.

Module AXF_mi0z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section MI0.
Context {fx : FPState}.

Definition VALS_mi0 (sp1 auxv : Z) : list Z := [sp1; auxv].

Record mi0_pre (regs : bvmap 5 word) (m : word -> option byte) (sp1 auxv : Z) : Prop := {
  mi0_R2 : getr regs 2 = wa sp1 ;
  mi0_R19 : getr regs 19 = wa 614096 ;
  mi0_rng_sp1 : 2^20 <= sp1 <= 2^47 ;
  mi0_rng_auxv : 8 <= auxv <= 2^47 ;
  mi0_ka1 : sp1 mod 16 = 0 ;
  mi0_kw3 : rdn SEGS m (wa (0 + 614112)) 4 = Some (word_to_le_bytes 4 (wa 0)) ;
  mi0_kw4 : rdn SEGS m (wa (0 + 613992)) 8 = Some (word_to_le_bytes 8 (wa auxv)) ;
  mi0_kwr5 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (sp1 + 0 + d)) k = true ;
  mi0_kd6 : sp1 + 0 + 8 <= 0 + 613992 \/ 0 + 613992 + 8 <= sp1 + 0
}.


#[using="Type"] Lemma mi0_setup : forall regs m sp1 auxv, mi0_pre regs m sp1 auxv ->
  regs_ok (Ez regs (VALS_mi0 sp1 auxv)) AXF_mi0.sr_mi0 regs /\ know_ok SEGS (Ez regs (VALS_mi0 sp1 auxv)) m AXF_mi0.kn_mi0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sp1 auxv P. destruct P as [mi0_R2 mi0_R19 mi0_rng_sp1 mi0_rng_auxv mi0_ka1 mi0_kw3 mi0_kw4 mi0_kwr5 mi0_kd6].
  set (E := Ez regs (VALS_mi0 sp1 auxv)).
  assert (Z32 : bv_unsigned (ev E 32) = sp1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = auxv) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mi0.sr_mi0.
    apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 2); [apply regs_ok_id|]|].
    - rewrite mi0_R2. reflexivity.
    - rewrite mi0_R19. reflexivity. }
  unfold know_ok, AXF_mi0.kn_mi0.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mi0.e_sp1 AXF_mi0.e_auxv a_base a_off].
  all: rewrite ?Z32, ?Z33.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sp1 _ _ mi0_rng_sp1 eq_refl eq_refl), ?(mod64_of_range auxv _ _ mi0_rng_auxv eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply mi0_kwr5]; assumption).
  all: try (clear - mi0_rng_sp1 mi0_rng_auxv mi0_ka1; lia).
  all: first [(clear - mi0_rng_sp1 mi0_rng_auxv mi0_ka1 mi0_kd6; lia) | lia].
Qed.


Definition mi0_mem_pmi0 (m : word -> option byte) (regs : bvmap 5 word) (sp1 auxv : Z) : word -> option byte :=
  wbytes (m) (wa (sp1 + 0)) (word_to_le_bytes 8 (wa (1103515245 * sp1))).

#[using="Type"] Theorem mi0_pmi0 : forall regs m rom sp1 auxv, mi0_pre regs m sp1 auxv ->
  scs_denot SEGS m (Ez regs (VALS_mi0 sp1 auxv)) (snd (fst AXF_mi0.RES_pmi0)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51cdc) m rom) (mkst R (wa 0x51d2c) (mi0_mem_pmi0 m regs sp1 auxv) rom) /\
    getr R 2 = wa sp1 /\ getr R 8 = wa 613984 /\ getr R 9 = wa 0 /\ getr R 10 = wa auxv /\ getr R 11 = wa (1103515245 * sp1) /\ getr R 12 = wa sp1 /\ getr R 19 = wa 614096 /\ getr R 20 = wa 25 /\ (forall k, In k [1; 3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 18; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sp1 auxv P Hsc. destruct (mi0_setup regs m sp1 auxv P) as [HR HK].
  set (E := Ez regs (VALS_mi0 sp1 auxv)) in *. destruct P as [mi0_R2 mi0_R19 mi0_rng_sp1 mi0_rng_auxv mi0_ka1 mi0_kw3 mi0_kw4 mi0_kwr5 mi0_kd6].
  assert (Z32 : bv_unsigned (ev E 32) = sp1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = auxv) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x51d2c] AXF_mi0.scr_pmi0 0x51cdc AXF_mi0.sr_mi0 AXF_mi0.kn_mi0 34 _ _ _ E m rom regs AXF_mi0.RES_pmi0_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mi0.RES_pmi0 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mi0_mem_pmi0 m regs sp1 auxv) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mi0_mem_pmi0. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MI0.
End AXF_mi0z.

Module AXF_mic2.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_auxv := EVar 32.
Definition e_off := EVar 33.
Definition sr_mic2 := (sr_upd (sr_upd sr_id 8 (ELit 613984)) 9 (e_off)).
Definition kn_mic2 : list kentry :=
  [ KRange e_auxv 8 (2^47);
    KRange e_off 0 (2^47);
    KWord (SA (ELit 0) 613992) 8 e_auxv ].
Definition scr_mic2 : scripts := SCR [] [] [].
Definition ss_mic2 := SS 0x51d24 sr_mic2 [] kn_mic2 34.
Definition RUN_mic2 := sym_exec SEGS 100 true [0x51d2c] scr_mic2 ss_mic2 [].

Definition scr_pmic : scripts := SCR [] [] [].
Definition RES_pmic := Eval vm_compute in sym_exec SEGS 100 true [0x51d2c] scr_pmic ss_mic2 [].
Lemma RES_pmic_ok : sym_exec SEGS 100 true [0x51d2c] scr_pmic (SS 0x51d24 sr_mic2 [] kn_mic2 34) [] = RES_pmic.
Proof. vm_compute. reflexivity. Qed.
End AXF_mic2.

Module AXF_mic2z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section MIC2.
Context {fx : FPState}.

Definition VALS_mic2 (auxv off : Z) : list Z := [auxv; off].

Record mic2_pre (regs : bvmap 5 word) (m : word -> option byte) (auxv off : Z) : Prop := {
  mic2_R8 : getr regs 8 = wa 613984 ;
  mic2_R9 : getr regs 9 = wa off ;
  mic2_rng_auxv : 8 <= auxv <= 2^47 ;
  mic2_rng_off : 0 <= off <= 2^47 ;
  mic2_kw2 : rdn SEGS m (wa (0 + 613992)) 8 = Some (word_to_le_bytes 8 (wa auxv))
}.


#[using="Type"] Lemma mic2_setup : forall regs m auxv off, mic2_pre regs m auxv off ->
  regs_ok (Ez regs (VALS_mic2 auxv off)) AXF_mic2.sr_mic2 regs /\ know_ok SEGS (Ez regs (VALS_mic2 auxv off)) m AXF_mic2.kn_mic2.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m auxv off P. destruct P as [mic2_R8 mic2_R9 mic2_rng_auxv mic2_rng_off mic2_kw2].
  set (E := Ez regs (VALS_mic2 auxv off)).
  assert (Z32 : bv_unsigned (ev E 32) = auxv) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = off) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mic2.sr_mic2.
    apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|].
    - rewrite mic2_R8. reflexivity.
    - rewrite mic2_R9. reflexivity. }
  unfold know_ok, AXF_mic2.kn_mic2.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mic2.e_auxv AXF_mic2.e_off a_base a_off].
  all: rewrite ?Z32, ?Z33.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range auxv _ _ mic2_rng_auxv eq_refl eq_refl), ?(mod64_of_range off _ _ mic2_rng_off eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - mic2_rng_auxv mic2_rng_off; lia).
  all: first [lia].
Qed.


Definition mic2_mem_pmic (m : word -> option byte) (regs : bvmap 5 word) (auxv off : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mic2_pmic : forall regs m rom auxv off, mic2_pre regs m auxv off ->
  scs_denot SEGS m (Ez regs (VALS_mic2 auxv off)) (snd (fst AXF_mic2.RES_pmic)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51d24) m rom) (mkst R (wa 0x51d2c) (mic2_mem_pmic m regs auxv off) rom) /\
    getr R 8 = wa 613984 /\ getr R 9 = wa (off + 16) /\ getr R 10 = wa auxv /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom auxv off P Hsc. destruct (mic2_setup regs m auxv off P) as [HR HK].
  set (E := Ez regs (VALS_mic2 auxv off)) in *. destruct P as [mic2_R8 mic2_R9 mic2_rng_auxv mic2_rng_off mic2_kw2].
  assert (Z32 : bv_unsigned (ev E 32) = auxv) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = off) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x51d2c] AXF_mic2.scr_pmic 0x51d24 AXF_mic2.sr_mic2 AXF_mic2.kn_mic2 34 _ _ _ E m rom regs AXF_mic2.RES_pmic_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mic2.RES_pmic fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mic2_mem_pmic m regs auxv off) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mic2_mem_pmic. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MIC2.
End AXF_mic2z.

Module AXF_mil2.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_auxv := EVar 32.
Definition e_off := EVar 33.
Definition e_typ := EVar 34.
Definition sr_mil2 := (sr_upd (sr_upd (sr_upd sr_id 9 (e_off)) 10 (e_auxv)) 20 (ELit 25)).
Definition kn_mil2 : list kentry :=
  [ KRange e_auxv 8 (2^47);
    KAlign e_auxv 8;
    KRange e_off 0 (2^47);
    KAlign e_off 16;
    KRange e_typ 0 (2^64-1);
    KWord (SA (EAlu ALU_ADD e_auxv e_off) 0) 8 e_typ ].
Definition scr_mil2 : scripts := SCR [true] [] [].
Definition ss_mil2 := SS 0x51d2c sr_mil2 [] kn_mil2 35.
Definition RUN_mil2 := sym_exec SEGS 100 true [0x51d10; 0x51d2c; 0x51d3c] scr_mil2 ss_mil2 [].

Definition scr_pmlr : scripts := SCR [true] [] [].
Definition RES_pmlr := Eval vm_compute in sym_exec SEGS 100 true [0x51d10; 0x51d2c; 0x51d3c] scr_pmlr ss_mil2 [].
Lemma RES_pmlr_ok : sym_exec SEGS 100 true [0x51d10; 0x51d2c; 0x51d3c] scr_pmlr (SS 0x51d2c sr_mil2 [] kn_mil2 35) [] = RES_pmlr.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pmlc : scripts := SCR [false; true] [] [].
Definition RES_pmlc := Eval vm_compute in sym_exec SEGS 100 true [0x51d10; 0x51d2c; 0x51d3c] scr_pmlc ss_mil2 [].
Lemma RES_pmlc_ok : sym_exec SEGS 100 true [0x51d10; 0x51d2c; 0x51d3c] scr_pmlc (SS 0x51d2c sr_mil2 [] kn_mil2 35) [] = RES_pmlc.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pmlx : scripts := SCR [false; false] [] [].
Definition RES_pmlx := Eval vm_compute in sym_exec SEGS 100 true [0x51d10; 0x51d2c; 0x51d3c] scr_pmlx ss_mil2 [].
Lemma RES_pmlx_ok : sym_exec SEGS 100 true [0x51d10; 0x51d2c; 0x51d3c] scr_pmlx (SS 0x51d2c sr_mil2 [] kn_mil2 35) [] = RES_pmlx.
Proof. vm_compute. reflexivity. Qed.
End AXF_mil2.

Module AXF_mil2z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section MIL2.
Context {fx : FPState}.

Definition VALS_mil2 (auxv off typ : Z) : list Z := [auxv; off; typ].

Record mil2_pre (regs : bvmap 5 word) (m : word -> option byte) (auxv off typ : Z) : Prop := {
  mil2_R9 : getr regs 9 = wa off ;
  mil2_R10 : getr regs 10 = wa auxv ;
  mil2_R20 : getr regs 20 = wa 25 ;
  mil2_rng_auxv : 8 <= auxv <= 2^47 ;
  mil2_rng_off : 0 <= off <= 2^47 ;
  mil2_rng_typ : 0 <= typ <= 2^64-1 ;
  mil2_ka1 : auxv mod 8 = 0 ;
  mil2_ka3 : off mod 16 = 0 ;
  mil2_kw5 : rdn SEGS m (wa (auxv + off + 0)) 8 = Some (word_to_le_bytes 8 (wa typ))
}.


#[using="Type"] Lemma mil2_setup : forall regs m auxv off typ, mil2_pre regs m auxv off typ ->
  regs_ok (Ez regs (VALS_mil2 auxv off typ)) AXF_mil2.sr_mil2 regs /\ know_ok SEGS (Ez regs (VALS_mil2 auxv off typ)) m AXF_mil2.kn_mil2.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m auxv off typ P. destruct P as [mil2_R9 mil2_R10 mil2_R20 mil2_rng_auxv mil2_rng_off mil2_rng_typ mil2_ka1 mil2_ka3 mil2_kw5].
  set (E := Ez regs (VALS_mil2 auxv off typ)).
  assert (Z32 : bv_unsigned (ev E 32) = auxv) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = off) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = typ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mil2.sr_mil2.
    apply (regs_ok_pin E _ regs 20); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply regs_ok_id|]|]|].
    - rewrite mil2_R9. reflexivity.
    - rewrite mil2_R10. reflexivity.
    - rewrite mil2_R20. reflexivity. }
  unfold know_ok, AXF_mil2.kn_mil2.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mil2.e_auxv AXF_mil2.e_off AXF_mil2.e_typ a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range auxv _ _ mil2_rng_auxv eq_refl eq_refl), ?(mod64_of_range off _ _ mil2_rng_off eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - mil2_rng_auxv mil2_rng_off mil2_rng_typ mil2_ka1 mil2_ka3; lia).
  all: first [lia].
Qed.


Definition mil2_mem_pmlr (m : word -> option byte) (regs : bvmap 5 word) (auxv off typ : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mil2_pmlr : forall regs m rom auxv off typ, mil2_pre regs m auxv off typ ->
  scs_denot SEGS m (Ez regs (VALS_mil2 auxv off typ)) (snd (fst AXF_mil2.RES_pmlr)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51d2c) m rom) (mkst R (wa 0x51d10) (mil2_mem_pmlr m regs auxv off typ) rom) /\
    getr R 9 = wa off /\ getr R 10 = wa auxv /\ getr R 11 = wa typ /\ getr R 12 = wa (auxv + off) /\ getr R 20 = wa 25 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 13; 14; 15; 16; 17; 18; 19; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom auxv off typ P Hsc. destruct (mil2_setup regs m auxv off typ P) as [HR HK].
  set (E := Ez regs (VALS_mil2 auxv off typ)) in *. destruct P as [mil2_R9 mil2_R10 mil2_R20 mil2_rng_auxv mil2_rng_off mil2_rng_typ mil2_ka1 mil2_ka3 mil2_kw5].
  assert (Z32 : bv_unsigned (ev E 32) = auxv) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = off) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = typ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x51d10; 0x51d2c; 0x51d3c] AXF_mil2.scr_pmlr 0x51d2c AXF_mil2.sr_mil2 AXF_mil2.kn_mil2 35 _ _ _ E m rom regs AXF_mil2.RES_pmlr_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mil2.RES_pmlr fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mil2_mem_pmlr m regs auxv off typ) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mil2_mem_pmlr. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition mil2_mem_pmlc (m : word -> option byte) (regs : bvmap 5 word) (auxv off typ : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mil2_pmlc : forall regs m rom auxv off typ, mil2_pre regs m auxv off typ ->
  scs_denot SEGS m (Ez regs (VALS_mil2 auxv off typ)) (snd (fst AXF_mil2.RES_pmlc)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51d2c) m rom) (mkst R (wa 0x51d2c) (mil2_mem_pmlc m regs auxv off typ) rom) /\
    getr R 9 = wa (off + 16) /\ getr R 10 = wa auxv /\ getr R 11 = wa typ /\ getr R 12 = wa (auxv + off) /\ getr R 20 = wa 25 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 13; 14; 15; 16; 17; 18; 19; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom auxv off typ P Hsc. destruct (mil2_setup regs m auxv off typ P) as [HR HK].
  set (E := Ez regs (VALS_mil2 auxv off typ)) in *. destruct P as [mil2_R9 mil2_R10 mil2_R20 mil2_rng_auxv mil2_rng_off mil2_rng_typ mil2_ka1 mil2_ka3 mil2_kw5].
  assert (Z32 : bv_unsigned (ev E 32) = auxv) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = off) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = typ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x51d10; 0x51d2c; 0x51d3c] AXF_mil2.scr_pmlc 0x51d2c AXF_mil2.sr_mil2 AXF_mil2.kn_mil2 35 _ _ _ E m rom regs AXF_mil2.RES_pmlc_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mil2.RES_pmlc fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mil2_mem_pmlc m regs auxv off typ) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mil2_mem_pmlc. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition mil2_mem_pmlx (m : word -> option byte) (regs : bvmap 5 word) (auxv off typ : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mil2_pmlx : forall regs m rom auxv off typ, mil2_pre regs m auxv off typ ->
  scs_denot SEGS m (Ez regs (VALS_mil2 auxv off typ)) (snd (fst AXF_mil2.RES_pmlx)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51d2c) m rom) (mkst R (wa 0x51d3c) (mil2_mem_pmlx m regs auxv off typ) rom) /\
    getr R 9 = wa off /\ getr R 10 = wa auxv /\ getr R 11 = wa typ /\ getr R 12 = wa (auxv + off) /\ getr R 20 = wa 25 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 13; 14; 15; 16; 17; 18; 19; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom auxv off typ P Hsc. destruct (mil2_setup regs m auxv off typ P) as [HR HK].
  set (E := Ez regs (VALS_mil2 auxv off typ)) in *. destruct P as [mil2_R9 mil2_R10 mil2_R20 mil2_rng_auxv mil2_rng_off mil2_rng_typ mil2_ka1 mil2_ka3 mil2_kw5].
  assert (Z32 : bv_unsigned (ev E 32) = auxv) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = off) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = typ) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x51d10; 0x51d2c; 0x51d3c] AXF_mil2.scr_pmlx 0x51d2c AXF_mil2.sr_mil2 AXF_mil2.kn_mil2 35 _ _ _ E m rom regs AXF_mil2.RES_pmlx_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mil2.RES_pmlx fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mil2_mem_pmlx m regs auxv off typ) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mil2_mem_pmlx. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MIL2.
End AXF_mil2z.

Module AXF_mir.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_ent := EVar 32.
Definition e_rnd := EVar 33.
Definition e_sp1 := EVar 34.
Definition sr_mir := (sr_upd (sr_upd sr_id 2 (e_sp1)) 12 (e_ent)).
Definition kn_mir : list kentry :=
  [ KRange e_ent 8 (2^47);
    KAlign e_ent 8;
    KRange e_rnd 8 (2^47);
    KRange e_sp1 (2^20) (2^47);
    KAlign e_sp1 16;
    KWord (SA e_ent 8) 8 e_rnd ].
Definition scr_mir : scripts := SCR [] [] [].
Definition ss_mir := SS 0x51d10 sr_mir [] kn_mir 35.
Definition RUN_mir := sym_exec SEGS 100 true [0x5e2f0] scr_mir ss_mir [].

Definition scr_pmir : scripts := SCR [] [] [].
Definition RES_pmir := Eval vm_compute in sym_exec SEGS 100 true [0x5e2f0] scr_pmir ss_mir [].
Lemma RES_pmir_ok : sym_exec SEGS 100 true [0x5e2f0] scr_pmir (SS 0x51d10 sr_mir [] kn_mir 35) [] = RES_pmir.
Proof. vm_compute. reflexivity. Qed.
End AXF_mir.

Module AXF_mirz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section MIR.
Context {fx : FPState}.

Definition VALS_mir (ent rnd sp1 : Z) : list Z := [ent; rnd; sp1].

Record mir_pre (regs : bvmap 5 word) (m : word -> option byte) (ent rnd sp1 : Z) : Prop := {
  mir_R2 : getr regs 2 = wa sp1 ;
  mir_R12 : getr regs 12 = wa ent ;
  mir_rng_ent : 8 <= ent <= 2^47 ;
  mir_rng_rnd : 8 <= rnd <= 2^47 ;
  mir_rng_sp1 : 2^20 <= sp1 <= 2^47 ;
  mir_ka1 : ent mod 8 = 0 ;
  mir_ka4 : sp1 mod 16 = 0 ;
  mir_kw5 : rdn SEGS m (wa (ent + 8)) 8 = Some (word_to_le_bytes 8 (wa rnd))
}.


#[using="Type"] Lemma mir_setup : forall regs m ent rnd sp1, mir_pre regs m ent rnd sp1 ->
  regs_ok (Ez regs (VALS_mir ent rnd sp1)) AXF_mir.sr_mir regs /\ know_ok SEGS (Ez regs (VALS_mir ent rnd sp1)) m AXF_mir.kn_mir.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m ent rnd sp1 P. destruct P as [mir_R2 mir_R12 mir_rng_ent mir_rng_rnd mir_rng_sp1 mir_ka1 mir_ka4 mir_kw5].
  set (E := Ez regs (VALS_mir ent rnd sp1)).
  assert (Z32 : bv_unsigned (ev E 32) = ent) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = rnd) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sp1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mir.sr_mir.
    apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 2); [apply regs_ok_id|]|].
    - rewrite mir_R2. reflexivity.
    - rewrite mir_R12. reflexivity. }
  unfold know_ok, AXF_mir.kn_mir.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mir.e_ent AXF_mir.e_rnd AXF_mir.e_sp1 a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range ent _ _ mir_rng_ent eq_refl eq_refl), ?(mod64_of_range rnd _ _ mir_rng_rnd eq_refl eq_refl), ?(mod64_of_range sp1 _ _ mir_rng_sp1 eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - mir_rng_ent mir_rng_rnd mir_rng_sp1 mir_ka1 mir_ka4; lia).
  all: first [lia].
Qed.


Definition mir_mem_pmir (m : word -> option byte) (regs : bvmap 5 word) (ent rnd sp1 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mir_pmir : forall regs m rom ent rnd sp1, mir_pre regs m ent rnd sp1 ->
  scs_denot SEGS m (Ez regs (VALS_mir ent rnd sp1)) (snd (fst AXF_mir.RES_pmir)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51d10) m rom) (mkst R (wa 0x5e2f0) (mir_mem_pmir m regs ent rnd sp1) rom) /\
    getr R 1 = wa 335140 /\ getr R 2 = wa sp1 /\ getr R 10 = wa sp1 /\ getr R 11 = wa (rnd + 8) /\ getr R 12 = wa 8 /\ (forall k, In k [3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom ent rnd sp1 P Hsc. destruct (mir_setup regs m ent rnd sp1 P) as [HR HK].
  set (E := Ez regs (VALS_mir ent rnd sp1)) in *. destruct P as [mir_R2 mir_R12 mir_rng_ent mir_rng_rnd mir_rng_sp1 mir_ka1 mir_ka4 mir_kw5].
  assert (Z32 : bv_unsigned (ev E 32) = ent) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = rnd) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sp1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x5e2f0] AXF_mir.scr_pmir 0x51d10 AXF_mir.sr_mir AXF_mir.kn_mir 35 _ _ _ E m rom regs AXF_mir.RES_pmir_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mir.RES_pmir fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mir_mem_pmir m regs ent rnd sp1) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mir_mem_pmir. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MIR.
End AXF_mirz.

Module AXF_mix.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_sp1 := EVar 32.
Definition e_sec := EVar 33.
Definition sr_mix := (sr_upd (sr_upd (sr_upd sr_id 2 (e_sp1)) 8 (ELit 613984)) 19 (ELit 614096)).
Definition kn_mix : list kentry :=
  [ KRange e_sp1 (2^20) (2^47);
    KAlign e_sp1 16;
    KRange e_sec 0 (2^64-1);
    KWord (SA e_sp1 0) 8 e_sec;
    KWord (SA (ELit 0) 614032) 8 (ELit 4096);
    KWord (SA (ELit 0) 614120) 8 (ELit 0);
    KWr (SA (ELit 0) 614104) (ELit 12);
    KDisj (SA (ELit 0) 614104) (ELit 12) (SA e_sp1 0) (ELit 8) ].
Definition scr_mix : scripts := SCR [] [] [].
Definition ss_mix := SS 0x51d3c sr_mix [] kn_mix 34.
Definition RUN_mix := sym_exec SEGS 100 true [0x51d94] scr_mix ss_mix [].

Definition scr_pmix : scripts := SCR [] [] [].
Definition RES_pmix := Eval vm_compute in sym_exec SEGS 100 true [0x51d94] scr_pmix ss_mix [].
Lemma RES_pmix_ok : sym_exec SEGS 100 true [0x51d94] scr_pmix (SS 0x51d3c sr_mix [] kn_mix 34) [] = RES_pmix.
Proof. vm_compute. reflexivity. Qed.
End AXF_mix.

Module AXF_mixz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section MIX.
Context {fx : FPState}.

Definition VALS_mix (sp1 sec : Z) : list Z := [sp1; sec].

Record mix_pre (regs : bvmap 5 word) (m : word -> option byte) (sp1 sec : Z) : Prop := {
  mix_R2 : getr regs 2 = wa sp1 ;
  mix_R8 : getr regs 8 = wa 613984 ;
  mix_R19 : getr regs 19 = wa 614096 ;
  mix_rng_sp1 : 2^20 <= sp1 <= 2^47 ;
  mix_rng_sec : 0 <= sec <= 2^64-1 ;
  mix_ka1 : sp1 mod 16 = 0 ;
  mix_kw3 : rdn SEGS m (wa (sp1 + 0)) 8 = Some (word_to_le_bytes 8 (wa sec)) ;
  mix_kw4 : rdn SEGS m (wa (0 + 614032)) 8 = Some (word_to_le_bytes 8 (wa 4096)) ;
  mix_kw5 : rdn SEGS m (wa (0 + 614120)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  mix_kwr6 : forall d k, 0 <= d -> d + Z.of_nat k <= 12 -> store_ok SEGS m (wa (0 + 614104 + d)) k = true ;
  mix_kd7 : 0 + 614104 + 12 <= sp1 + 0 \/ sp1 + 0 + 8 <= 0 + 614104
}.


#[using="Type"] Lemma mix_setup : forall regs m sp1 sec, mix_pre regs m sp1 sec ->
  regs_ok (Ez regs (VALS_mix sp1 sec)) AXF_mix.sr_mix regs /\ know_ok SEGS (Ez regs (VALS_mix sp1 sec)) m AXF_mix.kn_mix.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sp1 sec P. destruct P as [mix_R2 mix_R8 mix_R19 mix_rng_sp1 mix_rng_sec mix_ka1 mix_kw3 mix_kw4 mix_kw5 mix_kwr6 mix_kd7].
  set (E := Ez regs (VALS_mix sp1 sec)).
  assert (Z32 : bv_unsigned (ev E 32) = sp1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sec) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mix.sr_mix.
    apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 8); [apply (regs_ok_pin E _ regs 2); [apply regs_ok_id|]|]|].
    - rewrite mix_R2. reflexivity.
    - rewrite mix_R8. reflexivity.
    - rewrite mix_R19. reflexivity. }
  unfold know_ok, AXF_mix.kn_mix.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mix.e_sp1 AXF_mix.e_sec a_base a_off].
  all: rewrite ?Z32, ?Z33.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sp1 _ _ mix_rng_sp1 eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply mix_kwr6]; assumption).
  all: try (clear - mix_rng_sp1 mix_rng_sec mix_ka1; lia).
  all: first [(clear - mix_rng_sp1 mix_rng_sec mix_ka1 mix_kd7; lia) | lia].
Qed.


Definition mix_mem_pmix (m : word -> option byte) (regs : bvmap 5 word) (sp1 sec : Z) : word -> option byte :=
  wbytes (wbytes (m) (wa (0 + 614104)) (word_to_le_bytes 8 (wa sec))) (wa (0 + 614112)) (word_to_le_bytes 4 (wa 1)).

#[using="Type"] Theorem mix_pmix : forall regs m rom sp1 sec, mix_pre regs m sp1 sec ->
  scs_denot SEGS m (Ez regs (VALS_mix sp1 sec)) (snd (fst AXF_mix.RES_pmix)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51d3c) m rom) (mkst R (wa 0x51d94) (mix_mem_pmix m regs sp1 sec) rom) /\
    getr R 2 = wa sp1 /\ getr R 8 = wa 4096 /\ getr R 10 = wa 0 /\ getr R 11 = wa 1 /\ getr R 19 = wa 614096 /\ (forall k, In k [1; 3; 4; 5; 6; 7; 9; 12; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sp1 sec P Hsc. destruct (mix_setup regs m sp1 sec P) as [HR HK].
  set (E := Ez regs (VALS_mix sp1 sec)) in *. destruct P as [mix_R2 mix_R8 mix_R19 mix_rng_sp1 mix_rng_sec mix_ka1 mix_kw3 mix_kw4 mix_kw5 mix_kwr6 mix_kd7].
  assert (Z32 : bv_unsigned (ev E 32) = sp1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sec) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x51d94] AXF_mix.scr_pmix 0x51d3c AXF_mix.sr_mix AXF_mix.kn_mix 34 _ _ _ E m rom regs AXF_mix.RES_pmix_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mix.RES_pmix fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mix_mem_pmix m regs sp1 sec) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mix_mem_pmix. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MIX.
End AXF_mixz.

Module AXF_mmrg.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_sp0 := EVar 32.
Definition e_res := EVar 33.
Definition e_ad := EVar 34.
Definition e_s00 := EVar 35.
Definition e_s10 := EVar 36.
Definition e_s20 := EVar 37.
Definition e_s30 := EVar 38.
Definition e_s40 := EVar 39.
Definition e_s50 := EVar 40.
Definition sr_mmrg := (sr_upd (sr_upd (sr_upd sr_id 2 (EAlu ALU_ADD e_sp0 (ELit (-64)))) 10 (e_res)) 16 (e_ad)).
Definition kn_mmrg : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KRange e_res 4096 (2^47);
    KRange e_ad 0 (2^63-1);
    KWord (SA e_sp0 (-8)) 8 (ELit 335412);
    KWord (SA e_sp0 (-16)) 8 e_s00;
    KWord (SA e_sp0 (-24)) 8 e_s10;
    KWord (SA e_sp0 (-32)) 8 e_s20;
    KWord (SA e_sp0 (-40)) 8 e_s30;
    KWord (SA e_sp0 (-48)) 8 e_s40;
    KWord (SA e_sp0 (-56)) 8 e_s50;
    KRange e_s00 0 (2^64-1);
    KRange e_s10 0 (2^64-1);
    KRange e_s20 0 (2^64-1);
    KRange e_s30 0 (2^64-1);
    KRange e_s40 0 (2^64-1);
    KRange e_s50 0 (2^64-1) ].
Definition scr_mmrg : scripts := SCR [] [] [].
Definition ss_mmrg := SS 0x533f0 sr_mmrg [] kn_mmrg 41.
Definition RUN_mmrg := sym_exec SEGS 100 true [0x51e34] scr_mmrg ss_mmrg [].

Definition scr_pmmrg : scripts := SCR [] [] [].
Definition RES_pmmrg := Eval vm_compute in sym_exec SEGS 100 true [0x51e34] scr_pmmrg ss_mmrg [].
Lemma RES_pmmrg_ok : sym_exec SEGS 100 true [0x51e34] scr_pmmrg (SS 0x533f0 sr_mmrg [] kn_mmrg 41) [] = RES_pmmrg.
Proof. vm_compute. reflexivity. Qed.
End AXF_mmrg.

Module AXF_mmrgz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section MMRG.
Context {fx : FPState}.

Definition VALS_mmrg (sp0 res ad s00 s10 s20 s30 s40 s50 : Z) : list Z := [sp0; res; ad; s00; s10; s20; s30; s40; s50].

Record mmrg_pre (regs : bvmap 5 word) (m : word -> option byte) (sp0 res ad s00 s10 s20 s30 s40 s50 : Z) : Prop := {
  mmrg_R2 : getr regs 2 = wa (sp0 + -64) ;
  mmrg_R10 : getr regs 10 = wa res ;
  mmrg_R16 : getr regs 16 = wa ad ;
  mmrg_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  mmrg_rng_res : 4096 <= res <= 2^47 ;
  mmrg_rng_ad : 0 <= ad <= 2^63-1 ;
  mmrg_rng_s00 : 0 <= s00 <= 2^64-1 ;
  mmrg_rng_s10 : 0 <= s10 <= 2^64-1 ;
  mmrg_rng_s20 : 0 <= s20 <= 2^64-1 ;
  mmrg_rng_s30 : 0 <= s30 <= 2^64-1 ;
  mmrg_rng_s40 : 0 <= s40 <= 2^64-1 ;
  mmrg_rng_s50 : 0 <= s50 <= 2^64-1 ;
  mmrg_ka1 : sp0 mod 16 = 0 ;
  mmrg_kw4 : rdn SEGS m (wa (sp0 + -8)) 8 = Some (word_to_le_bytes 8 (wa 335412)) ;
  mmrg_kw5 : rdn SEGS m (wa (sp0 + -16)) 8 = Some (word_to_le_bytes 8 (wa s00)) ;
  mmrg_kw6 : rdn SEGS m (wa (sp0 + -24)) 8 = Some (word_to_le_bytes 8 (wa s10)) ;
  mmrg_kw7 : rdn SEGS m (wa (sp0 + -32)) 8 = Some (word_to_le_bytes 8 (wa s20)) ;
  mmrg_kw8 : rdn SEGS m (wa (sp0 + -40)) 8 = Some (word_to_le_bytes 8 (wa s30)) ;
  mmrg_kw9 : rdn SEGS m (wa (sp0 + -48)) 8 = Some (word_to_le_bytes 8 (wa s40)) ;
  mmrg_kw10 : rdn SEGS m (wa (sp0 + -56)) 8 = Some (word_to_le_bytes 8 (wa s50))
}.


#[using="Type"] Lemma mmrg_setup : forall regs m sp0 res ad s00 s10 s20 s30 s40 s50, mmrg_pre regs m sp0 res ad s00 s10 s20 s30 s40 s50 ->
  regs_ok (Ez regs (VALS_mmrg sp0 res ad s00 s10 s20 s30 s40 s50)) AXF_mmrg.sr_mmrg regs /\ know_ok SEGS (Ez regs (VALS_mmrg sp0 res ad s00 s10 s20 s30 s40 s50)) m AXF_mmrg.kn_mmrg.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sp0 res ad s00 s10 s20 s30 s40 s50 P. destruct P as [mmrg_R2 mmrg_R10 mmrg_R16 mmrg_rng_sp0 mmrg_rng_res mmrg_rng_ad mmrg_rng_s00 mmrg_rng_s10 mmrg_rng_s20 mmrg_rng_s30 mmrg_rng_s40 mmrg_rng_s50 mmrg_ka1 mmrg_kw4 mmrg_kw5 mmrg_kw6 mmrg_kw7 mmrg_kw8 mmrg_kw9 mmrg_kw10].
  set (E := Ez regs (VALS_mmrg sp0 res ad s00 s10 s20 s30 s40 s50)).
  assert (Z32 : bv_unsigned (ev E 32) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = res) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = ad) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = s00) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = s10) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = s20) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = s30) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = s40) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = s50) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mmrg.sr_mmrg.
    apply (regs_ok_pin E _ regs 16); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 2); [apply regs_ok_id|]|]|].
    - rewrite mmrg_R2, zeval_sound. cbn [zeval edenot AXF_mmrg.e_sp0 AXF_mmrg.e_res AXF_mmrg.e_ad AXF_mmrg.e_s00 AXF_mmrg.e_s10 AXF_mmrg.e_s20 AXF_mmrg.e_s30 AXF_mmrg.e_s40 AXF_mmrg.e_s50]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite mmrg_R10. reflexivity.
    - rewrite mmrg_R16. reflexivity. }
  unfold know_ok, AXF_mmrg.kn_mmrg.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_mmrg.e_sp0 (wa sp0) 1024); [reflexivity | assumption | rewrite u_wa_small by lia; lia])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mmrg.e_sp0 AXF_mmrg.e_res AXF_mmrg.e_ad AXF_mmrg.e_s00 AXF_mmrg.e_s10 AXF_mmrg.e_s20 AXF_mmrg.e_s30 AXF_mmrg.e_s40 AXF_mmrg.e_s50 a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sp0 _ _ mmrg_rng_sp0 eq_refl eq_refl), ?(mod64_of_range res _ _ mmrg_rng_res eq_refl eq_refl), ?(mod64_of_range ad _ _ mmrg_rng_ad eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - mmrg_rng_sp0 mmrg_rng_res mmrg_rng_ad mmrg_rng_s00 mmrg_rng_s10 mmrg_rng_s20 mmrg_rng_s30 mmrg_rng_s40 mmrg_rng_s50 mmrg_ka1; lia).
  all: first [lia].
Qed.


Definition mmrg_mem_pmmrg (m : word -> option byte) (regs : bvmap 5 word) (sp0 res ad s00 s10 s20 s30 s40 s50 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mmrg_pmmrg : forall regs m rom sp0 res ad s00 s10 s20 s30 s40 s50, mmrg_pre regs m sp0 res ad s00 s10 s20 s30 s40 s50 ->
  scs_denot SEGS m (Ez regs (VALS_mmrg sp0 res ad s00 s10 s20 s30 s40 s50)) (snd (fst AXF_mmrg.RES_pmmrg)) ->
  exists R, msteps SEGS (mkst regs (wa 0x533f0) m rom) (mkst R (wa 0x51e34) (mmrg_mem_pmmrg m regs sp0 res ad s00 s10 s20 s30 s40 s50) rom) /\
    getr R 1 = wa 335412 /\ getr R 2 = wa sp0 /\ getr R 8 = wa s00 /\ getr R 9 = wa s10 /\ getr R 10 = wa res /\ getr R 11 = wa 18446744073709547521 /\ getr R 16 = wa ad /\ getr R 18 = wa s20 /\ getr R 19 = wa s30 /\ getr R 20 = wa s40 /\ getr R 21 = wa s50 /\ (forall k, In k [3; 4; 5; 6; 7; 12; 13; 14; 15; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sp0 res ad s00 s10 s20 s30 s40 s50 P Hsc. destruct (mmrg_setup regs m sp0 res ad s00 s10 s20 s30 s40 s50 P) as [HR HK].
  set (E := Ez regs (VALS_mmrg sp0 res ad s00 s10 s20 s30 s40 s50)) in *. destruct P as [mmrg_R2 mmrg_R10 mmrg_R16 mmrg_rng_sp0 mmrg_rng_res mmrg_rng_ad mmrg_rng_s00 mmrg_rng_s10 mmrg_rng_s20 mmrg_rng_s30 mmrg_rng_s40 mmrg_rng_s50 mmrg_ka1 mmrg_kw4 mmrg_kw5 mmrg_kw6 mmrg_kw7 mmrg_kw8 mmrg_kw9 mmrg_kw10].
  assert (Z32 : bv_unsigned (ev E 32) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = res) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = ad) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = s00) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = s10) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = s20) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = s30) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = s40) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = s50) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x51e34] AXF_mmrg.scr_pmmrg 0x533f0 AXF_mmrg.sr_mmrg AXF_mmrg.kn_mmrg 41 _ _ _ E m rom regs AXF_mmrg.RES_pmmrg_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mmrg.RES_pmmrg fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mmrg_mem_pmmrg m regs sp0 res ad s00 s10 s20 s30 s40 s50) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mmrg_mem_pmmrg. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MMRG.
End AXF_mmrgz.

Module AXF_mmrr.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_sp0 := EVar 32.
Definition e_res := EVar 33.
Definition e_ad := EVar 34.
Definition e_s00 := EVar 35.
Definition e_s10 := EVar 36.
Definition e_s20 := EVar 37.
Definition e_s30 := EVar 38.
Definition e_s40 := EVar 39.
Definition e_s50 := EVar 40.
Definition sr_mmrr := (sr_upd (sr_upd (sr_upd sr_id 2 (EAlu ALU_ADD e_sp0 (ELit (-64)))) 10 (e_res)) 16 (e_ad)).
Definition kn_mmrr : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KRange e_res 4096 (2^47);
    KRange e_ad 0 (2^63-1);
    KWord (SA e_sp0 (-8)) 8 (ELit 335500);
    KWord (SA e_sp0 (-16)) 8 e_s00;
    KWord (SA e_sp0 (-24)) 8 e_s10;
    KWord (SA e_sp0 (-32)) 8 e_s20;
    KWord (SA e_sp0 (-40)) 8 e_s30;
    KWord (SA e_sp0 (-48)) 8 e_s40;
    KWord (SA e_sp0 (-56)) 8 e_s50;
    KRange e_s00 0 (2^64-1);
    KRange e_s10 0 (2^64-1);
    KRange e_s20 0 (2^64-1);
    KRange e_s30 0 (2^64-1);
    KRange e_s40 0 (2^64-1);
    KRange e_s50 0 (2^64-1) ].
Definition scr_mmrr : scripts := SCR [] [] [].
Definition ss_mmrr := SS 0x533f0 sr_mmrr [] kn_mmrr 41.
Definition RUN_mmrr := sym_exec SEGS 100 true [0x51e8c] scr_mmrr ss_mmrr [].

Definition scr_pmmrr : scripts := SCR [] [] [].
Definition RES_pmmrr := Eval vm_compute in sym_exec SEGS 100 true [0x51e8c] scr_pmmrr ss_mmrr [].
Lemma RES_pmmrr_ok : sym_exec SEGS 100 true [0x51e8c] scr_pmmrr (SS 0x533f0 sr_mmrr [] kn_mmrr 41) [] = RES_pmmrr.
Proof. vm_compute. reflexivity. Qed.
End AXF_mmrr.

Module AXF_mmrrz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section MMRR.
Context {fx : FPState}.

Definition VALS_mmrr (sp0 res ad s00 s10 s20 s30 s40 s50 : Z) : list Z := [sp0; res; ad; s00; s10; s20; s30; s40; s50].

Record mmrr_pre (regs : bvmap 5 word) (m : word -> option byte) (sp0 res ad s00 s10 s20 s30 s40 s50 : Z) : Prop := {
  mmrr_R2 : getr regs 2 = wa (sp0 + -64) ;
  mmrr_R10 : getr regs 10 = wa res ;
  mmrr_R16 : getr regs 16 = wa ad ;
  mmrr_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  mmrr_rng_res : 4096 <= res <= 2^47 ;
  mmrr_rng_ad : 0 <= ad <= 2^63-1 ;
  mmrr_rng_s00 : 0 <= s00 <= 2^64-1 ;
  mmrr_rng_s10 : 0 <= s10 <= 2^64-1 ;
  mmrr_rng_s20 : 0 <= s20 <= 2^64-1 ;
  mmrr_rng_s30 : 0 <= s30 <= 2^64-1 ;
  mmrr_rng_s40 : 0 <= s40 <= 2^64-1 ;
  mmrr_rng_s50 : 0 <= s50 <= 2^64-1 ;
  mmrr_ka1 : sp0 mod 16 = 0 ;
  mmrr_kw4 : rdn SEGS m (wa (sp0 + -8)) 8 = Some (word_to_le_bytes 8 (wa 335500)) ;
  mmrr_kw5 : rdn SEGS m (wa (sp0 + -16)) 8 = Some (word_to_le_bytes 8 (wa s00)) ;
  mmrr_kw6 : rdn SEGS m (wa (sp0 + -24)) 8 = Some (word_to_le_bytes 8 (wa s10)) ;
  mmrr_kw7 : rdn SEGS m (wa (sp0 + -32)) 8 = Some (word_to_le_bytes 8 (wa s20)) ;
  mmrr_kw8 : rdn SEGS m (wa (sp0 + -40)) 8 = Some (word_to_le_bytes 8 (wa s30)) ;
  mmrr_kw9 : rdn SEGS m (wa (sp0 + -48)) 8 = Some (word_to_le_bytes 8 (wa s40)) ;
  mmrr_kw10 : rdn SEGS m (wa (sp0 + -56)) 8 = Some (word_to_le_bytes 8 (wa s50))
}.


#[using="Type"] Lemma mmrr_setup : forall regs m sp0 res ad s00 s10 s20 s30 s40 s50, mmrr_pre regs m sp0 res ad s00 s10 s20 s30 s40 s50 ->
  regs_ok (Ez regs (VALS_mmrr sp0 res ad s00 s10 s20 s30 s40 s50)) AXF_mmrr.sr_mmrr regs /\ know_ok SEGS (Ez regs (VALS_mmrr sp0 res ad s00 s10 s20 s30 s40 s50)) m AXF_mmrr.kn_mmrr.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sp0 res ad s00 s10 s20 s30 s40 s50 P. destruct P as [mmrr_R2 mmrr_R10 mmrr_R16 mmrr_rng_sp0 mmrr_rng_res mmrr_rng_ad mmrr_rng_s00 mmrr_rng_s10 mmrr_rng_s20 mmrr_rng_s30 mmrr_rng_s40 mmrr_rng_s50 mmrr_ka1 mmrr_kw4 mmrr_kw5 mmrr_kw6 mmrr_kw7 mmrr_kw8 mmrr_kw9 mmrr_kw10].
  set (E := Ez regs (VALS_mmrr sp0 res ad s00 s10 s20 s30 s40 s50)).
  assert (Z32 : bv_unsigned (ev E 32) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = res) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = ad) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = s00) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = s10) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = s20) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = s30) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = s40) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = s50) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mmrr.sr_mmrr.
    apply (regs_ok_pin E _ regs 16); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 2); [apply regs_ok_id|]|]|].
    - rewrite mmrr_R2, zeval_sound. cbn [zeval edenot AXF_mmrr.e_sp0 AXF_mmrr.e_res AXF_mmrr.e_ad AXF_mmrr.e_s00 AXF_mmrr.e_s10 AXF_mmrr.e_s20 AXF_mmrr.e_s30 AXF_mmrr.e_s40 AXF_mmrr.e_s50]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite mmrr_R10. reflexivity.
    - rewrite mmrr_R16. reflexivity. }
  unfold know_ok, AXF_mmrr.kn_mmrr.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_mmrr.e_sp0 (wa sp0) 1024); [reflexivity | assumption | rewrite u_wa_small by lia; lia])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mmrr.e_sp0 AXF_mmrr.e_res AXF_mmrr.e_ad AXF_mmrr.e_s00 AXF_mmrr.e_s10 AXF_mmrr.e_s20 AXF_mmrr.e_s30 AXF_mmrr.e_s40 AXF_mmrr.e_s50 a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sp0 _ _ mmrr_rng_sp0 eq_refl eq_refl), ?(mod64_of_range res _ _ mmrr_rng_res eq_refl eq_refl), ?(mod64_of_range ad _ _ mmrr_rng_ad eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - mmrr_rng_sp0 mmrr_rng_res mmrr_rng_ad mmrr_rng_s00 mmrr_rng_s10 mmrr_rng_s20 mmrr_rng_s30 mmrr_rng_s40 mmrr_rng_s50 mmrr_ka1; lia).
  all: first [lia].
Qed.


Definition mmrr_mem_pmmrr (m : word -> option byte) (regs : bvmap 5 word) (sp0 res ad s00 s10 s20 s30 s40 s50 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mmrr_pmmrr : forall regs m rom sp0 res ad s00 s10 s20 s30 s40 s50, mmrr_pre regs m sp0 res ad s00 s10 s20 s30 s40 s50 ->
  scs_denot SEGS m (Ez regs (VALS_mmrr sp0 res ad s00 s10 s20 s30 s40 s50)) (snd (fst AXF_mmrr.RES_pmmrr)) ->
  exists R, msteps SEGS (mkst regs (wa 0x533f0) m rom) (mkst R (wa 0x51e8c) (mmrr_mem_pmmrr m regs sp0 res ad s00 s10 s20 s30 s40 s50) rom) /\
    getr R 1 = wa 335500 /\ getr R 2 = wa sp0 /\ getr R 8 = wa s00 /\ getr R 9 = wa s10 /\ getr R 10 = wa res /\ getr R 11 = wa 18446744073709547521 /\ getr R 16 = wa ad /\ getr R 18 = wa s20 /\ getr R 19 = wa s30 /\ getr R 20 = wa s40 /\ getr R 21 = wa s50 /\ (forall k, In k [3; 4; 5; 6; 7; 12; 13; 14; 15; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sp0 res ad s00 s10 s20 s30 s40 s50 P Hsc. destruct (mmrr_setup regs m sp0 res ad s00 s10 s20 s30 s40 s50 P) as [HR HK].
  set (E := Ez regs (VALS_mmrr sp0 res ad s00 s10 s20 s30 s40 s50)) in *. destruct P as [mmrr_R2 mmrr_R10 mmrr_R16 mmrr_rng_sp0 mmrr_rng_res mmrr_rng_ad mmrr_rng_s00 mmrr_rng_s10 mmrr_rng_s20 mmrr_rng_s30 mmrr_rng_s40 mmrr_rng_s50 mmrr_ka1 mmrr_kw4 mmrr_kw5 mmrr_kw6 mmrr_kw7 mmrr_kw8 mmrr_kw9 mmrr_kw10].
  assert (Z32 : bv_unsigned (ev E 32) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = res) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = ad) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = s00) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = s10) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = s20) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = s30) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = s40) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = s50) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x51e8c] AXF_mmrr.scr_pmmrr 0x533f0 AXF_mmrr.sr_mmrr AXF_mmrr.kn_mmrr 41 _ _ _ E m rom regs AXF_mmrr.RES_pmmrr_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mmrr.RES_pmmrr fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mmrr_mem_pmmrr m regs sp0 res ad s00 s10 s20 s30 s40 s50) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mmrr_mem_pmmrr. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MMRR.
End AXF_mmrrz.

Module AXF_mmwr.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_sp0 := EVar 32.
Definition e_ad := EVar 33.
Definition e_len := EVar 34.
Definition e_prot := EVar 35.
Definition e_flags := EVar 36.
Definition STK := SA e_sp0 (-1024).
Definition sr_mmwr := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 2 (e_sp0)) 10 (e_ad)) 11 (e_len)) 12 (e_prot)) 13 (e_flags)) 14 (ELit 18446744073709551615)) 15 (ELit 0)).
Definition kn_mmwr : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KWr STK (ELit 1024);
    KRange e_ad 0 (2^63-1);
    KRange e_len 0 (2^47);
    KRange e_prot 0 7;
    KRange e_flags 0 255 ].
Definition scr_mmwr : scripts := SCR [false] [] [].
Definition ss_mmwr := SS 0x53328 sr_mmwr [] kn_mmwr 37.
Definition RUN_mmwr := sym_exec SEGS 100 true [0x533ec] scr_mmwr ss_mmwr [].

Definition scr_pnfr : scripts := SCR [false] [] [].
Definition RES_pnfr := Eval vm_compute in sym_exec SEGS 100 true [0x533ec] scr_pnfr ss_mmwr [].
Lemma RES_pnfr_ok : sym_exec SEGS 100 true [0x533ec] scr_pnfr (SS 0x53328 sr_mmwr [] kn_mmwr 37) [] = RES_pnfr.
Proof. vm_compute. reflexivity. Qed.
End AXF_mmwr.

Module AXF_mmwrz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section MMWR.
Context {fx : FPState}.

Definition VALS_mmwr (sp0 ad len prot flags : Z) : list Z := [sp0; ad; len; prot; flags].

Record mmwr_pre (regs : bvmap 5 word) (m : word -> option byte) (sp0 ad len prot flags : Z) : Prop := {
  mmwr_R2 : getr regs 2 = wa sp0 ;
  mmwr_R10 : getr regs 10 = wa ad ;
  mmwr_R11 : getr regs 11 = wa len ;
  mmwr_R12 : getr regs 12 = wa prot ;
  mmwr_R13 : getr regs 13 = wa flags ;
  mmwr_R14 : getr regs 14 = wa 18446744073709551615 ;
  mmwr_R15 : getr regs 15 = wa 0 ;
  mmwr_HSTK : stk_ok SEGS m (wa sp0) 1024 ;
  mmwr_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  mmwr_rng_ad : 0 <= ad <= 2^63-1 ;
  mmwr_rng_len : 0 <= len <= 2^47 ;
  mmwr_rng_prot : 0 <= prot <= 7 ;
  mmwr_rng_flags : 0 <= flags <= 255 ;
  mmwr_ka1 : sp0 mod 16 = 0
}.


#[using="Type"] Lemma mmwr_setup : forall regs m sp0 ad len prot flags, mmwr_pre regs m sp0 ad len prot flags ->
  regs_ok (Ez regs (VALS_mmwr sp0 ad len prot flags)) AXF_mmwr.sr_mmwr regs /\ know_ok SEGS (Ez regs (VALS_mmwr sp0 ad len prot flags)) m AXF_mmwr.kn_mmwr.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sp0 ad len prot flags P. destruct P as [mmwr_R2 mmwr_R10 mmwr_R11 mmwr_R12 mmwr_R13 mmwr_R14 mmwr_R15 mmwr_HSTK mmwr_rng_sp0 mmwr_rng_ad mmwr_rng_len mmwr_rng_prot mmwr_rng_flags mmwr_ka1].
  set (E := Ez regs (VALS_mmwr sp0 ad len prot flags)).
  assert (Z32 : bv_unsigned (ev E 32) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ad) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = len) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = prot) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = flags) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mmwr.sr_mmwr.
    apply (regs_ok_pin E _ regs 15); [apply (regs_ok_pin E _ regs 14); [apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 2); [apply regs_ok_id|]|]|]|]|]|]|].
    - rewrite mmwr_R2. reflexivity.
    - rewrite mmwr_R10. reflexivity.
    - rewrite mmwr_R11. reflexivity.
    - rewrite mmwr_R12. reflexivity.
    - rewrite mmwr_R13. reflexivity.
    - rewrite mmwr_R14. reflexivity.
    - rewrite mmwr_R15. reflexivity. }
  unfold know_ok, AXF_mmwr.kn_mmwr.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_mmwr.e_sp0 (wa sp0) 1024); [reflexivity | assumption | rewrite u_wa_small by lia; lia])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mmwr.e_sp0 AXF_mmwr.e_ad AXF_mmwr.e_len AXF_mmwr.e_prot AXF_mmwr.e_flags AXF_mmwr.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sp0 _ _ mmwr_rng_sp0 eq_refl eq_refl), ?(mod64_of_range ad _ _ mmwr_rng_ad eq_refl eq_refl), ?(mod64_of_range len _ _ mmwr_rng_len eq_refl eq_refl), ?(mod64_of_range prot _ _ mmwr_rng_prot eq_refl eq_refl), ?(mod64_of_range flags _ _ mmwr_rng_flags eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - mmwr_rng_sp0 mmwr_rng_ad mmwr_rng_len mmwr_rng_prot mmwr_rng_flags mmwr_ka1; lia).
  all: first [lia].
Qed.


Definition mmwr_mem_pnfr (m : word -> option byte) (regs : bvmap 5 word) (sp0 ad len prot flags : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (sp0 + -8)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1))))))) (wa (sp0 + -16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))))) (wa (sp0 + -24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))))))) (wa (sp0 + -32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))))))) (wa (sp0 + -40)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))))) (wa (sp0 + -48)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))))) (wa (sp0 + -56)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21)))))).

#[using="Type"] Theorem mmwr_pnfr : forall regs m rom sp0 ad len prot flags, mmwr_pre regs m sp0 ad len prot flags ->
  scs_denot SEGS m (Ez regs (VALS_mmwr sp0 ad len prot flags)) (snd (fst AXF_mmwr.RES_pnfr)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53328) m rom) (mkst R (wa 0x533ec) (mmwr_mem_pnfr m regs sp0 ad len prot flags) rom) /\
    getr R 2 = wa (sp0 + -64) /\ getr R 5 = wa 18446744073709551604 /\ getr R 10 = wa ad /\ getr R 11 = wa len /\ getr R 12 = wa prot /\ getr R 13 = wa flags /\ getr R 14 = wa 18446744073709551615 /\ getr R 15 = wa 0 /\ getr R 16 = wa ad /\ getr R 17 = wa 222 /\ (forall k, In k [1; 3; 4; 6; 7; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sp0 ad len prot flags P Hsc. destruct (mmwr_setup regs m sp0 ad len prot flags P) as [HR HK].
  set (E := Ez regs (VALS_mmwr sp0 ad len prot flags)) in *. destruct P as [mmwr_R2 mmwr_R10 mmwr_R11 mmwr_R12 mmwr_R13 mmwr_R14 mmwr_R15 mmwr_HSTK mmwr_rng_sp0 mmwr_rng_ad mmwr_rng_len mmwr_rng_prot mmwr_rng_flags mmwr_ka1].
  assert (Z32 : bv_unsigned (ev E 32) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ad) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = len) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = prot) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = flags) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x533ec] AXF_mmwr.scr_pnfr 0x53328 AXF_mmwr.sr_mmwr AXF_mmwr.kn_mmwr 37 _ _ _ E m rom regs AXF_mmwr.RES_pnfr_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mmwr.RES_pnfr fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mmwr_mem_pnfr m regs sp0 ad len prot flags) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mmwr_mem_pnfr. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MMWR.
End AXF_mmwrz.

Module AXF_mpr.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_sp0 := EVar 32.
Definition sr_mpr := (sr_upd (sr_upd sr_id 2 (EAlu ALU_ADD e_sp0 (ELit (-16)))) 10 (ELit 0)).
Definition kn_mpr : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KWord (SA e_sp0 (-8)) 8 (ELit 335712) ].
Definition scr_mpr : scripts := SCR [] [] [].
Definition ss_mpr := SS 0x53448 sr_mpr [] kn_mpr 33.
Definition RUN_mpr := sym_exec SEGS 100 true [0x51f60] scr_mpr ss_mpr [].

Definition scr_pmpr : scripts := SCR [] [] [].
Definition RES_pmpr := Eval vm_compute in sym_exec SEGS 100 true [0x51f60] scr_pmpr ss_mpr [].
Lemma RES_pmpr_ok : sym_exec SEGS 100 true [0x51f60] scr_pmpr (SS 0x53448 sr_mpr [] kn_mpr 33) [] = RES_pmpr.
Proof. vm_compute. reflexivity. Qed.
End AXF_mpr.

Module AXF_mprz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section MPR.
Context {fx : FPState}.

Definition VALS_mpr (sp0 : Z) : list Z := [sp0].

Record mpr_pre (regs : bvmap 5 word) (m : word -> option byte) (sp0 : Z) : Prop := {
  mpr_R2 : getr regs 2 = wa (sp0 + -16) ;
  mpr_R10 : getr regs 10 = wa 0 ;
  mpr_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  mpr_ka1 : sp0 mod 16 = 0 ;
  mpr_kw2 : rdn SEGS m (wa (sp0 + -8)) 8 = Some (word_to_le_bytes 8 (wa 335712))
}.


#[using="Type"] Lemma mpr_setup : forall regs m sp0, mpr_pre regs m sp0 ->
  regs_ok (Ez regs (VALS_mpr sp0)) AXF_mpr.sr_mpr regs /\ know_ok SEGS (Ez regs (VALS_mpr sp0)) m AXF_mpr.kn_mpr.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sp0 P. destruct P as [mpr_R2 mpr_R10 mpr_rng_sp0 mpr_ka1 mpr_kw2].
  set (E := Ez regs (VALS_mpr sp0)).
  assert (Z32 : bv_unsigned (ev E 32) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mpr.sr_mpr.
    apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 2); [apply regs_ok_id|]|].
    - rewrite mpr_R2, zeval_sound. cbn [zeval edenot AXF_mpr.e_sp0]. rewrite ?Z32. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite mpr_R10. reflexivity. }
  unfold know_ok, AXF_mpr.kn_mpr.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_mpr.e_sp0 (wa sp0) 1024); [reflexivity | assumption | rewrite u_wa_small by lia; lia])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mpr.e_sp0 a_base a_off].
  all: rewrite ?Z32.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sp0 _ _ mpr_rng_sp0 eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - mpr_rng_sp0 mpr_ka1; lia).
  all: first [lia].
Qed.


Definition mpr_mem_pmpr (m : word -> option byte) (regs : bvmap 5 word) (sp0 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mpr_pmpr : forall regs m rom sp0, mpr_pre regs m sp0 ->
  scs_denot SEGS m (Ez regs (VALS_mpr sp0)) (snd (fst AXF_mpr.RES_pmpr)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53448) m rom) (mkst R (wa 0x51f60) (mpr_mem_pmpr m regs sp0) rom) /\
    getr R 1 = wa 335712 /\ getr R 2 = wa sp0 /\ getr R 10 = wa 0 /\ getr R 11 = wa 18446744073709547521 /\ (forall k, In k [3; 4; 5; 6; 7; 8; 9; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sp0 P Hsc. destruct (mpr_setup regs m sp0 P) as [HR HK].
  set (E := Ez regs (VALS_mpr sp0)) in *. destruct P as [mpr_R2 mpr_R10 mpr_rng_sp0 mpr_ka1 mpr_kw2].
  assert (Z32 : bv_unsigned (ev E 32) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x51f60] AXF_mpr.scr_pmpr 0x53448 AXF_mpr.sr_mpr AXF_mpr.kn_mpr 33 _ _ _ E m rom regs AXF_mpr.RES_pmpr_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mpr.RES_pmpr fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mpr_mem_pmpr m regs sp0) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mpr_mem_pmpr. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MPR.
End AXF_mprz.

Module AXF_mpw.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_sp0 := EVar 32.
Definition e_p := EVar 33.
Definition STK := SA e_sp0 (-1024).
Definition sr_mpw := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 2 (e_sp0)) 10 (e_p)) 11 (ELit 4096)) 12 (ELit 3)).
Definition kn_mpw : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KWr STK (ELit 1024);
    KRange e_p 4096 (2^47);
    KAlign e_p 4096;
    KWord (SA (ELit 0) 614032) 8 (ELit 4096);
    KDisj STK (ELit 1024) (SA (ELit 0) 614032) (ELit 8) ].
Definition scr_mpw : scripts := SCR [] [] [].
Definition ss_mpw := SS 0x53414 sr_mpw [] kn_mpw 34.
Definition RUN_mpw := sym_exec SEGS 100 true [0x53444] scr_mpw ss_mpw [].

Definition scr_pmpw : scripts := SCR [] [] [].
Definition RES_pmpw := Eval vm_compute in sym_exec SEGS 100 true [0x53444] scr_pmpw ss_mpw [].
Lemma RES_pmpw_ok : sym_exec SEGS 100 true [0x53444] scr_pmpw (SS 0x53414 sr_mpw [] kn_mpw 34) [] = RES_pmpw.
Proof. vm_compute. reflexivity. Qed.
End AXF_mpw.

Module AXF_mpwz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section MPW.
Context {fx : FPState}.

Definition VALS_mpw (sp0 p : Z) : list Z := [sp0; p].

Record mpw_pre (regs : bvmap 5 word) (m : word -> option byte) (sp0 p : Z) : Prop := {
  mpw_R2 : getr regs 2 = wa sp0 ;
  mpw_R10 : getr regs 10 = wa p ;
  mpw_R11 : getr regs 11 = wa 4096 ;
  mpw_R12 : getr regs 12 = wa 3 ;
  mpw_HSTK : stk_ok SEGS m (wa sp0) 1024 ;
  mpw_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  mpw_rng_p : 4096 <= p <= 2^47 ;
  mpw_ka1 : sp0 mod 16 = 0 ;
  mpw_ka4 : p mod 4096 = 0 ;
  mpw_kw5 : rdn SEGS m (wa (0 + 614032)) 8 = Some (word_to_le_bytes 8 (wa 4096)) ;
  mpw_kd6 : sp0 + -1024 + 1024 <= 0 + 614032 \/ 0 + 614032 + 8 <= sp0 + -1024
}.


#[using="Type"] Lemma mpw_setup : forall regs m sp0 p, mpw_pre regs m sp0 p ->
  regs_ok (Ez regs (VALS_mpw sp0 p)) AXF_mpw.sr_mpw regs /\ know_ok SEGS (Ez regs (VALS_mpw sp0 p)) m AXF_mpw.kn_mpw.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sp0 p P. destruct P as [mpw_R2 mpw_R10 mpw_R11 mpw_R12 mpw_HSTK mpw_rng_sp0 mpw_rng_p mpw_ka1 mpw_ka4 mpw_kw5 mpw_kd6].
  set (E := Ez regs (VALS_mpw sp0 p)).
  assert (Z32 : bv_unsigned (ev E 32) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = p) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mpw.sr_mpw.
    apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 2); [apply regs_ok_id|]|]|]|].
    - rewrite mpw_R2. reflexivity.
    - rewrite mpw_R10. reflexivity.
    - rewrite mpw_R11. reflexivity.
    - rewrite mpw_R12. reflexivity. }
  unfold know_ok, AXF_mpw.kn_mpw.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_mpw.e_sp0 (wa sp0) 1024); [reflexivity | assumption | rewrite u_wa_small by lia; lia])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mpw.e_sp0 AXF_mpw.e_p AXF_mpw.STK a_base a_off].
  all: rewrite ?Z32, ?Z33.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sp0 _ _ mpw_rng_sp0 eq_refl eq_refl), ?(mod64_of_range p _ _ mpw_rng_p eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - mpw_rng_sp0 mpw_rng_p mpw_ka1 mpw_ka4; lia).
  all: first [(clear - mpw_rng_sp0 mpw_rng_p mpw_ka1 mpw_ka4 mpw_kd6; lia) | lia].
Qed.


Definition mpw_mem_pmpw (m : word -> option byte) (regs : bvmap 5 word) (sp0 p : Z) : word -> option byte :=
  wbytes (m) (wa (sp0 + -8)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1)))))).

#[using="Type"] Theorem mpw_pmpw : forall regs m rom sp0 p, mpw_pre regs m sp0 p ->
  scs_denot SEGS m (Ez regs (VALS_mpw sp0 p)) (snd (fst AXF_mpw.RES_pmpw)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53414) m rom) (mkst R (wa 0x53444) (mpw_mem_pmpw m regs sp0 p) rom) /\
    getr R 2 = wa (sp0 + -16) /\ getr R 10 = wa p /\ getr R 11 = wa 4096 /\ getr R 12 = wa 3 /\ getr R 13 = wa 4096 /\ getr R 14 = wa 18446744073709547520 /\ getr R 17 = wa 226 /\ (forall k, In k [1; 3; 4; 5; 6; 7; 8; 9; 15; 16; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sp0 p P Hsc. destruct (mpw_setup regs m sp0 p P) as [HR HK].
  set (E := Ez regs (VALS_mpw sp0 p)) in *. destruct P as [mpw_R2 mpw_R10 mpw_R11 mpw_R12 mpw_HSTK mpw_rng_sp0 mpw_rng_p mpw_ka1 mpw_ka4 mpw_kw5 mpw_kd6].
  assert (Z32 : bv_unsigned (ev E 32) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = p) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53444] AXF_mpw.scr_pmpw 0x53414 AXF_mpw.sr_mpw AXF_mpw.kn_mpw 34 _ _ _ E m rom regs AXF_mpw.RES_pmpw_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mpw.RES_pmpw fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mpw_mem_pmpw m regs sp0 p) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mpw_mem_pmpw. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MPW.
End AXF_mpwz.

Module AXF_mt0.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_can := EVar 32.
Definition e_sp0 := EVar 33.
Definition STK := SA e_sp0 (-1024).
Definition sr_mt0 := (sr_upd sr_id 2 (e_sp0)).
Definition kn_mt0 : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KWr STK (ELit 1024);
    KWord (SA (ELit 0) 408992) 8 (ELit 613952);
    KWord (SA (ELit 0) 613952) 8 e_can;
    KDisj STK (ELit 1024) (SA (ELit 0) 408992) (ELit 8);
    KDisj STK (ELit 1024) (SA (ELit 0) 613952) (ELit 8) ].
Definition scr_mt0 : scripts := SCR [] [] [].
Definition ss_mt0 := SS 0x51ca8 sr_mt0 [] kn_mt0 34.
Definition RUN_mt0 := sym_exec SEGS 100 true [0x51cdc] scr_mt0 ss_mt0 [].

Definition scr_pmt0 : scripts := SCR [] [] [].
Definition RES_pmt0 := Eval vm_compute in sym_exec SEGS 100 true [0x51cdc] scr_pmt0 ss_mt0 [].
Lemma RES_pmt0_ok : sym_exec SEGS 100 true [0x51cdc] scr_pmt0 (SS 0x51ca8 sr_mt0 [] kn_mt0 34) [] = RES_pmt0.
Proof. vm_compute. reflexivity. Qed.
End AXF_mt0.

Module AXF_mt0z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section MT0.
Context {fx : FPState}.

Definition VALS_mt0 (can sp0 : Z) : list Z := [can; sp0].

Record mt0_pre (regs : bvmap 5 word) (m : word -> option byte) (can sp0 : Z) : Prop := {
  mt0_R2 : getr regs 2 = wa sp0 ;
  mt0_HSTK : stk_ok SEGS m (wa sp0) 1024 ;
  mt0_rng_can : 0 <= can <= 2^64-1 ;
  mt0_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  mt0_ka1 : sp0 mod 16 = 0 ;
  mt0_kw3 : rdn SEGS m (wa (0 + 408992)) 8 = Some (word_to_le_bytes 8 (wa 613952)) ;
  mt0_kw4 : rdn SEGS m (wa (0 + 613952)) 8 = Some (word_to_le_bytes 8 (wa can)) ;
  mt0_kd5 : sp0 + -1024 + 1024 <= 0 + 408992 \/ 0 + 408992 + 8 <= sp0 + -1024 ;
  mt0_kd6 : sp0 + -1024 + 1024 <= 0 + 613952 \/ 0 + 613952 + 8 <= sp0 + -1024
}.


#[using="Type"] Lemma mt0_setup : forall regs m can sp0, mt0_pre regs m can sp0 ->
  regs_ok (Ez regs (VALS_mt0 can sp0)) AXF_mt0.sr_mt0 regs /\ know_ok SEGS (Ez regs (VALS_mt0 can sp0)) m AXF_mt0.kn_mt0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m can sp0 P. destruct P as [mt0_R2 mt0_HSTK mt0_rng_can mt0_rng_sp0 mt0_ka1 mt0_kw3 mt0_kw4 mt0_kd5 mt0_kd6].
  set (E := Ez regs (VALS_mt0 can sp0)).
  assert (Z32 : bv_unsigned (ev E 32) = can) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mt0.sr_mt0.
    apply (regs_ok_pin E _ regs 2); [apply regs_ok_id|].
    - rewrite mt0_R2. reflexivity. }
  unfold know_ok, AXF_mt0.kn_mt0.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_mt0.e_sp0 (wa sp0) 1024); [reflexivity | assumption | rewrite u_wa_small by lia; lia])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mt0.e_can AXF_mt0.e_sp0 AXF_mt0.STK a_base a_off].
  all: rewrite ?Z32, ?Z33.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sp0 _ _ mt0_rng_sp0 eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - mt0_rng_can mt0_rng_sp0 mt0_ka1; lia).
  all: first [(clear - mt0_rng_can mt0_rng_sp0 mt0_ka1 mt0_kd5; lia) | (clear - mt0_rng_can mt0_rng_sp0 mt0_ka1 mt0_kd6; lia) | lia].
Qed.


Definition mt0_mem_pmt0 (m : word -> option byte) (regs : bvmap 5 word) (can sp0 : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (sp0 + -8)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1))))))) (wa (sp0 + -16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))))) (wa (sp0 + -24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))))))) (wa (sp0 + -32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))))))) (wa (sp0 + -40)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))))) (wa (sp0 + -48)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))))) (wa (sp0 + -56)) (word_to_le_bytes 8 (wa can)).

#[using="Type"] Theorem mt0_pmt0 : forall regs m rom can sp0, mt0_pre regs m can sp0 ->
  scs_denot SEGS m (Ez regs (VALS_mt0 can sp0)) (snd (fst AXF_mt0.RES_pmt0)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51ca8) m rom) (mkst R (wa 0x51cdc) (mt0_mem_pmt0 m regs can sp0) rom) /\
    getr R 2 = wa (sp0 + -64) /\ getr R 10 = wa can /\ getr R 11 = wa 613584 /\ getr R 18 = wa 613952 /\ getr R 19 = wa 614096 /\ (forall k, In k [1; 3; 4; 5; 6; 7; 8; 9; 12; 13; 14; 15; 16; 17; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom can sp0 P Hsc. destruct (mt0_setup regs m can sp0 P) as [HR HK].
  set (E := Ez regs (VALS_mt0 can sp0)) in *. destruct P as [mt0_R2 mt0_HSTK mt0_rng_can mt0_rng_sp0 mt0_ka1 mt0_kw3 mt0_kw4 mt0_kd5 mt0_kd6].
  assert (Z32 : bv_unsigned (ev E 32) = can) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x51cdc] AXF_mt0.scr_pmt0 0x51ca8 AXF_mt0.sr_mt0 AXF_mt0.kn_mt0 34 _ _ _ E m rom regs AXF_mt0.RES_pmt0_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mt0.RES_pmt0 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mt0_mem_pmt0 m regs can sp0) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mt0_mem_pmt0. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MT0.
End AXF_mt0z.

Module AXF_mt1.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_d := EVar 32.
Definition sr_mt1 := (sr_upd sr_id 19 (ELit 614096)).
Definition kn_mt1 : list kentry :=
  [ KWord (SA (ELit 0) 614112) 4 (ELit 1);
    KWord (SA (ELit 0) 614032) 8 (ELit 4096);
    KWord (SA (ELit 0) 614120) 8 (ELit 0) ].
Definition scr_mt1 : scripts := SCR [] [] [].
Definition ss_mt1 := SS 0x51cdc sr_mt1 [] kn_mt1 33.
Definition RUN_mt1 := sym_exec SEGS 100 true [0x51d94; 0x51f1c] scr_mt1 ss_mt1 [].

Definition scr_pmt1 : scripts := SCR [] [] [].
Definition RES_pmt1 := Eval vm_compute in sym_exec SEGS 100 true [0x51d94; 0x51f1c] scr_pmt1 ss_mt1 [].
Lemma RES_pmt1_ok : sym_exec SEGS 100 true [0x51d94; 0x51f1c] scr_pmt1 (SS 0x51cdc sr_mt1 [] kn_mt1 33) [] = RES_pmt1.
Proof. vm_compute. reflexivity. Qed.
End AXF_mt1.

Module AXF_mt10.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_p := EVar 32.
Definition e_ac := EVar 33.
Definition e_tl := EVar 34.
Definition e_sec := EVar 35.
Definition sr_mt10 := (sr_upd (sr_upd sr_id 9 (e_p)) 19 (ELit 614096)).
Definition kn_mt10 : list kentry :=
  [ KRange e_p 4096 (2^47);
    KAlign e_p 4096;
    KRange e_ac 1 (2^60);
    KRange e_tl 0 (2^63-1);
    KRange e_sec 0 (2^64-1);
    KWord (SA (ELit 0) 614144) 8 e_ac;
    KWord (SA (ELit 0) 614168) 8 e_tl;
    KWord (SA (ELit 0) 614104) 8 e_sec;
    KWr (SA (ELit 0) 614120) (ELit 64);
    KWr (SA e_p 0) (ELit 24);
    KWr (SA e_tl 8) (ELit 8);
    KDisj (SA (ELit 0) 614120) (ELit 64) (SA e_p 0) (ELit 24);
    KDisj (SA (ELit 0) 614120) (ELit 64) (SA e_tl 8) (ELit 8);
    KDisj (SA e_p 0) (ELit 24) (SA e_tl 8) (ELit 8);
    KDisj (SA (ELit 0) 614104) (ELit 8) (SA e_tl 8) (ELit 8) ].
Definition scr_mt10 : scripts := SCR [false] [] [].
Definition ss_mt10 := SS 0x51ec0 sr_mt10 [] kn_mt10 36.
Definition RUN_mt10 := sym_exec SEGS 100 true [0x51f1c] scr_mt10 ss_mt10 [].

Definition scr_ptl : scripts := SCR [false] [] [].
Definition RES_ptl := Eval vm_compute in sym_exec SEGS 100 true [0x51f1c] scr_ptl ss_mt10 [].
Lemma RES_ptl_ok : sym_exec SEGS 100 true [0x51f1c] scr_ptl (SS 0x51ec0 sr_mt10 [] kn_mt10 36) [] = RES_ptl.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pt0 : scripts := SCR [true] [] [].
Definition RES_pt0 := Eval vm_compute in sym_exec SEGS 100 true [0x51f1c] scr_pt0 ss_mt10 [].
Lemma RES_pt0_ok : sym_exec SEGS 100 true [0x51f1c] scr_pt0 (SS 0x51ec0 sr_mt10 [] kn_mt10 36) [] = RES_pt0.
Proof. vm_compute. reflexivity. Qed.
End AXF_mt10.

Module AXF_mt100.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_p := EVar 32.
Definition e_ac := EVar 33.
Definition e_sec := EVar 34.
Definition sr_mt100 := (sr_upd (sr_upd sr_id 9 (e_p)) 19 (ELit 614096)).
Definition kn_mt100 : list kentry :=
  [ KRange e_p 4096 (2^47);
    KAlign e_p 4096;
    KRange e_ac 1 (2^60);
    KRange e_sec 0 (2^64-1);
    KWord (SA (ELit 0) 614144) 8 e_ac;
    KWord (SA (ELit 0) 614168) 8 (ELit 0);
    KWord (SA (ELit 0) 614104) 8 e_sec;
    KWr (SA (ELit 0) 614120) (ELit 64);
    KWr (SA e_p 0) (ELit 24);
    KDisj (SA (ELit 0) 614120) (ELit 64) (SA e_p 0) (ELit 24) ].
Definition scr_mt100 : scripts := SCR [] [] [].
Definition ss_mt100 := SS 0x51ec0 sr_mt100 [] kn_mt100 35.
Definition RUN_mt100 := sym_exec SEGS 100 true [0x51f1c] scr_mt100 ss_mt100 [].

Definition scr_pt00 : scripts := SCR [true] [] [].
Definition RES_pt00 := Eval vm_compute in sym_exec SEGS 100 true [0x51f1c] scr_pt00 ss_mt100 [].
Lemma RES_pt00_ok : sym_exec SEGS 100 true [0x51f1c] scr_pt00 (SS 0x51ec0 sr_mt100 [] kn_mt100 35) [] = RES_pt00.
Proof. vm_compute. reflexivity. Qed.
End AXF_mt100.

Module AXF_mt100z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section MT100.
Context {fx : FPState}.

Definition VALS_mt100 (p ac sec : Z) : list Z := [p; ac; sec].

Record mt100_pre (regs : bvmap 5 word) (m : word -> option byte) (p ac sec : Z) : Prop := {
  mt100_R9 : getr regs 9 = wa p ;
  mt100_R19 : getr regs 19 = wa 614096 ;
  mt100_rng_p : 4096 <= p <= 2^47 ;
  mt100_rng_ac : 1 <= ac <= 2^60 ;
  mt100_rng_sec : 0 <= sec <= 2^64-1 ;
  mt100_ka1 : p mod 4096 = 0 ;
  mt100_kw4 : rdn SEGS m (wa (0 + 614144)) 8 = Some (word_to_le_bytes 8 (wa ac)) ;
  mt100_kw5 : rdn SEGS m (wa (0 + 614168)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  mt100_kw6 : rdn SEGS m (wa (0 + 614104)) 8 = Some (word_to_le_bytes 8 (wa sec)) ;
  mt100_kwr7 : forall d k, 0 <= d -> d + Z.of_nat k <= 64 -> store_ok SEGS m (wa (0 + 614120 + d)) k = true ;
  mt100_kwr8 : forall d k, 0 <= d -> d + Z.of_nat k <= 24 -> store_ok SEGS m (wa (p + 0 + d)) k = true ;
  mt100_kd9 : 0 + 614120 + 64 <= p + 0 \/ p + 0 + 24 <= 0 + 614120
}.


#[using="Type"] Lemma mt100_setup : forall regs m p ac sec, mt100_pre regs m p ac sec ->
  regs_ok (Ez regs (VALS_mt100 p ac sec)) AXF_mt100.sr_mt100 regs /\ know_ok SEGS (Ez regs (VALS_mt100 p ac sec)) m AXF_mt100.kn_mt100.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m p ac sec P. destruct P as [mt100_R9 mt100_R19 mt100_rng_p mt100_rng_ac mt100_rng_sec mt100_ka1 mt100_kw4 mt100_kw5 mt100_kw6 mt100_kwr7 mt100_kwr8 mt100_kd9].
  set (E := Ez regs (VALS_mt100 p ac sec)).
  assert (Z32 : bv_unsigned (ev E 32) = p) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ac) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sec) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mt100.sr_mt100.
    apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 9); [apply regs_ok_id|]|].
    - rewrite mt100_R9. reflexivity.
    - rewrite mt100_R19. reflexivity. }
  unfold know_ok, AXF_mt100.kn_mt100.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mt100.e_p AXF_mt100.e_ac AXF_mt100.e_sec a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range p _ _ mt100_rng_p eq_refl eq_refl), ?(mod64_of_range ac _ _ mt100_rng_ac eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply mt100_kwr7 | apply mt100_kwr8]; assumption).
  all: try (clear - mt100_rng_p mt100_rng_ac mt100_rng_sec mt100_ka1; lia).
  all: first [(clear - mt100_rng_p mt100_rng_ac mt100_rng_sec mt100_ka1 mt100_kd9; lia) | lia].
Qed.


Definition mt100_mem_pt00 (m : word -> option byte) (regs : bvmap 5 word) (p ac sec : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (0 + 614144)) (word_to_le_bytes 8 (wa (ac + -1)))) (wa (0 + 614176)) (word_to_le_bytes 8 (wa (p + 4096)))) (wa (0 + 614160)) (word_to_le_bytes 8 (wa p))) (wa (0 + 614168)) (word_to_le_bytes 8 (wa p))) (wa (p + 0)) (word_to_le_bytes 8 (wa sec))) (wa (p + 16)) (word_to_le_bytes 4 (wa 101))) (wa (0 + 614128)) (word_to_le_bytes 8 (wa (p + 64)))) (wa (0 + 614136)) (word_to_le_bytes 8 (wa 100)).

#[using="Type"] Theorem mt100_pt00 : forall regs m rom p ac sec, mt100_pre regs m p ac sec ->
  scs_denot SEGS m (Ez regs (VALS_mt100 p ac sec)) (snd (fst AXF_mt100.RES_pt00)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51ec0) m rom) (mkst R (wa 0x51f1c) (mt100_mem_pt00 m regs p ac sec) rom) /\
    getr R 9 = wa p /\ getr R 10 = wa (p + 24) /\ getr R 11 = wa 100 /\ getr R 12 = wa (p + 64) /\ getr R 19 = wa 614096 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom p ac sec P Hsc. destruct (mt100_setup regs m p ac sec P) as [HR HK].
  set (E := Ez regs (VALS_mt100 p ac sec)) in *. destruct P as [mt100_R9 mt100_R19 mt100_rng_p mt100_rng_ac mt100_rng_sec mt100_ka1 mt100_kw4 mt100_kw5 mt100_kw6 mt100_kwr7 mt100_kwr8 mt100_kd9].
  assert (Z32 : bv_unsigned (ev E 32) = p) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ac) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sec) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x51f1c] AXF_mt100.scr_pt00 0x51ec0 AXF_mt100.sr_mt100 AXF_mt100.kn_mt100 35 _ _ _ E m rom regs AXF_mt100.RES_pt00_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mt100.RES_pt00 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mt100_mem_pt00 m regs p ac sec) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mt100_mem_pt00. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MT100.
End AXF_mt100z.

Module AXF_mt10z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section MT10.
Context {fx : FPState}.

Definition VALS_mt10 (p ac tl sec : Z) : list Z := [p; ac; tl; sec].

Record mt10_pre (regs : bvmap 5 word) (m : word -> option byte) (p ac tl sec : Z) : Prop := {
  mt10_R9 : getr regs 9 = wa p ;
  mt10_R19 : getr regs 19 = wa 614096 ;
  mt10_rng_p : 4096 <= p <= 2^47 ;
  mt10_rng_ac : 1 <= ac <= 2^60 ;
  mt10_rng_tl : 0 <= tl <= 2^63-1 ;
  mt10_rng_sec : 0 <= sec <= 2^64-1 ;
  mt10_ka1 : p mod 4096 = 0 ;
  mt10_kw5 : rdn SEGS m (wa (0 + 614144)) 8 = Some (word_to_le_bytes 8 (wa ac)) ;
  mt10_kw6 : rdn SEGS m (wa (0 + 614168)) 8 = Some (word_to_le_bytes 8 (wa tl)) ;
  mt10_kw7 : rdn SEGS m (wa (0 + 614104)) 8 = Some (word_to_le_bytes 8 (wa sec)) ;
  mt10_kwr8 : forall d k, 0 <= d -> d + Z.of_nat k <= 64 -> store_ok SEGS m (wa (0 + 614120 + d)) k = true ;
  mt10_kwr9 : forall d k, 0 <= d -> d + Z.of_nat k <= 24 -> store_ok SEGS m (wa (p + 0 + d)) k = true ;
  mt10_kwr10 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (tl + 8 + d)) k = true ;
  mt10_kd11 : 0 + 614120 + 64 <= p + 0 \/ p + 0 + 24 <= 0 + 614120 ;
  mt10_kd12 : 0 + 614120 + 64 <= tl + 8 \/ tl + 8 + 8 <= 0 + 614120 ;
  mt10_kd13 : p + 0 + 24 <= tl + 8 \/ tl + 8 + 8 <= p + 0 ;
  mt10_kd14 : 0 + 614104 + 8 <= tl + 8 \/ tl + 8 + 8 <= 0 + 614104
}.


#[using="Type"] Lemma mt10_setup : forall regs m p ac tl sec, mt10_pre regs m p ac tl sec ->
  regs_ok (Ez regs (VALS_mt10 p ac tl sec)) AXF_mt10.sr_mt10 regs /\ know_ok SEGS (Ez regs (VALS_mt10 p ac tl sec)) m AXF_mt10.kn_mt10.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m p ac tl sec P. destruct P as [mt10_R9 mt10_R19 mt10_rng_p mt10_rng_ac mt10_rng_tl mt10_rng_sec mt10_ka1 mt10_kw5 mt10_kw6 mt10_kw7 mt10_kwr8 mt10_kwr9 mt10_kwr10 mt10_kd11 mt10_kd12 mt10_kd13 mt10_kd14].
  set (E := Ez regs (VALS_mt10 p ac tl sec)).
  assert (Z32 : bv_unsigned (ev E 32) = p) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ac) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = tl) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = sec) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mt10.sr_mt10.
    apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 9); [apply regs_ok_id|]|].
    - rewrite mt10_R9. reflexivity.
    - rewrite mt10_R19. reflexivity. }
  unfold know_ok, AXF_mt10.kn_mt10.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mt10.e_p AXF_mt10.e_ac AXF_mt10.e_tl AXF_mt10.e_sec a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range p _ _ mt10_rng_p eq_refl eq_refl), ?(mod64_of_range ac _ _ mt10_rng_ac eq_refl eq_refl), ?(mod64_of_range tl _ _ mt10_rng_tl eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply mt10_kwr8 | apply mt10_kwr9 | apply mt10_kwr10]; assumption).
  all: try (clear - mt10_rng_p mt10_rng_ac mt10_rng_tl mt10_rng_sec mt10_ka1; lia).
  all: first [(clear - mt10_rng_p mt10_rng_ac mt10_rng_tl mt10_rng_sec mt10_ka1 mt10_kd11; lia) | (clear - mt10_rng_p mt10_rng_ac mt10_rng_tl mt10_rng_sec mt10_ka1 mt10_kd12; lia) | (clear - mt10_rng_p mt10_rng_ac mt10_rng_tl mt10_rng_sec mt10_ka1 mt10_kd13; lia) | (clear - mt10_rng_p mt10_rng_ac mt10_rng_tl mt10_rng_sec mt10_ka1 mt10_kd14; lia) | lia].
Qed.


Definition mt10_mem_ptl (m : word -> option byte) (regs : bvmap 5 word) (p ac tl sec : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (0 + 614144)) (word_to_le_bytes 8 (wa (ac + -1)))) (wa (0 + 614176)) (word_to_le_bytes 8 (wa (p + 4096)))) (wa (tl + 8)) (word_to_le_bytes 8 (wa p))) (wa (0 + 614168)) (word_to_le_bytes 8 (wa p))) (wa (p + 0)) (word_to_le_bytes 8 (wa sec))) (wa (p + 16)) (word_to_le_bytes 4 (wa 101))) (wa (0 + 614128)) (word_to_le_bytes 8 (wa (p + 64)))) (wa (0 + 614136)) (word_to_le_bytes 8 (wa 100)).

#[using="Type"] Theorem mt10_ptl : forall regs m rom p ac tl sec, mt10_pre regs m p ac tl sec ->
  scs_denot SEGS m (Ez regs (VALS_mt10 p ac tl sec)) (snd (fst AXF_mt10.RES_ptl)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51ec0) m rom) (mkst R (wa 0x51f1c) (mt10_mem_ptl m regs p ac tl sec) rom) /\
    getr R 9 = wa p /\ getr R 10 = wa (p + 24) /\ getr R 11 = wa 100 /\ getr R 12 = wa (p + 64) /\ getr R 19 = wa 614096 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom p ac tl sec P Hsc. destruct (mt10_setup regs m p ac tl sec P) as [HR HK].
  set (E := Ez regs (VALS_mt10 p ac tl sec)) in *. destruct P as [mt10_R9 mt10_R19 mt10_rng_p mt10_rng_ac mt10_rng_tl mt10_rng_sec mt10_ka1 mt10_kw5 mt10_kw6 mt10_kw7 mt10_kwr8 mt10_kwr9 mt10_kwr10 mt10_kd11 mt10_kd12 mt10_kd13 mt10_kd14].
  assert (Z32 : bv_unsigned (ev E 32) = p) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ac) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = tl) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = sec) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x51f1c] AXF_mt10.scr_ptl 0x51ec0 AXF_mt10.sr_mt10 AXF_mt10.kn_mt10 36 _ _ _ E m rom regs AXF_mt10.RES_ptl_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mt10.RES_ptl fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mt10_mem_ptl m regs p ac tl sec) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mt10_mem_ptl. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition mt10_mem_pt0 (m : word -> option byte) (regs : bvmap 5 word) (p ac tl sec : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (0 + 614144)) (word_to_le_bytes 8 (wa (ac + -1)))) (wa (0 + 614176)) (word_to_le_bytes 8 (wa (p + 4096)))) (wa (0 + 614160)) (word_to_le_bytes 8 (wa p))) (wa (0 + 614168)) (word_to_le_bytes 8 (wa p))) (wa (p + 0)) (word_to_le_bytes 8 (wa sec))) (wa (p + 16)) (word_to_le_bytes 4 (wa 101))) (wa (0 + 614128)) (word_to_le_bytes 8 (wa (p + 64)))) (wa (0 + 614136)) (word_to_le_bytes 8 (wa 100)).

#[using="Type"] Theorem mt10_pt0 : forall regs m rom p ac tl sec, mt10_pre regs m p ac tl sec ->
  scs_denot SEGS m (Ez regs (VALS_mt10 p ac tl sec)) (snd (fst AXF_mt10.RES_pt0)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51ec0) m rom) (mkst R (wa 0x51f1c) (mt10_mem_pt0 m regs p ac tl sec) rom) /\
    getr R 9 = wa p /\ getr R 10 = wa (p + 24) /\ getr R 11 = wa 100 /\ getr R 12 = wa (p + 64) /\ getr R 19 = wa 614096 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom p ac tl sec P Hsc. destruct (mt10_setup regs m p ac tl sec P) as [HR HK].
  set (E := Ez regs (VALS_mt10 p ac tl sec)) in *. destruct P as [mt10_R9 mt10_R19 mt10_rng_p mt10_rng_ac mt10_rng_tl mt10_rng_sec mt10_ka1 mt10_kw5 mt10_kw6 mt10_kw7 mt10_kwr8 mt10_kwr9 mt10_kwr10 mt10_kd11 mt10_kd12 mt10_kd13 mt10_kd14].
  assert (Z32 : bv_unsigned (ev E 32) = p) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ac) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = tl) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = sec) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x51f1c] AXF_mt10.scr_pt0 0x51ec0 AXF_mt10.sr_mt10 AXF_mt10.kn_mt10 36 _ _ _ E m rom regs AXF_mt10.RES_pt0_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mt10.RES_pt0 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mt10_mem_pt0 m regs p ac tl sec) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mt10_mem_pt0. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MT10.
End AXF_mt10z.

Module AXF_mt1f.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_fm := EVar 32.
Definition e_nx := EVar 33.
Definition e_pv := EVar 34.
Definition sr_mt1f := (sr_upd sr_id 19 (ELit 614096)).
Definition kn_mt1f : list kentry :=
  [ KRange e_fm 1 (2^63-1);
    KAlign e_fm 8;
    KRange e_nx 1 (2^63-1);
    KRange e_pv 1 (2^63-1);
    KWord (SA (ELit 0) 614112) 4 (ELit 1);
    KWord (SA (ELit 0) 614032) 8 (ELit 4096);
    KWord (SA (ELit 0) 614120) 8 e_fm;
    KWord (SA e_fm 8) 8 e_nx;
    KWord (SA e_fm 0) 8 e_pv;
    KWr (SA (ELit 0) 614120) (ELit 8);
    KWr (SA e_pv 8) (ELit 8);
    KWr (SA e_nx 0) (ELit 8);
    KDisj (SA (ELit 0) 614120) (ELit 8) (SA e_pv 8) (ELit 8);
    KDisj (SA (ELit 0) 614120) (ELit 8) (SA e_nx 0) (ELit 8);
    KDisj (SA e_pv 8) (ELit 8) (SA e_fm 0) (ELit 16);
    KDisj (SA e_nx 0) (ELit 8) (SA e_fm 0) (ELit 16) ].
Definition scr_mt1f : scripts := SCR [true] [] [].
Definition ss_mt1f := SS 0x51cdc sr_mt1f [] kn_mt1f 35.
Definition RUN_mt1f := sym_exec SEGS 100 true [0x51d94; 0x51f1c] scr_mt1f ss_mt1f [].

Definition scr_pmf1 : scripts := SCR [true] [] [].
Definition RES_pmf1 := Eval vm_compute in sym_exec SEGS 100 true [0x51d94; 0x51f1c] scr_pmf1 ss_mt1f [].
Lemma RES_pmf1_ok : sym_exec SEGS 100 true [0x51d94; 0x51f1c] scr_pmf1 (SS 0x51cdc sr_mt1f [] kn_mt1f 35) [] = RES_pmf1.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pmfn : scripts := SCR [false] [] [].
Definition RES_pmfn := Eval vm_compute in sym_exec SEGS 100 true [0x51d94; 0x51f1c] scr_pmfn ss_mt1f [].
Lemma RES_pmfn_ok : sym_exec SEGS 100 true [0x51d94; 0x51f1c] scr_pmfn (SS 0x51cdc sr_mt1f [] kn_mt1f 35) [] = RES_pmfn.
Proof. vm_compute. reflexivity. Qed.
End AXF_mt1f.

Module AXF_mt1f1.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_fm := EVar 32.
Definition sr_mt1f1 := (sr_upd sr_id 19 (ELit 614096)).
Definition kn_mt1f1 : list kentry :=
  [ KRange e_fm 1 (2^63-1);
    KAlign e_fm 8;
    KWord (SA (ELit 0) 614112) 4 (ELit 1);
    KWord (SA (ELit 0) 614032) 8 (ELit 4096);
    KWord (SA (ELit 0) 614120) 8 e_fm;
    KWord (SA e_fm 8) 8 e_fm;
    KWr (SA (ELit 0) 614120) (ELit 8) ].
Definition scr_mt1f1 : scripts := SCR [true] [] [].
Definition ss_mt1f1 := SS 0x51cdc sr_mt1f1 [] kn_mt1f1 33.
Definition RUN_mt1f1 := sym_exec SEGS 100 true [0x51d94; 0x51f1c] scr_mt1f1 ss_mt1f1 [].

Definition scr_pmf1a : scripts := SCR [true] [] [].
Definition RES_pmf1a := Eval vm_compute in sym_exec SEGS 100 true [0x51d94; 0x51f1c] scr_pmf1a ss_mt1f1 [].
Lemma RES_pmf1a_ok : sym_exec SEGS 100 true [0x51d94; 0x51f1c] scr_pmf1a (SS 0x51cdc sr_mt1f1 [] kn_mt1f1 33) [] = RES_pmf1a.
Proof. vm_compute. reflexivity. Qed.
End AXF_mt1f1.

Module AXF_mt1f1z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section MT1F1.
Context {fx : FPState}.

Definition VALS_mt1f1 (fm : Z) : list Z := [fm].

Record mt1f1_pre (regs : bvmap 5 word) (m : word -> option byte) (fm : Z) : Prop := {
  mt1f1_R19 : getr regs 19 = wa 614096 ;
  mt1f1_rng_fm : 1 <= fm <= 2^63-1 ;
  mt1f1_ka1 : fm mod 8 = 0 ;
  mt1f1_kw2 : rdn SEGS m (wa (0 + 614112)) 4 = Some (word_to_le_bytes 4 (wa 1)) ;
  mt1f1_kw3 : rdn SEGS m (wa (0 + 614032)) 8 = Some (word_to_le_bytes 8 (wa 4096)) ;
  mt1f1_kw4 : rdn SEGS m (wa (0 + 614120)) 8 = Some (word_to_le_bytes 8 (wa fm)) ;
  mt1f1_kw5 : rdn SEGS m (wa (fm + 8)) 8 = Some (word_to_le_bytes 8 (wa fm)) ;
  mt1f1_kwr6 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (0 + 614120 + d)) k = true
}.


#[using="Type"] Lemma mt1f1_setup : forall regs m fm, mt1f1_pre regs m fm ->
  regs_ok (Ez regs (VALS_mt1f1 fm)) AXF_mt1f1.sr_mt1f1 regs /\ know_ok SEGS (Ez regs (VALS_mt1f1 fm)) m AXF_mt1f1.kn_mt1f1.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m fm P. destruct P as [mt1f1_R19 mt1f1_rng_fm mt1f1_ka1 mt1f1_kw2 mt1f1_kw3 mt1f1_kw4 mt1f1_kw5 mt1f1_kwr6].
  set (E := Ez regs (VALS_mt1f1 fm)).
  assert (Z32 : bv_unsigned (ev E 32) = fm) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mt1f1.sr_mt1f1.
    apply (regs_ok_pin E _ regs 19); [apply regs_ok_id|].
    - rewrite mt1f1_R19. reflexivity. }
  unfold know_ok, AXF_mt1f1.kn_mt1f1.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mt1f1.e_fm a_base a_off].
  all: rewrite ?Z32.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range fm _ _ mt1f1_rng_fm eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply mt1f1_kwr6]; assumption).
  all: try (clear - mt1f1_rng_fm mt1f1_ka1; lia).
  all: first [lia].
Qed.


Definition mt1f1_mem_pmf1a (m : word -> option byte) (regs : bvmap 5 word) (fm : Z) : word -> option byte :=
  wbytes (m) (wa (0 + 614120)) (word_to_le_bytes 8 (wa 0)).

#[using="Type"] Theorem mt1f1_pmf1a : forall regs m rom fm, mt1f1_pre regs m fm ->
  scs_denot SEGS m (Ez regs (VALS_mt1f1 fm)) (snd (fst AXF_mt1f1.RES_pmf1a)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51cdc) m rom) (mkst R (wa 0x51f1c) (mt1f1_mem_pmf1a m regs fm) rom) /\
    getr R 8 = wa 4096 /\ getr R 10 = wa fm /\ getr R 11 = wa fm /\ getr R 19 = wa 614096 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 9; 12; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom fm P Hsc. destruct (mt1f1_setup regs m fm P) as [HR HK].
  set (E := Ez regs (VALS_mt1f1 fm)) in *. destruct P as [mt1f1_R19 mt1f1_rng_fm mt1f1_ka1 mt1f1_kw2 mt1f1_kw3 mt1f1_kw4 mt1f1_kw5 mt1f1_kwr6].
  assert (Z32 : bv_unsigned (ev E 32) = fm) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x51d94; 0x51f1c] AXF_mt1f1.scr_pmf1a 0x51cdc AXF_mt1f1.sr_mt1f1 AXF_mt1f1.kn_mt1f1 33 _ _ _ E m rom regs AXF_mt1f1.RES_pmf1a_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mt1f1.RES_pmf1a fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mt1f1_mem_pmf1a m regs fm) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mt1f1_mem_pmf1a. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MT1F1.
End AXF_mt1f1z.

Module AXF_mt1fz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section MT1F.
Context {fx : FPState}.

Definition VALS_mt1f (fm nx pv : Z) : list Z := [fm; nx; pv].

Record mt1f_pre (regs : bvmap 5 word) (m : word -> option byte) (fm nx pv : Z) : Prop := {
  mt1f_R19 : getr regs 19 = wa 614096 ;
  mt1f_rng_fm : 1 <= fm <= 2^63-1 ;
  mt1f_rng_nx : 1 <= nx <= 2^63-1 ;
  mt1f_rng_pv : 1 <= pv <= 2^63-1 ;
  mt1f_ka1 : fm mod 8 = 0 ;
  mt1f_kw4 : rdn SEGS m (wa (0 + 614112)) 4 = Some (word_to_le_bytes 4 (wa 1)) ;
  mt1f_kw5 : rdn SEGS m (wa (0 + 614032)) 8 = Some (word_to_le_bytes 8 (wa 4096)) ;
  mt1f_kw6 : rdn SEGS m (wa (0 + 614120)) 8 = Some (word_to_le_bytes 8 (wa fm)) ;
  mt1f_kw7 : rdn SEGS m (wa (fm + 8)) 8 = Some (word_to_le_bytes 8 (wa nx)) ;
  mt1f_kw8 : rdn SEGS m (wa (fm + 0)) 8 = Some (word_to_le_bytes 8 (wa pv)) ;
  mt1f_kwr9 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (0 + 614120 + d)) k = true ;
  mt1f_kwr10 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (pv + 8 + d)) k = true ;
  mt1f_kwr11 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (nx + 0 + d)) k = true ;
  mt1f_kd12 : 0 + 614120 + 8 <= pv + 8 \/ pv + 8 + 8 <= 0 + 614120 ;
  mt1f_kd13 : 0 + 614120 + 8 <= nx + 0 \/ nx + 0 + 8 <= 0 + 614120 ;
  mt1f_kd14 : pv + 8 + 8 <= fm + 0 \/ fm + 0 + 16 <= pv + 8 ;
  mt1f_kd15 : nx + 0 + 8 <= fm + 0 \/ fm + 0 + 16 <= nx + 0
}.


#[using="Type"] Lemma mt1f_setup : forall regs m fm nx pv, mt1f_pre regs m fm nx pv ->
  regs_ok (Ez regs (VALS_mt1f fm nx pv)) AXF_mt1f.sr_mt1f regs /\ know_ok SEGS (Ez regs (VALS_mt1f fm nx pv)) m AXF_mt1f.kn_mt1f.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m fm nx pv P. destruct P as [mt1f_R19 mt1f_rng_fm mt1f_rng_nx mt1f_rng_pv mt1f_ka1 mt1f_kw4 mt1f_kw5 mt1f_kw6 mt1f_kw7 mt1f_kw8 mt1f_kwr9 mt1f_kwr10 mt1f_kwr11 mt1f_kd12 mt1f_kd13 mt1f_kd14 mt1f_kd15].
  set (E := Ez regs (VALS_mt1f fm nx pv)).
  assert (Z32 : bv_unsigned (ev E 32) = fm) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = nx) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = pv) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mt1f.sr_mt1f.
    apply (regs_ok_pin E _ regs 19); [apply regs_ok_id|].
    - rewrite mt1f_R19. reflexivity. }
  unfold know_ok, AXF_mt1f.kn_mt1f.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mt1f.e_fm AXF_mt1f.e_nx AXF_mt1f.e_pv a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range fm _ _ mt1f_rng_fm eq_refl eq_refl), ?(mod64_of_range nx _ _ mt1f_rng_nx eq_refl eq_refl), ?(mod64_of_range pv _ _ mt1f_rng_pv eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply mt1f_kwr9 | apply mt1f_kwr10 | apply mt1f_kwr11]; assumption).
  all: try (clear - mt1f_rng_fm mt1f_rng_nx mt1f_rng_pv mt1f_ka1; lia).
  all: first [(clear - mt1f_rng_fm mt1f_rng_nx mt1f_rng_pv mt1f_ka1 mt1f_kd12; lia) | (clear - mt1f_rng_fm mt1f_rng_nx mt1f_rng_pv mt1f_ka1 mt1f_kd13; lia) | (clear - mt1f_rng_fm mt1f_rng_nx mt1f_rng_pv mt1f_ka1 mt1f_kd14; lia) | (clear - mt1f_rng_fm mt1f_rng_nx mt1f_rng_pv mt1f_ka1 mt1f_kd15; lia) | lia].
Qed.


Definition mt1f_mem_pmf1 (m : word -> option byte) (regs : bvmap 5 word) (fm nx pv : Z) : word -> option byte :=
  wbytes (m) (wa (0 + 614120)) (word_to_le_bytes 8 (wa 0)).

#[using="Type"] Theorem mt1f_pmf1 : forall regs m rom fm nx pv, mt1f_pre regs m fm nx pv ->
  scs_denot SEGS m (Ez regs (VALS_mt1f fm nx pv)) (snd (fst AXF_mt1f.RES_pmf1)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51cdc) m rom) (mkst R (wa 0x51f1c) (mt1f_mem_pmf1 m regs fm nx pv) rom) /\
    getr R 8 = wa 4096 /\ getr R 10 = wa fm /\ getr R 11 = wa nx /\ getr R 19 = wa 614096 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 9; 12; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom fm nx pv P Hsc. destruct (mt1f_setup regs m fm nx pv P) as [HR HK].
  set (E := Ez regs (VALS_mt1f fm nx pv)) in *. destruct P as [mt1f_R19 mt1f_rng_fm mt1f_rng_nx mt1f_rng_pv mt1f_ka1 mt1f_kw4 mt1f_kw5 mt1f_kw6 mt1f_kw7 mt1f_kw8 mt1f_kwr9 mt1f_kwr10 mt1f_kwr11 mt1f_kd12 mt1f_kd13 mt1f_kd14 mt1f_kd15].
  assert (Z32 : bv_unsigned (ev E 32) = fm) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = nx) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = pv) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x51d94; 0x51f1c] AXF_mt1f.scr_pmf1 0x51cdc AXF_mt1f.sr_mt1f AXF_mt1f.kn_mt1f 35 _ _ _ E m rom regs AXF_mt1f.RES_pmf1_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mt1f.RES_pmf1 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mt1f_mem_pmf1 m regs fm nx pv) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mt1f_mem_pmf1. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition mt1f_mem_pmfn (m : word -> option byte) (regs : bvmap 5 word) (fm nx pv : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (m) (wa (pv + 8)) (word_to_le_bytes 8 (wa nx))) (wa (nx + 0)) (word_to_le_bytes 8 (wa pv))) (wa (0 + 614120)) (word_to_le_bytes 8 (wa nx)).

#[using="Type"] Theorem mt1f_pmfn : forall regs m rom fm nx pv, mt1f_pre regs m fm nx pv ->
  scs_denot SEGS m (Ez regs (VALS_mt1f fm nx pv)) (snd (fst AXF_mt1f.RES_pmfn)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51cdc) m rom) (mkst R (wa 0x51f1c) (mt1f_mem_pmfn m regs fm nx pv) rom) /\
    getr R 8 = wa 4096 /\ getr R 10 = wa fm /\ getr R 11 = wa nx /\ getr R 12 = wa nx /\ getr R 19 = wa 614096 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 9; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom fm nx pv P Hsc. destruct (mt1f_setup regs m fm nx pv P) as [HR HK].
  set (E := Ez regs (VALS_mt1f fm nx pv)) in *. destruct P as [mt1f_R19 mt1f_rng_fm mt1f_rng_nx mt1f_rng_pv mt1f_ka1 mt1f_kw4 mt1f_kw5 mt1f_kw6 mt1f_kw7 mt1f_kw8 mt1f_kwr9 mt1f_kwr10 mt1f_kwr11 mt1f_kd12 mt1f_kd13 mt1f_kd14 mt1f_kd15].
  assert (Z32 : bv_unsigned (ev E 32) = fm) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = nx) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = pv) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x51d94; 0x51f1c] AXF_mt1f.scr_pmfn 0x51cdc AXF_mt1f.sr_mt1f AXF_mt1f.kn_mt1f 35 _ _ _ E m rom regs AXF_mt1f.RES_pmfn_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mt1f.RES_pmfn fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mt1f_mem_pmfn m regs fm nx pv) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mt1f_mem_pmfn. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MT1F.
End AXF_mt1fz.

Module AXF_mt1z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section MT1.
Context {fx : FPState}.

Definition VALS_mt1 (d : Z) : list Z := [d].

Record mt1_pre (regs : bvmap 5 word) (m : word -> option byte) (d : Z) : Prop := {
  mt1_R19 : getr regs 19 = wa 614096 ;
  mt1_rng_d : 0 <= d <= 1 ;
  mt1_kw0 : rdn SEGS m (wa (0 + 614112)) 4 = Some (word_to_le_bytes 4 (wa 1)) ;
  mt1_kw1 : rdn SEGS m (wa (0 + 614032)) 8 = Some (word_to_le_bytes 8 (wa 4096)) ;
  mt1_kw2 : rdn SEGS m (wa (0 + 614120)) 8 = Some (word_to_le_bytes 8 (wa 0))
}.


#[using="Type"] Lemma mt1_setup : forall regs m d, mt1_pre regs m d ->
  regs_ok (Ez regs (VALS_mt1 d)) AXF_mt1.sr_mt1 regs /\ know_ok SEGS (Ez regs (VALS_mt1 d)) m AXF_mt1.kn_mt1.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m d P. destruct P as [mt1_R19 mt1_rng_d mt1_kw0 mt1_kw1 mt1_kw2].
  set (E := Ez regs (VALS_mt1 d)).
  assert (Z32 : bv_unsigned (ev E 32) = d) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mt1.sr_mt1.
    apply (regs_ok_pin E _ regs 19); [apply regs_ok_id|].
    - rewrite mt1_R19. reflexivity. }
  unfold know_ok, AXF_mt1.kn_mt1.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mt1.e_d a_base a_off].
  all: rewrite ?Z32.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range d _ _ mt1_rng_d eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - mt1_rng_d; lia).
  all: first [lia].
Qed.


Definition mt1_mem_pmt1 (m : word -> option byte) (regs : bvmap 5 word) (d : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mt1_pmt1 : forall regs m rom d, mt1_pre regs m d ->
  scs_denot SEGS m (Ez regs (VALS_mt1 d)) (snd (fst AXF_mt1.RES_pmt1)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51cdc) m rom) (mkst R (wa 0x51d94) (mt1_mem_pmt1 m regs d) rom) /\
    getr R 8 = wa 4096 /\ getr R 10 = wa 0 /\ getr R 11 = wa 613600 /\ getr R 19 = wa 614096 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 9; 12; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom d P Hsc. destruct (mt1_setup regs m d P) as [HR HK].
  set (E := Ez regs (VALS_mt1 d)) in *. destruct P as [mt1_R19 mt1_rng_d mt1_kw0 mt1_kw1 mt1_kw2].
  assert (Z32 : bv_unsigned (ev E 32) = d) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x51d94; 0x51f1c] AXF_mt1.scr_pmt1 0x51cdc AXF_mt1.sr_mt1 AXF_mt1.kn_mt1 33 _ _ _ E m rom regs AXF_mt1.RES_pmt1_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mt1.RES_pmt1 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mt1_mem_pmt1 m regs d) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mt1_mem_pmt1. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MT1.
End AXF_mt1z.

Module AXF_mt2.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_cnt := EVar 32.
Definition e_am := EVar 33.
Definition sr_mt2 := (sr_upd sr_id 19 (ELit 614096)).
Definition kn_mt2 : list kentry :=
  [ KRange e_cnt 0 101;
    KRange e_am 0 (2^63-1);
    KWord (SA (ELit 0) 614136) 8 e_cnt;
    KWord (SA (ELit 0) 614128) 8 e_am;
    KWr (SA (ELit 0) 614128) (ELit 16) ].
Definition scr_mt2 : scripts := SCR [false] [] [].
Definition ss_mt2 := SS 0x51d94 sr_mt2 [] kn_mt2 34.
Definition RUN_mt2 := sym_exec SEGS 100 true [0x51f1c; 0x51db0] scr_mt2 ss_mt2 [].

Definition scr_pmt2t : scripts := SCR [false] [] [].
Definition RES_pmt2t := Eval vm_compute in sym_exec SEGS 100 true [0x51f1c; 0x51db0] scr_pmt2t ss_mt2 [].
Lemma RES_pmt2t_ok : sym_exec SEGS 100 true [0x51f1c; 0x51db0] scr_pmt2t (SS 0x51d94 sr_mt2 [] kn_mt2 34) [] = RES_pmt2t.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pmt2z : scripts := SCR [true] [] [].
Definition RES_pmt2z := Eval vm_compute in sym_exec SEGS 100 true [0x51f1c; 0x51db0] scr_pmt2z ss_mt2 [].
Lemma RES_pmt2z_ok : sym_exec SEGS 100 true [0x51f1c; 0x51db0] scr_pmt2z (SS 0x51d94 sr_mt2 [] kn_mt2 34) [] = RES_pmt2z.
Proof. vm_compute. reflexivity. Qed.
End AXF_mt2.

Module AXF_mt2z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section MT2.
Context {fx : FPState}.

Definition VALS_mt2 (cnt am : Z) : list Z := [cnt; am].

Record mt2_pre (regs : bvmap 5 word) (m : word -> option byte) (cnt am : Z) : Prop := {
  mt2_R19 : getr regs 19 = wa 614096 ;
  mt2_rng_cnt : 0 <= cnt <= 101 ;
  mt2_rng_am : 0 <= am <= 2^63-1 ;
  mt2_kw2 : rdn SEGS m (wa (0 + 614136)) 8 = Some (word_to_le_bytes 8 (wa cnt)) ;
  mt2_kw3 : rdn SEGS m (wa (0 + 614128)) 8 = Some (word_to_le_bytes 8 (wa am)) ;
  mt2_kwr4 : forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS m (wa (0 + 614128 + d)) k = true
}.


#[using="Type"] Lemma mt2_setup : forall regs m cnt am, mt2_pre regs m cnt am ->
  regs_ok (Ez regs (VALS_mt2 cnt am)) AXF_mt2.sr_mt2 regs /\ know_ok SEGS (Ez regs (VALS_mt2 cnt am)) m AXF_mt2.kn_mt2.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m cnt am P. destruct P as [mt2_R19 mt2_rng_cnt mt2_rng_am mt2_kw2 mt2_kw3 mt2_kwr4].
  set (E := Ez regs (VALS_mt2 cnt am)).
  assert (Z32 : bv_unsigned (ev E 32) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = am) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mt2.sr_mt2.
    apply (regs_ok_pin E _ regs 19); [apply regs_ok_id|].
    - rewrite mt2_R19. reflexivity. }
  unfold know_ok, AXF_mt2.kn_mt2.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mt2.e_cnt AXF_mt2.e_am a_base a_off].
  all: rewrite ?Z32, ?Z33.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range cnt _ _ mt2_rng_cnt eq_refl eq_refl), ?(mod64_of_range am _ _ mt2_rng_am eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply mt2_kwr4]; assumption).
  all: try (clear - mt2_rng_cnt mt2_rng_am; lia).
  all: first [lia].
Qed.


Definition mt2_mem_pmt2t (m : word -> option byte) (regs : bvmap 5 word) (cnt am : Z) : word -> option byte :=
  wbytes (wbytes (m) (wa (0 + 614128)) (word_to_le_bytes 8 (wa (am + 40)))) (wa (0 + 614136)) (word_to_le_bytes 8 (wa (cnt + -1))).

#[using="Type"] Theorem mt2_pmt2t : forall regs m rom cnt am, mt2_pre regs m cnt am ->
  scs_denot SEGS m (Ez regs (VALS_mt2 cnt am)) (snd (fst AXF_mt2.RES_pmt2t)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51d94) m rom) (mkst R (wa 0x51f1c) (mt2_mem_pmt2t m regs cnt am) rom) /\
    getr R 10 = wa am /\ getr R 11 = wa (cnt + -1) /\ getr R 12 = wa (am + 40) /\ getr R 19 = wa 614096 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom cnt am P Hsc. destruct (mt2_setup regs m cnt am P) as [HR HK].
  set (E := Ez regs (VALS_mt2 cnt am)) in *. destruct P as [mt2_R19 mt2_rng_cnt mt2_rng_am mt2_kw2 mt2_kw3 mt2_kwr4].
  assert (Z32 : bv_unsigned (ev E 32) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = am) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x51f1c; 0x51db0] AXF_mt2.scr_pmt2t 0x51d94 AXF_mt2.sr_mt2 AXF_mt2.kn_mt2 34 _ _ _ E m rom regs AXF_mt2.RES_pmt2t_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mt2.RES_pmt2t fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mt2_mem_pmt2t m regs cnt am) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mt2_mem_pmt2t. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition mt2_mem_pmt2z (m : word -> option byte) (regs : bvmap 5 word) (cnt am : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mt2_pmt2z : forall regs m rom cnt am, mt2_pre regs m cnt am ->
  scs_denot SEGS m (Ez regs (VALS_mt2 cnt am)) (snd (fst AXF_mt2.RES_pmt2z)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51d94) m rom) (mkst R (wa 0x51db0) (mt2_mem_pmt2z m regs cnt am) rom) /\
    getr R 11 = wa cnt /\ getr R 19 = wa 614096 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 12; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom cnt am P Hsc. destruct (mt2_setup regs m cnt am P) as [HR HK].
  set (E := Ez regs (VALS_mt2 cnt am)) in *. destruct P as [mt2_R19 mt2_rng_cnt mt2_rng_am mt2_kw2 mt2_kw3 mt2_kwr4].
  assert (Z32 : bv_unsigned (ev E 32) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = am) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x51f1c; 0x51db0] AXF_mt2.scr_pmt2z 0x51d94 AXF_mt2.sr_mt2 AXF_mt2.kn_mt2 34 _ _ _ E m rom regs AXF_mt2.RES_pmt2z_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mt2.RES_pmt2z fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mt2_mem_pmt2z m regs cnt am) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mt2_mem_pmt2z. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MT2.
End AXF_mt2z.

Module AXF_mt3o.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_ac := EVar 32.
Definition e_ar := EVar 33.
Definition sr_mt3o := (sr_upd (sr_upd sr_id 8 (ELit 4096)) 19 (ELit 614096)).
Definition kn_mt3o : list kentry :=
  [ KRange e_ac 1 (2^60);
    KRange e_ar 0 (2^63-1);
    KWord (SA (ELit 0) 614144) 8 e_ac;
    KWord (SA (ELit 0) 614176) 8 e_ar ].
Definition scr_mt3o : scripts := SCR [] [] [].
Definition ss_mt3o := SS 0x51db0 sr_mt3o [] kn_mt3o 34.
Definition RUN_mt3o := sym_exec SEGS 100 true [0x51eb4; 0x51dd4; 0x51dec; 0x53328] scr_mt3o ss_mt3o [].

Definition scr_pmt3oo : scripts := SCR [] [] [].
Definition RES_pmt3oo := Eval vm_compute in sym_exec SEGS 100 true [0x51eb4; 0x51dd4; 0x51dec; 0x53328] scr_pmt3oo ss_mt3o [].
Lemma RES_pmt3oo_ok : sym_exec SEGS 100 true [0x51eb4; 0x51dd4; 0x51dec; 0x53328] scr_pmt3oo (SS 0x51db0 sr_mt3o [] kn_mt3o 34) [] = RES_pmt3oo.
Proof. vm_compute. reflexivity. Qed.
End AXF_mt3o.

Module AXF_mt3oz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section MT3O.
Context {fx : FPState}.

Definition VALS_mt3o (ac ar : Z) : list Z := [ac; ar].

Record mt3o_pre (regs : bvmap 5 word) (m : word -> option byte) (ac ar : Z) : Prop := {
  mt3o_R8 : getr regs 8 = wa 4096 ;
  mt3o_R19 : getr regs 19 = wa 614096 ;
  mt3o_rng_ac : 1 <= ac <= 2^60 ;
  mt3o_rng_ar : 0 <= ar <= 2^63-1 ;
  mt3o_kw2 : rdn SEGS m (wa (0 + 614144)) 8 = Some (word_to_le_bytes 8 (wa ac)) ;
  mt3o_kw3 : rdn SEGS m (wa (0 + 614176)) 8 = Some (word_to_le_bytes 8 (wa ar))
}.


#[using="Type"] Lemma mt3o_setup : forall regs m ac ar, mt3o_pre regs m ac ar ->
  regs_ok (Ez regs (VALS_mt3o ac ar)) AXF_mt3o.sr_mt3o regs /\ know_ok SEGS (Ez regs (VALS_mt3o ac ar)) m AXF_mt3o.kn_mt3o.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m ac ar P. destruct P as [mt3o_R8 mt3o_R19 mt3o_rng_ac mt3o_rng_ar mt3o_kw2 mt3o_kw3].
  set (E := Ez regs (VALS_mt3o ac ar)).
  assert (Z32 : bv_unsigned (ev E 32) = ac) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ar) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mt3o.sr_mt3o.
    apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|].
    - rewrite mt3o_R8. reflexivity.
    - rewrite mt3o_R19. reflexivity. }
  unfold know_ok, AXF_mt3o.kn_mt3o.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mt3o.e_ac AXF_mt3o.e_ar a_base a_off].
  all: rewrite ?Z32, ?Z33.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range ac _ _ mt3o_rng_ac eq_refl eq_refl), ?(mod64_of_range ar _ _ mt3o_rng_ar eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - mt3o_rng_ac mt3o_rng_ar; lia).
  all: first [lia].
Qed.


Definition mt3o_mem_pmt3oo (m : word -> option byte) (regs : bvmap 5 word) (ac ar : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mt3o_pmt3oo : forall regs m rom ac ar, mt3o_pre regs m ac ar ->
  scs_denot SEGS m (Ez regs (VALS_mt3o ac ar)) (snd (fst AXF_mt3o.RES_pmt3oo)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51db0) m rom) (mkst R (wa 0x51eb4) (mt3o_mem_pmt3oo m regs ac ar) rom) /\
    getr R 8 = wa 4096 /\ getr R 9 = wa ar /\ getr R 10 = wa ac /\ getr R 19 = wa 614096 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom ac ar P Hsc. destruct (mt3o_setup regs m ac ar P) as [HR HK].
  set (E := Ez regs (VALS_mt3o ac ar)) in *. destruct P as [mt3o_R8 mt3o_R19 mt3o_rng_ac mt3o_rng_ar mt3o_kw2 mt3o_kw3].
  assert (Z32 : bv_unsigned (ev E 32) = ac) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ar) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x51eb4; 0x51dd4; 0x51dec; 0x53328] AXF_mt3o.scr_pmt3oo 0x51db0 AXF_mt3o.sr_mt3o AXF_mt3o.kn_mt3o 34 _ _ _ E m rom regs AXF_mt3o.RES_pmt3oo_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mt3o.RES_pmt3oo fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mt3o_mem_pmt3oo m regs ac ar) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mt3o_mem_pmt3oo. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MT3O.
End AXF_mt3oz.

Module AXF_mt3w.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_ac := EVar 32.
Definition e_bk := EVar 33.
Definition e_ar := EVar 34.
Definition e_sh := EVar 35.
Definition sr_mt3w := (sr_upd (sr_upd sr_id 8 (ELit 4096)) 19 (ELit 614096)).
Definition kn_mt3w : list kentry :=
  [ KRange e_ac 0 (2^60);
    KRange e_bk 0 (2^64-1);
    KRange e_ar 0 (2^64-1);
    KRange e_sh 0 40;
    KWord (SA (ELit 0) 614144) 8 e_ac;
    KWord (SA (ELit 0) 615024) 8 e_bk;
    KWord (SA (ELit 0) 614176) 8 e_ar;
    KWord (SA (ELit 0) 614152) 8 e_sh ].
Definition scr_mt3w : scripts := SCR [true; false] [] [].
Definition ss_mt3w := SS 0x51db0 sr_mt3w [] kn_mt3w 36.
Definition RUN_mt3w := sym_exec SEGS 100 true [0x51eb4; 0x51dd4; 0x51dec; 0x53328] scr_mt3w ss_mt3w [].

Definition scr_pmt3dw : scripts := SCR [false; true; true] [] [].
Definition RES_pmt3dw := Eval vm_compute in sym_exec SEGS 100 true [0x51eb4; 0x51dd4; 0x51dec; 0x53328] scr_pmt3dw ss_mt3w [].
Lemma RES_pmt3dw_ok : sym_exec SEGS 100 true [0x51eb4; 0x51dd4; 0x51dec; 0x53328] scr_pmt3dw (SS 0x51db0 sr_mt3w [] kn_mt3w 36) [] = RES_pmt3dw.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pmt3nw : scripts := SCR [false; false; true] [] [].
Definition RES_pmt3nw := Eval vm_compute in sym_exec SEGS 100 true [0x51eb4; 0x51dd4; 0x51dec; 0x53328] scr_pmt3nw ss_mt3w [].
Lemma RES_pmt3nw_ok : sym_exec SEGS 100 true [0x51eb4; 0x51dd4; 0x51dec; 0x53328] scr_pmt3nw (SS 0x51db0 sr_mt3w [] kn_mt3w 36) [] = RES_pmt3nw.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pmt3cw : scripts := SCR [false; false; false] [] [].
Definition RES_pmt3cw := Eval vm_compute in sym_exec SEGS 100 true [0x51eb4; 0x51dd4; 0x51dec; 0x53328] scr_pmt3cw ss_mt3w [].
Lemma RES_pmt3cw_ok : sym_exec SEGS 100 true [0x51eb4; 0x51dd4; 0x51dec; 0x53328] scr_pmt3cw (SS 0x51db0 sr_mt3w [] kn_mt3w 36) [] = RES_pmt3cw.
Proof. vm_compute. reflexivity. Qed.
End AXF_mt3w.

Module AXF_mt3wz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section MT3W.
Context {fx : FPState}.

Definition VALS_mt3w (ac bk ar sh : Z) : list Z := [ac; bk; ar; sh].

Record mt3w_pre (regs : bvmap 5 word) (m : word -> option byte) (ac bk ar sh : Z) : Prop := {
  mt3w_R8 : getr regs 8 = wa 4096 ;
  mt3w_R19 : getr regs 19 = wa 614096 ;
  mt3w_rng_ac : 0 <= ac <= 2^60 ;
  mt3w_rng_bk : 0 <= bk <= 2^64-1 ;
  mt3w_rng_ar : 0 <= ar <= 2^64-1 ;
  mt3w_rng_sh : 0 <= sh <= 40 ;
  mt3w_kw4 : rdn SEGS m (wa (0 + 614144)) 8 = Some (word_to_le_bytes 8 (wa ac)) ;
  mt3w_kw5 : rdn SEGS m (wa (0 + 615024)) 8 = Some (word_to_le_bytes 8 (wa bk)) ;
  mt3w_kw6 : rdn SEGS m (wa (0 + 614176)) 8 = Some (word_to_le_bytes 8 (wa ar)) ;
  mt3w_kw7 : rdn SEGS m (wa (0 + 614152)) 8 = Some (word_to_le_bytes 8 (wa sh))
}.


#[using="Type"] Lemma mt3w_setup : forall regs m ac bk ar sh, mt3w_pre regs m ac bk ar sh ->
  regs_ok (Ez regs (VALS_mt3w ac bk ar sh)) AXF_mt3w.sr_mt3w regs /\ know_ok SEGS (Ez regs (VALS_mt3w ac bk ar sh)) m AXF_mt3w.kn_mt3w.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m ac bk ar sh P. destruct P as [mt3w_R8 mt3w_R19 mt3w_rng_ac mt3w_rng_bk mt3w_rng_ar mt3w_rng_sh mt3w_kw4 mt3w_kw5 mt3w_kw6 mt3w_kw7].
  set (E := Ez regs (VALS_mt3w ac bk ar sh)).
  assert (Z32 : bv_unsigned (ev E 32) = ac) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = bk) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = ar) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = sh) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mt3w.sr_mt3w.
    apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|].
    - rewrite mt3w_R8. reflexivity.
    - rewrite mt3w_R19. reflexivity. }
  unfold know_ok, AXF_mt3w.kn_mt3w.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mt3w.e_ac AXF_mt3w.e_bk AXF_mt3w.e_ar AXF_mt3w.e_sh a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range ac _ _ mt3w_rng_ac eq_refl eq_refl), ?(mod64_of_range sh _ _ mt3w_rng_sh eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - mt3w_rng_ac mt3w_rng_bk mt3w_rng_ar mt3w_rng_sh; lia).
  all: first [lia].
Qed.


Definition mt3w_mem_pmt3dw (m : word -> option byte) (regs : bvmap 5 word) (ac bk ar sh : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mt3w_pmt3dw : forall regs m rom ac bk ar sh, mt3w_pre regs m ac bk ar sh ->
  scs_denot SEGS m (Ez regs (VALS_mt3w ac bk ar sh)) (snd (fst AXF_mt3w.RES_pmt3dw)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51db0) m rom) (mkst R (wa 0x53328) (mt3w_mem_pmt3dw m regs ac bk ar sh) rom) /\
    getr R 1 = wa 335500 /\ getr R 8 = wa 4096 /\ getr R 9 = wa (Z.shiftl 2 sh) /\ getr R 10 = wa 0 /\ getr R 11 = wa (4096 * Z.shiftl 2 sh) /\ getr R 12 = wa 0 /\ getr R 13 = wa 34 /\ getr R 14 = wa 18446744073709551615 /\ getr R 15 = wa 0 /\ getr R 19 = wa 614096 /\ getr R 20 = wa 18446744073709551615 /\ (forall k, In k [2; 3; 4; 5; 6; 7; 16; 17; 18; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom ac bk ar sh P Hsc. destruct (mt3w_setup regs m ac bk ar sh P) as [HR HK].
  set (E := Ez regs (VALS_mt3w ac bk ar sh)) in *. destruct P as [mt3w_R8 mt3w_R19 mt3w_rng_ac mt3w_rng_bk mt3w_rng_ar mt3w_rng_sh mt3w_kw4 mt3w_kw5 mt3w_kw6 mt3w_kw7].
  assert (Z32 : bv_unsigned (ev E 32) = ac) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = bk) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = ar) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = sh) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x51eb4; 0x51dd4; 0x51dec; 0x53328] AXF_mt3w.scr_pmt3dw 0x51db0 AXF_mt3w.sr_mt3w AXF_mt3w.kn_mt3w 36 _ _ _ E m rom regs AXF_mt3w.RES_pmt3dw_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mt3w.RES_pmt3dw fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mt3w_mem_pmt3dw m regs ac bk ar sh) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mt3w_mem_pmt3dw. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition mt3w_mem_pmt3nw (m : word -> option byte) (regs : bvmap 5 word) (ac bk ar sh : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mt3w_pmt3nw : forall regs m rom ac bk ar sh, mt3w_pre regs m ac bk ar sh ->
  scs_denot SEGS m (Ez regs (VALS_mt3w ac bk ar sh)) (snd (fst AXF_mt3w.RES_pmt3nw)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51db0) m rom) (mkst R (wa 0x51dec) (mt3w_mem_pmt3nw m regs ac bk ar sh) rom) /\
    getr R 8 = wa 4096 /\ getr R 9 = wa bk /\ getr R 10 = wa 0 /\ getr R 11 = wa 4095 /\ getr R 17 = wa 214 /\ getr R 19 = wa 614096 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 12; 13; 14; 15; 16; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom ac bk ar sh P Hsc. destruct (mt3w_setup regs m ac bk ar sh P) as [HR HK].
  set (E := Ez regs (VALS_mt3w ac bk ar sh)) in *. destruct P as [mt3w_R8 mt3w_R19 mt3w_rng_ac mt3w_rng_bk mt3w_rng_ar mt3w_rng_sh mt3w_kw4 mt3w_kw5 mt3w_kw6 mt3w_kw7].
  assert (Z32 : bv_unsigned (ev E 32) = ac) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = bk) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = ar) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = sh) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x51eb4; 0x51dd4; 0x51dec; 0x53328] AXF_mt3w.scr_pmt3nw 0x51db0 AXF_mt3w.sr_mt3w AXF_mt3w.kn_mt3w 36 _ _ _ E m rom regs AXF_mt3w.RES_pmt3nw_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mt3w.RES_pmt3nw fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mt3w_mem_pmt3nw m regs ac bk ar sh) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mt3w_mem_pmt3nw. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition mt3w_mem_pmt3cw (m : word -> option byte) (regs : bvmap 5 word) (ac bk ar sh : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mt3w_pmt3cw : forall regs m rom ac bk ar sh, mt3w_pre regs m ac bk ar sh ->
  scs_denot SEGS m (Ez regs (VALS_mt3w ac bk ar sh)) (snd (fst AXF_mt3w.RES_pmt3cw)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51db0) m rom) (mkst R (wa 0x51dd4) (mt3w_mem_pmt3cw m regs ac bk ar sh) rom) /\
    getr R 8 = wa 4096 /\ getr R 9 = wa (bk + 4096) /\ getr R 10 = wa (bk + 4096) /\ getr R 11 = wa 18446744073709551615 /\ getr R 17 = wa 214 /\ getr R 19 = wa 614096 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 12; 13; 14; 15; 16; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom ac bk ar sh P Hsc. destruct (mt3w_setup regs m ac bk ar sh P) as [HR HK].
  set (E := Ez regs (VALS_mt3w ac bk ar sh)) in *. destruct P as [mt3w_R8 mt3w_R19 mt3w_rng_ac mt3w_rng_bk mt3w_rng_ar mt3w_rng_sh mt3w_kw4 mt3w_kw5 mt3w_kw6 mt3w_kw7].
  assert (Z32 : bv_unsigned (ev E 32) = ac) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = bk) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = ar) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = sh) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x51eb4; 0x51dd4; 0x51dec; 0x53328] AXF_mt3w.scr_pmt3cw 0x51db0 AXF_mt3w.sr_mt3w AXF_mt3w.kn_mt3w 36 _ _ _ E m rom regs AXF_mt3w.RES_pmt3cw_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mt3w.RES_pmt3cw fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mt3w_mem_pmt3cw m regs ac bk ar sh) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mt3w_mem_pmt3cw. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MT3W.
End AXF_mt3wz.

Module AXF_mt4.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_b0 := EVar 32.
Definition sr_mt4 := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 8 (ELit 4096)) 10 (e_b0)) 11 (ELit 4095)) 19 (ELit 614096)).
Definition kn_mt4 : list kentry :=
  [ KRange e_b0 0 (2^47);
    KWr (SA (ELit 0) 615024) (ELit 8) ].
Definition scr_mt4 : scripts := SCR [] [] [].
Definition ss_mt4 := SS 0x51df0 sr_mt4 [] kn_mt4 33.
Definition RUN_mt4 := sym_exec SEGS 100 true [0x51e10] scr_mt4 ss_mt4 [].

Definition scr_pmt4 : scripts := SCR [] [] [].
Definition RES_pmt4 := Eval vm_compute in sym_exec SEGS 100 true [0x51e10] scr_pmt4 ss_mt4 [].
Lemma RES_pmt4_ok : sym_exec SEGS 100 true [0x51e10] scr_pmt4 (SS 0x51df0 sr_mt4 [] kn_mt4 33) [] = RES_pmt4.
Proof. vm_compute. reflexivity. Qed.
End AXF_mt4.

Module AXF_mt4z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section MT4.
Context {fx : FPState}.

Definition VALS_mt4 (b0 : Z) : list Z := [b0].

Record mt4_pre (regs : bvmap 5 word) (m : word -> option byte) (b0 : Z) : Prop := {
  mt4_R8 : getr regs 8 = wa 4096 ;
  mt4_R10 : getr regs 10 = wa b0 ;
  mt4_R11 : getr regs 11 = wa 4095 ;
  mt4_R19 : getr regs 19 = wa 614096 ;
  mt4_rng_b0 : 0 <= b0 <= 2^47 ;
  mt4_kwr1 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (0 + 615024 + d)) k = true
}.


#[using="Type"] Lemma mt4_setup : forall regs m b0, mt4_pre regs m b0 ->
  regs_ok (Ez regs (VALS_mt4 b0)) AXF_mt4.sr_mt4 regs /\ know_ok SEGS (Ez regs (VALS_mt4 b0)) m AXF_mt4.kn_mt4.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m b0 P. destruct P as [mt4_R8 mt4_R10 mt4_R11 mt4_R19 mt4_rng_b0 mt4_kwr1].
  set (E := Ez regs (VALS_mt4 b0)).
  assert (Z32 : bv_unsigned (ev E 32) = b0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mt4.sr_mt4.
    apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|]|]|].
    - rewrite mt4_R8. reflexivity.
    - rewrite mt4_R10. reflexivity.
    - rewrite mt4_R11. reflexivity.
    - rewrite mt4_R19. reflexivity. }
  unfold know_ok, AXF_mt4.kn_mt4.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mt4.e_b0 a_base a_off].
  all: rewrite ?Z32.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range b0 _ _ mt4_rng_b0 eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply mt4_kwr1]; assumption).
  all: try (clear - mt4_rng_b0; lia).
  all: first [lia].
Qed.


Definition mt4_mem_pmt4 (m : word -> option byte) (regs : bvmap 5 word) (b0 : Z) : word -> option byte :=
  wbytes (m) (wa (0 + 615024)) (word_to_le_bytes 8 (wa (b0 + Z.land (((-1 * b0)) mod 2^64) 4095))).

#[using="Type"] Theorem mt4_pmt4 : forall regs m rom b0, mt4_pre regs m b0 ->
  scs_denot SEGS m (Ez regs (VALS_mt4 b0)) (snd (fst AXF_mt4.RES_pmt4)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51df0) m rom) (mkst R (wa 0x51e10) (mt4_mem_pmt4 m regs b0) rom) /\
    getr R 8 = wa 4096 /\ getr R 9 = wa ((b0 + Z.land (((-1 * b0)) mod 2^64) 4095) + 8192) /\ getr R 10 = wa ((b0 + Z.land (((-1 * b0)) mod 2^64) 4095) + 8192) /\ getr R 11 = wa (Z.land (((-1 * b0)) mod 2^64) 4095) /\ getr R 12 = wa (-1 * b0) /\ getr R 17 = wa 214 /\ getr R 19 = wa 614096 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 13; 14; 15; 16; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom b0 P Hsc. destruct (mt4_setup regs m b0 P) as [HR HK].
  set (E := Ez regs (VALS_mt4 b0)) in *. destruct P as [mt4_R8 mt4_R10 mt4_R11 mt4_R19 mt4_rng_b0 mt4_kwr1].
  assert (Z32 : bv_unsigned (ev E 32) = b0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x51e10] AXF_mt4.scr_pmt4 0x51df0 AXF_mt4.sr_mt4 AXF_mt4.kn_mt4 33 _ _ _ E m rom regs AXF_mt4.RES_pmt4_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mt4.RES_pmt4 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mt4_mem_pmt4 m regs b0) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mt4_mem_pmt4. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MT4.
End AXF_mt4z.

Module AXF_mt5.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_res := EVar 32.
Definition e_b := EVar 33.
Definition e_sh := EVar 34.
Definition sr_mt5 := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 8 (ELit 4096)) 9 (EAlu ALU_ADD e_b (ELit 8192))) 10 (e_res)) 19 (ELit 614096)).
Definition kn_mt5 : list kentry :=
  [ KRange e_res 0 (2^64-1);
    KRange e_b 4096 (2^47);
    KRange e_sh 0 40;
    KWord (SA (ELit 0) 615024) 8 e_b;
    KWord (SA (ELit 0) 614144) 8 (ELit 0);
    KWord (SA (ELit 0) 614152) 8 e_sh;
    KWr (SA (ELit 0) 615024) (ELit 8) ].
Definition scr_mt5 : scripts := SCR [false] [] [].
Definition ss_mt5 := SS 0x51e14 sr_mt5 [] kn_mt5 35.
Definition RUN_mt5 := sym_exec SEGS 100 true [0x53328] scr_mt5 ss_mt5 [].

Definition scr_pmt5g : scripts := SCR [false] [] [].
Definition RES_pmt5g := Eval vm_compute in sym_exec SEGS 100 true [0x53328] scr_pmt5g ss_mt5 [].
Lemma RES_pmt5g_ok : sym_exec SEGS 100 true [0x53328] scr_pmt5g (SS 0x51e14 sr_mt5 [] kn_mt5 35) [] = RES_pmt5g.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pmt5r : scripts := SCR [true] [] [].
Definition RES_pmt5r := Eval vm_compute in sym_exec SEGS 100 true [0x53328] scr_pmt5r ss_mt5 [].
Lemma RES_pmt5r_ok : sym_exec SEGS 100 true [0x53328] scr_pmt5r (SS 0x51e14 sr_mt5 [] kn_mt5 35) [] = RES_pmt5r.
Proof. vm_compute. reflexivity. Qed.
End AXF_mt5.

Module AXF_mt5z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section MT5.
Context {fx : FPState}.

Definition VALS_mt5 (res b sh : Z) : list Z := [res; b; sh].

Record mt5_pre (regs : bvmap 5 word) (m : word -> option byte) (res b sh : Z) : Prop := {
  mt5_R8 : getr regs 8 = wa 4096 ;
  mt5_R9 : getr regs 9 = wa (b + 8192) ;
  mt5_R10 : getr regs 10 = wa res ;
  mt5_R19 : getr regs 19 = wa 614096 ;
  mt5_rng_res : 0 <= res <= 2^64-1 ;
  mt5_rng_b : 4096 <= b <= 2^47 ;
  mt5_rng_sh : 0 <= sh <= 40 ;
  mt5_kw3 : rdn SEGS m (wa (0 + 615024)) 8 = Some (word_to_le_bytes 8 (wa b)) ;
  mt5_kw4 : rdn SEGS m (wa (0 + 614144)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  mt5_kw5 : rdn SEGS m (wa (0 + 614152)) 8 = Some (word_to_le_bytes 8 (wa sh)) ;
  mt5_kwr6 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (0 + 615024 + d)) k = true
}.


#[using="Type"] Lemma mt5_setup : forall regs m res b sh, mt5_pre regs m res b sh ->
  regs_ok (Ez regs (VALS_mt5 res b sh)) AXF_mt5.sr_mt5 regs /\ know_ok SEGS (Ez regs (VALS_mt5 res b sh)) m AXF_mt5.kn_mt5.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m res b sh P. destruct P as [mt5_R8 mt5_R9 mt5_R10 mt5_R19 mt5_rng_res mt5_rng_b mt5_rng_sh mt5_kw3 mt5_kw4 mt5_kw5 mt5_kwr6].
  set (E := Ez regs (VALS_mt5 res b sh)).
  assert (Z32 : bv_unsigned (ev E 32) = res) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = b) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sh) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mt5.sr_mt5.
    apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|]|]|].
    - rewrite mt5_R8. reflexivity.
    - rewrite mt5_R9, zeval_sound. cbn [zeval edenot AXF_mt5.e_res AXF_mt5.e_b AXF_mt5.e_sh]. rewrite ?Z32, ?Z33, ?Z34. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite mt5_R10. reflexivity.
    - rewrite mt5_R19. reflexivity. }
  unfold know_ok, AXF_mt5.kn_mt5.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mt5.e_res AXF_mt5.e_b AXF_mt5.e_sh a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range b _ _ mt5_rng_b eq_refl eq_refl), ?(mod64_of_range sh _ _ mt5_rng_sh eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply mt5_kwr6]; assumption).
  all: try (clear - mt5_rng_res mt5_rng_b mt5_rng_sh; lia).
  all: first [lia].
Qed.


Definition mt5_mem_pmt5g (m : word -> option byte) (regs : bvmap 5 word) (res b sh : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mt5_pmt5g : forall regs m rom res b sh, mt5_pre regs m res b sh ->
  scs_denot SEGS m (Ez regs (VALS_mt5 res b sh)) (snd (fst AXF_mt5.RES_pmt5g)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51e14) m rom) (mkst R (wa 0x53328) (mt5_mem_pmt5g m regs res b sh) rom) /\
    getr R 1 = wa 335412 /\ getr R 8 = wa 4096 /\ getr R 9 = wa (b + 8192) /\ getr R 10 = wa b /\ getr R 11 = wa 4096 /\ getr R 12 = wa 0 /\ getr R 13 = wa 50 /\ getr R 14 = wa 18446744073709551615 /\ getr R 15 = wa 0 /\ getr R 19 = wa 614096 /\ (forall k, In k [2; 3; 4; 5; 6; 7; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom res b sh P Hsc. destruct (mt5_setup regs m res b sh P) as [HR HK].
  set (E := Ez regs (VALS_mt5 res b sh)) in *. destruct P as [mt5_R8 mt5_R9 mt5_R10 mt5_R19 mt5_rng_res mt5_rng_b mt5_rng_sh mt5_kw3 mt5_kw4 mt5_kw5 mt5_kwr6].
  assert (Z32 : bv_unsigned (ev E 32) = res) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = b) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sh) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53328] AXF_mt5.scr_pmt5g 0x51e14 AXF_mt5.sr_mt5 AXF_mt5.kn_mt5 35 _ _ _ E m rom regs AXF_mt5.RES_pmt5g_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mt5.RES_pmt5g fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mt5_mem_pmt5g m regs res b sh) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mt5_mem_pmt5g. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition mt5_mem_pmt5r (m : word -> option byte) (regs : bvmap 5 word) (res b sh : Z) : word -> option byte :=
  wbytes (m) (wa (0 + 615024)) (word_to_le_bytes 8 (wa 18446744073709551615)).

#[using="Type"] Theorem mt5_pmt5r : forall regs m rom res b sh, mt5_pre regs m res b sh ->
  scs_denot SEGS m (Ez regs (VALS_mt5 res b sh)) (snd (fst AXF_mt5.RES_pmt5r)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51e14) m rom) (mkst R (wa 0x53328) (mt5_mem_pmt5r m regs res b sh) rom) /\
    getr R 1 = wa 335500 /\ getr R 8 = wa 4096 /\ getr R 9 = wa (Z.shiftl 2 sh) /\ getr R 10 = wa 0 /\ getr R 11 = wa (4096 * Z.shiftl 2 sh) /\ getr R 12 = wa 0 /\ getr R 13 = wa 34 /\ getr R 14 = wa 18446744073709551615 /\ getr R 15 = wa 0 /\ getr R 19 = wa 614096 /\ getr R 20 = wa 18446744073709551615 /\ (forall k, In k [2; 3; 4; 5; 6; 7; 16; 17; 18; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom res b sh P Hsc. destruct (mt5_setup regs m res b sh P) as [HR HK].
  set (E := Ez regs (VALS_mt5 res b sh)) in *. destruct P as [mt5_R8 mt5_R9 mt5_R10 mt5_R19 mt5_rng_res mt5_rng_b mt5_rng_sh mt5_kw3 mt5_kw4 mt5_kw5 mt5_kwr6].
  assert (Z32 : bv_unsigned (ev E 32) = res) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = b) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sh) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53328] AXF_mt5.scr_pmt5r 0x51e14 AXF_mt5.sr_mt5 AXF_mt5.kn_mt5 35 _ _ _ E m rom regs AXF_mt5.RES_pmt5r_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mt5.RES_pmt5r fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mt5_mem_pmt5r m regs res b sh) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mt5_mem_pmt5r. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MT5.
End AXF_mt5z.

Module AXF_mt6.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_res := EVar 32.
Definition e_nb := EVar 33.
Definition e_sh := EVar 34.
Definition sr_mt6 := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 8 (ELit 4096)) 9 (e_nb)) 10 (e_res)) 19 (ELit 614096)).
Definition kn_mt6 : list kentry :=
  [ KRange e_res 0 (2^64-1);
    KRange e_nb 8192 (2^47);
    KRange e_sh 0 40;
    KWord (SA (ELit 0) 614144) 8 (ELit 0);
    KWord (SA (ELit 0) 614152) 8 e_sh;
    KWr (SA (ELit 0) 615024) (ELit 8);
    KWr (SA (ELit 0) 614144) (ELit 8) ].
Definition scr_mt6 : scripts := SCR [true] [] [].
Definition ss_mt6 := SS 0x51dd8 sr_mt6 [] kn_mt6 35.
Definition RUN_mt6 := sym_exec SEGS 100 true [0x51ec0; 0x53328] scr_mt6 ss_mt6 [].

Definition scr_pmt6g : scripts := SCR [true] [] [].
Definition RES_pmt6g := Eval vm_compute in sym_exec SEGS 100 true [0x51ec0; 0x53328] scr_pmt6g ss_mt6 [].
Lemma RES_pmt6g_ok : sym_exec SEGS 100 true [0x51ec0; 0x53328] scr_pmt6g (SS 0x51dd8 sr_mt6 [] kn_mt6 35) [] = RES_pmt6g.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pmt6r : scripts := SCR [false] [] [].
Definition RES_pmt6r := Eval vm_compute in sym_exec SEGS 100 true [0x51ec0; 0x53328] scr_pmt6r ss_mt6 [].
Lemma RES_pmt6r_ok : sym_exec SEGS 100 true [0x51ec0; 0x53328] scr_pmt6r (SS 0x51dd8 sr_mt6 [] kn_mt6 35) [] = RES_pmt6r.
Proof. vm_compute. reflexivity. Qed.
End AXF_mt6.

Module AXF_mt6z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section MT6.
Context {fx : FPState}.

Definition VALS_mt6 (res nb sh : Z) : list Z := [res; nb; sh].

Record mt6_pre (regs : bvmap 5 word) (m : word -> option byte) (res nb sh : Z) : Prop := {
  mt6_R8 : getr regs 8 = wa 4096 ;
  mt6_R9 : getr regs 9 = wa nb ;
  mt6_R10 : getr regs 10 = wa res ;
  mt6_R19 : getr regs 19 = wa 614096 ;
  mt6_rng_res : 0 <= res <= 2^64-1 ;
  mt6_rng_nb : 8192 <= nb <= 2^47 ;
  mt6_rng_sh : 0 <= sh <= 40 ;
  mt6_kw3 : rdn SEGS m (wa (0 + 614144)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  mt6_kw4 : rdn SEGS m (wa (0 + 614152)) 8 = Some (word_to_le_bytes 8 (wa sh)) ;
  mt6_kwr5 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (0 + 615024 + d)) k = true ;
  mt6_kwr6 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (0 + 614144 + d)) k = true
}.


#[using="Type"] Lemma mt6_setup : forall regs m res nb sh, mt6_pre regs m res nb sh ->
  regs_ok (Ez regs (VALS_mt6 res nb sh)) AXF_mt6.sr_mt6 regs /\ know_ok SEGS (Ez regs (VALS_mt6 res nb sh)) m AXF_mt6.kn_mt6.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m res nb sh P. destruct P as [mt6_R8 mt6_R9 mt6_R10 mt6_R19 mt6_rng_res mt6_rng_nb mt6_rng_sh mt6_kw3 mt6_kw4 mt6_kwr5 mt6_kwr6].
  set (E := Ez regs (VALS_mt6 res nb sh)).
  assert (Z32 : bv_unsigned (ev E 32) = res) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = nb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sh) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mt6.sr_mt6.
    apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|]|]|].
    - rewrite mt6_R8. reflexivity.
    - rewrite mt6_R9. reflexivity.
    - rewrite mt6_R10. reflexivity.
    - rewrite mt6_R19. reflexivity. }
  unfold know_ok, AXF_mt6.kn_mt6.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mt6.e_res AXF_mt6.e_nb AXF_mt6.e_sh a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range nb _ _ mt6_rng_nb eq_refl eq_refl), ?(mod64_of_range sh _ _ mt6_rng_sh eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply mt6_kwr5 | apply mt6_kwr6]; assumption).
  all: try (clear - mt6_rng_res mt6_rng_nb mt6_rng_sh; lia).
  all: first [lia].
Qed.


Definition mt6_mem_pmt6g (m : word -> option byte) (regs : bvmap 5 word) (res nb sh : Z) : word -> option byte :=
  wbytes (wbytes (m) (wa (0 + 615024)) (word_to_le_bytes 8 (wa nb))) (wa (0 + 614144)) (word_to_le_bytes 8 (wa 1)).

#[using="Type"] Theorem mt6_pmt6g : forall regs m rom res nb sh, mt6_pre regs m res nb sh ->
  scs_denot SEGS m (Ez regs (VALS_mt6 res nb sh)) (snd (fst AXF_mt6.RES_pmt6g)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51dd8) m rom) (mkst R (wa 0x51ec0) (mt6_mem_pmt6g m regs res nb sh) rom) /\
    getr R 8 = wa 1 /\ getr R 9 = wa (nb + -4096) /\ getr R 10 = wa res /\ getr R 19 = wa 614096 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom res nb sh P Hsc. destruct (mt6_setup regs m res nb sh P) as [HR HK].
  set (E := Ez regs (VALS_mt6 res nb sh)) in *. destruct P as [mt6_R8 mt6_R9 mt6_R10 mt6_R19 mt6_rng_res mt6_rng_nb mt6_rng_sh mt6_kw3 mt6_kw4 mt6_kwr5 mt6_kwr6].
  assert (Z32 : bv_unsigned (ev E 32) = res) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = nb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sh) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x51ec0; 0x53328] AXF_mt6.scr_pmt6g 0x51dd8 AXF_mt6.sr_mt6 AXF_mt6.kn_mt6 35 _ _ _ E m rom regs AXF_mt6.RES_pmt6g_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mt6.RES_pmt6g fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mt6_mem_pmt6g m regs res nb sh) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mt6_mem_pmt6g. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition mt6_mem_pmt6r (m : word -> option byte) (regs : bvmap 5 word) (res nb sh : Z) : word -> option byte :=
  wbytes (m) (wa (0 + 615024)) (word_to_le_bytes 8 (wa 18446744073709551615)).

#[using="Type"] Theorem mt6_pmt6r : forall regs m rom res nb sh, mt6_pre regs m res nb sh ->
  scs_denot SEGS m (Ez regs (VALS_mt6 res nb sh)) (snd (fst AXF_mt6.RES_pmt6r)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51dd8) m rom) (mkst R (wa 0x53328) (mt6_mem_pmt6r m regs res nb sh) rom) /\
    getr R 1 = wa 335500 /\ getr R 8 = wa 4096 /\ getr R 9 = wa (Z.shiftl 2 sh) /\ getr R 10 = wa 0 /\ getr R 11 = wa (4096 * Z.shiftl 2 sh) /\ getr R 12 = wa 0 /\ getr R 13 = wa 34 /\ getr R 14 = wa 18446744073709551615 /\ getr R 15 = wa 0 /\ getr R 19 = wa 614096 /\ getr R 20 = wa 18446744073709551615 /\ (forall k, In k [2; 3; 4; 5; 6; 7; 16; 17; 18; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom res nb sh P Hsc. destruct (mt6_setup regs m res nb sh P) as [HR HK].
  set (E := Ez regs (VALS_mt6 res nb sh)) in *. destruct P as [mt6_R8 mt6_R9 mt6_R10 mt6_R19 mt6_rng_res mt6_rng_nb mt6_rng_sh mt6_kw3 mt6_kw4 mt6_kwr5 mt6_kwr6].
  assert (Z32 : bv_unsigned (ev E 32) = res) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = nb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sh) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x51ec0; 0x53328] AXF_mt6.scr_pmt6r 0x51dd8 AXF_mt6.sr_mt6 AXF_mt6.kn_mt6 35 _ _ _ E m rom regs AXF_mt6.RES_pmt6r_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mt6.RES_pmt6r fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mt6_mem_pmt6r m regs res nb sh) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mt6_mem_pmt6r. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    split; [first [zpost_reg HR' | (srg HR'; rewrite zeval_sound; cbn [zeval edenot]; repeat dsc_rw; repeat dsc_mod; litmods; rewrite (Z.mod_small sh 64) by lia; reflexivity)]|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MT6.
End AXF_mt6z.

Module AXF_mt7.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_nb := EVar 32.
Definition sr_mt7 := (sr_upd (sr_upd (sr_upd sr_id 8 (ELit 4096)) 9 (e_nb)) 19 (ELit 614096)).
Definition kn_mt7 : list kentry :=
  [ KRange e_nb 8192 (2^47);
    KWr (SA (ELit 0) 615024) (ELit 8);
    KWr (SA (ELit 0) 614144) (ELit 8) ].
Definition scr_mt7 : scripts := SCR [] [] [].
Definition ss_mt7 := SS 0x51e34 sr_mt7 [] kn_mt7 33.
Definition RUN_mt7 := sym_exec SEGS 100 true [0x51ec0] scr_mt7 ss_mt7 [].

Definition scr_pmt7 : scripts := SCR [] [] [].
Definition RES_pmt7 := Eval vm_compute in sym_exec SEGS 100 true [0x51ec0] scr_pmt7 ss_mt7 [].
Lemma RES_pmt7_ok : sym_exec SEGS 100 true [0x51ec0] scr_pmt7 (SS 0x51e34 sr_mt7 [] kn_mt7 33) [] = RES_pmt7.
Proof. vm_compute. reflexivity. Qed.
End AXF_mt7.

Module AXF_mt7z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section MT7.
Context {fx : FPState}.

Definition VALS_mt7 (nb : Z) : list Z := [nb].

Record mt7_pre (regs : bvmap 5 word) (m : word -> option byte) (nb : Z) : Prop := {
  mt7_R8 : getr regs 8 = wa 4096 ;
  mt7_R9 : getr regs 9 = wa nb ;
  mt7_R19 : getr regs 19 = wa 614096 ;
  mt7_rng_nb : 8192 <= nb <= 2^47 ;
  mt7_kwr1 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (0 + 615024 + d)) k = true ;
  mt7_kwr2 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (0 + 614144 + d)) k = true
}.


#[using="Type"] Lemma mt7_setup : forall regs m nb, mt7_pre regs m nb ->
  regs_ok (Ez regs (VALS_mt7 nb)) AXF_mt7.sr_mt7 regs /\ know_ok SEGS (Ez regs (VALS_mt7 nb)) m AXF_mt7.kn_mt7.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m nb P. destruct P as [mt7_R8 mt7_R9 mt7_R19 mt7_rng_nb mt7_kwr1 mt7_kwr2].
  set (E := Ez regs (VALS_mt7 nb)).
  assert (Z32 : bv_unsigned (ev E 32) = nb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mt7.sr_mt7.
    apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|]|].
    - rewrite mt7_R8. reflexivity.
    - rewrite mt7_R9. reflexivity.
    - rewrite mt7_R19. reflexivity. }
  unfold know_ok, AXF_mt7.kn_mt7.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mt7.e_nb a_base a_off].
  all: rewrite ?Z32.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range nb _ _ mt7_rng_nb eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply mt7_kwr1 | apply mt7_kwr2]; assumption).
  all: try (clear - mt7_rng_nb; lia).
  all: first [lia].
Qed.


Definition mt7_mem_pmt7 (m : word -> option byte) (regs : bvmap 5 word) (nb : Z) : word -> option byte :=
  wbytes (wbytes (m) (wa (0 + 615024)) (word_to_le_bytes 8 (wa nb))) (wa (0 + 614144)) (word_to_le_bytes 8 (wa 1)).

#[using="Type"] Theorem mt7_pmt7 : forall regs m rom nb, mt7_pre regs m nb ->
  scs_denot SEGS m (Ez regs (VALS_mt7 nb)) (snd (fst AXF_mt7.RES_pmt7)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51e34) m rom) (mkst R (wa 0x51ec0) (mt7_mem_pmt7 m regs nb) rom) /\
    getr R 8 = wa 1 /\ getr R 9 = wa (nb + -4096) /\ getr R 19 = wa 614096 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom nb P Hsc. destruct (mt7_setup regs m nb P) as [HR HK].
  set (E := Ez regs (VALS_mt7 nb)) in *. destruct P as [mt7_R8 mt7_R9 mt7_R19 mt7_rng_nb mt7_kwr1 mt7_kwr2].
  assert (Z32 : bv_unsigned (ev E 32) = nb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x51ec0] AXF_mt7.scr_pmt7 0x51e34 AXF_mt7.sr_mt7 AXF_mt7.kn_mt7 33 _ _ _ E m rom regs AXF_mt7.RES_pmt7_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mt7.RES_pmt7 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mt7_mem_pmt7 m regs nb) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mt7_mem_pmt7. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MT7.
End AXF_mt7z.

Module AXF_mt8b.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_p := EVar 32.
Definition sr_mt8b := (sr_upd (sr_upd sr_id 8 (ELit 4096)) 9 (e_p)).
Definition kn_mt8b : list kentry :=
  [ KRange e_p 4096 (2^47);
    KAlign e_p 4096 ].
Definition scr_mt8b : scripts := SCR [true] [] [].
Definition ss_mt8b := SS 0x51eb4 sr_mt8b [] kn_mt8b 33.
Definition RUN_mt8b := sym_exec SEGS 100 true [0x53414] scr_mt8b ss_mt8b [].

Definition scr_pmt8b : scripts := SCR [true] [] [].
Definition RES_pmt8b := Eval vm_compute in sym_exec SEGS 100 true [0x53414] scr_pmt8b ss_mt8b [].
Lemma RES_pmt8b_ok : sym_exec SEGS 100 true [0x53414] scr_pmt8b (SS 0x51eb4 sr_mt8b [] kn_mt8b 33) [] = RES_pmt8b.
Proof. vm_compute. reflexivity. Qed.
End AXF_mt8b.

Module AXF_mt8bz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section MT8B.
Context {fx : FPState}.

Definition VALS_mt8b (p : Z) : list Z := [p].

Record mt8b_pre (regs : bvmap 5 word) (m : word -> option byte) (p : Z) : Prop := {
  mt8b_R8 : getr regs 8 = wa 4096 ;
  mt8b_R9 : getr regs 9 = wa p ;
  mt8b_rng_p : 4096 <= p <= 2^47 ;
  mt8b_ka1 : p mod 4096 = 0
}.


#[using="Type"] Lemma mt8b_setup : forall regs m p, mt8b_pre regs m p ->
  regs_ok (Ez regs (VALS_mt8b p)) AXF_mt8b.sr_mt8b regs /\ know_ok SEGS (Ez regs (VALS_mt8b p)) m AXF_mt8b.kn_mt8b.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m p P. destruct P as [mt8b_R8 mt8b_R9 mt8b_rng_p mt8b_ka1].
  set (E := Ez regs (VALS_mt8b p)).
  assert (Z32 : bv_unsigned (ev E 32) = p) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mt8b.sr_mt8b.
    apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|].
    - rewrite mt8b_R8. reflexivity.
    - rewrite mt8b_R9. reflexivity. }
  unfold know_ok, AXF_mt8b.kn_mt8b.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mt8b.e_p a_base a_off].
  all: rewrite ?Z32.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range p _ _ mt8b_rng_p eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - mt8b_rng_p mt8b_ka1; lia).
  all: first [lia].
Qed.


Definition mt8b_mem_pmt8b (m : word -> option byte) (regs : bvmap 5 word) (p : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mt8b_pmt8b : forall regs m rom p, mt8b_pre regs m p ->
  scs_denot SEGS m (Ez regs (VALS_mt8b p)) (snd (fst AXF_mt8b.RES_pmt8b)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51eb4) m rom) (mkst R (wa 0x53414) (mt8b_mem_pmt8b m regs p) rom) /\
    getr R 1 = wa 335712 /\ getr R 8 = wa 4096 /\ getr R 9 = wa p /\ getr R 10 = wa p /\ getr R 11 = wa 4096 /\ getr R 12 = wa 3 /\ (forall k, In k [2; 3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom p P Hsc. destruct (mt8b_setup regs m p P) as [HR HK].
  set (E := Ez regs (VALS_mt8b p)) in *. destruct P as [mt8b_R8 mt8b_R9 mt8b_rng_p mt8b_ka1].
  assert (Z32 : bv_unsigned (ev E 32) = p) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53414] AXF_mt8b.scr_pmt8b 0x51eb4 AXF_mt8b.sr_mt8b AXF_mt8b.kn_mt8b 33 _ _ _ E m rom regs AXF_mt8b.RES_pmt8b_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mt8b.RES_pmt8b fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mt8b_mem_pmt8b m regs p) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mt8b_mem_pmt8b. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MT8B.
End AXF_mt8bz.

Module AXF_mt8x.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_p := EVar 32.
Definition e_sh := EVar 33.
Definition e_n := EVar 34.
Definition sr_mt8x := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 8 (ELit 4096)) 9 (e_n)) 10 (e_p)) 19 (ELit 614096)) 20 (ELit 18446744073709551615)).
Definition kn_mt8x : list kentry :=
  [ KRange e_p 4096 (2^47);
    KAlign e_p 4096;
    KRange e_sh 0 40;
    KRange e_n 2 (2^41);
    KWord (SA (ELit 0) 614152) 8 e_sh;
    KWr (SA (ELit 0) 614144) (ELit 16);
    KWr (SA (ELit 0) 614176) (ELit 8) ].
Definition scr_mt8x : scripts := SCR [false] [] [].
Definition ss_mt8x := SS 0x51e8c sr_mt8x [] kn_mt8x 35.
Definition RUN_mt8x := sym_exec SEGS 100 true [0x53414] scr_mt8x ss_mt8x [].

Definition scr_pmt8x : scripts := SCR [false] [] [].
Definition RES_pmt8x := Eval vm_compute in sym_exec SEGS 100 true [0x53414] scr_pmt8x ss_mt8x [].
Lemma RES_pmt8x_ok : sym_exec SEGS 100 true [0x53414] scr_pmt8x (SS 0x51e8c sr_mt8x [] kn_mt8x 35) [] = RES_pmt8x.
Proof. vm_compute. reflexivity. Qed.
End AXF_mt8x.

Module AXF_mt8xz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section MT8X.
Context {fx : FPState}.

Definition VALS_mt8x (p sh n : Z) : list Z := [p; sh; n].

Record mt8x_pre (regs : bvmap 5 word) (m : word -> option byte) (p sh n : Z) : Prop := {
  mt8x_R8 : getr regs 8 = wa 4096 ;
  mt8x_R9 : getr regs 9 = wa n ;
  mt8x_R10 : getr regs 10 = wa p ;
  mt8x_R19 : getr regs 19 = wa 614096 ;
  mt8x_R20 : getr regs 20 = wa 18446744073709551615 ;
  mt8x_rng_p : 4096 <= p <= 2^47 ;
  mt8x_rng_sh : 0 <= sh <= 40 ;
  mt8x_rng_n : 2 <= n <= 2^41 ;
  mt8x_ka1 : p mod 4096 = 0 ;
  mt8x_kw4 : rdn SEGS m (wa (0 + 614152)) 8 = Some (word_to_le_bytes 8 (wa sh)) ;
  mt8x_kwr5 : forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS m (wa (0 + 614144 + d)) k = true ;
  mt8x_kwr6 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (0 + 614176 + d)) k = true
}.


#[using="Type"] Lemma mt8x_setup : forall regs m p sh n, mt8x_pre regs m p sh n ->
  regs_ok (Ez regs (VALS_mt8x p sh n)) AXF_mt8x.sr_mt8x regs /\ know_ok SEGS (Ez regs (VALS_mt8x p sh n)) m AXF_mt8x.kn_mt8x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m p sh n P. destruct P as [mt8x_R8 mt8x_R9 mt8x_R10 mt8x_R19 mt8x_R20 mt8x_rng_p mt8x_rng_sh mt8x_rng_n mt8x_ka1 mt8x_kw4 mt8x_kwr5 mt8x_kwr6].
  set (E := Ez regs (VALS_mt8x p sh n)).
  assert (Z32 : bv_unsigned (ev E 32) = p) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sh) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mt8x.sr_mt8x.
    apply (regs_ok_pin E _ regs 20); [apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|]|]|]|].
    - rewrite mt8x_R8. reflexivity.
    - rewrite mt8x_R9. reflexivity.
    - rewrite mt8x_R10. reflexivity.
    - rewrite mt8x_R19. reflexivity.
    - rewrite mt8x_R20. reflexivity. }
  unfold know_ok, AXF_mt8x.kn_mt8x.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mt8x.e_p AXF_mt8x.e_sh AXF_mt8x.e_n a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range p _ _ mt8x_rng_p eq_refl eq_refl), ?(mod64_of_range sh _ _ mt8x_rng_sh eq_refl eq_refl), ?(mod64_of_range n _ _ mt8x_rng_n eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply mt8x_kwr5 | apply mt8x_kwr6]; assumption).
  all: try (clear - mt8x_rng_p mt8x_rng_sh mt8x_rng_n mt8x_ka1; lia).
  all: first [lia].
Qed.


Definition mt8x_mem_pmt8x (m : word -> option byte) (regs : bvmap 5 word) (p sh n : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (m) (wa (0 + 614144)) (word_to_le_bytes 8 (wa (n + -1)))) (wa (0 + 614152)) (word_to_le_bytes 8 (wa (sh + 1)))) (wa (0 + 614176)) (word_to_le_bytes 8 (wa (p + 4096))).

#[using="Type"] Theorem mt8x_pmt8x : forall regs m rom p sh n, mt8x_pre regs m p sh n ->
  scs_denot SEGS m (Ez regs (VALS_mt8x p sh n)) (snd (fst AXF_mt8x.RES_pmt8x)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51e8c) m rom) (mkst R (wa 0x53414) (mt8x_mem_pmt8x m regs p sh n) rom) /\
    getr R 1 = wa 335712 /\ getr R 8 = wa 4096 /\ getr R 9 = wa (p + 4096) /\ getr R 10 = wa (p + 4096) /\ getr R 11 = wa 4096 /\ getr R 12 = wa 3 /\ getr R 19 = wa 614096 /\ getr R 20 = wa 18446744073709551615 /\ (forall k, In k [2; 3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 18; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom p sh n P Hsc. destruct (mt8x_setup regs m p sh n P) as [HR HK].
  set (E := Ez regs (VALS_mt8x p sh n)) in *. destruct P as [mt8x_R8 mt8x_R9 mt8x_R10 mt8x_R19 mt8x_R20 mt8x_rng_p mt8x_rng_sh mt8x_rng_n mt8x_ka1 mt8x_kw4 mt8x_kwr5 mt8x_kwr6].
  assert (Z32 : bv_unsigned (ev E 32) = p) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sh) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53414] AXF_mt8x.scr_pmt8x 0x51e8c AXF_mt8x.sr_mt8x AXF_mt8x.kn_mt8x 35 _ _ _ E m rom regs AXF_mt8x.RES_pmt8x_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mt8x.RES_pmt8x fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mt8x_mem_pmt8x m regs p sh n) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mt8x_mem_pmt8x. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MT8X.
End AXF_mt8xz.

Module AXF_mt9.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_d := EVar 32.
Definition sr_mt9 := (sr_upd sr_id 10 (ELit 0)).
Definition kn_mt9 : list kentry :=
  [  ].
Definition scr_mt9 : scripts := SCR [true] [] [].
Definition ss_mt9 := SS 0x51f60 sr_mt9 [] kn_mt9 33.
Definition RUN_mt9 := sym_exec SEGS 100 true [0x51ec0] scr_mt9 ss_mt9 [].

Definition scr_pmt9 : scripts := SCR [true] [] [].
Definition RES_pmt9 := Eval vm_compute in sym_exec SEGS 100 true [0x51ec0] scr_pmt9 ss_mt9 [].
Lemma RES_pmt9_ok : sym_exec SEGS 100 true [0x51ec0] scr_pmt9 (SS 0x51f60 sr_mt9 [] kn_mt9 33) [] = RES_pmt9.
Proof. vm_compute. reflexivity. Qed.
End AXF_mt9.

Module AXF_mt9z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section MT9.
Context {fx : FPState}.

Definition VALS_mt9 (d : Z) : list Z := [d].

Record mt9_pre (regs : bvmap 5 word) (m : word -> option byte) (d : Z) : Prop := {
  mt9_R10 : getr regs 10 = wa 0 ;
  mt9_rng_d : 0 <= d <= 1
}.


#[using="Type"] Lemma mt9_setup : forall regs m d, mt9_pre regs m d ->
  regs_ok (Ez regs (VALS_mt9 d)) AXF_mt9.sr_mt9 regs /\ know_ok SEGS (Ez regs (VALS_mt9 d)) m AXF_mt9.kn_mt9.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m d P. destruct P as [mt9_R10 mt9_rng_d].
  set (E := Ez regs (VALS_mt9 d)).
  assert (Z32 : bv_unsigned (ev E 32) = d) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mt9.sr_mt9.
    apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|].
    - rewrite mt9_R10. reflexivity. }
  unfold know_ok, AXF_mt9.kn_mt9.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mt9.e_d a_base a_off].
  all: rewrite ?Z32.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range d _ _ mt9_rng_d eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - mt9_rng_d; lia).
  all: first [lia].
Qed.


Definition mt9_mem_pmt9 (m : word -> option byte) (regs : bvmap 5 word) (d : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mt9_pmt9 : forall regs m rom d, mt9_pre regs m d ->
  scs_denot SEGS m (Ez regs (VALS_mt9 d)) (snd (fst AXF_mt9.RES_pmt9)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51f60) m rom) (mkst R (wa 0x51ec0) (mt9_mem_pmt9 m regs d) rom) /\
    getr R 10 = wa 0 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom d P Hsc. destruct (mt9_setup regs m d P) as [HR HK].
  set (E := Ez regs (VALS_mt9 d)) in *. destruct P as [mt9_R10 mt9_rng_d].
  assert (Z32 : bv_unsigned (ev E 32) = d) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x51ec0] AXF_mt9.scr_pmt9 0x51f60 AXF_mt9.sr_mt9 AXF_mt9.kn_mt9 33 _ _ _ E m rom regs AXF_mt9.RES_pmt9_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mt9.RES_pmt9 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mt9_mem_pmt9 m regs d) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mt9_mem_pmt9. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MT9.
End AXF_mt9z.

Module AXF_mte.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_mt := EVar 32.
Definition e_can := EVar 33.
Definition e_sp0 := EVar 34.
Definition e_s00 := EVar 35.
Definition e_s10 := EVar 36.
Definition e_s20 := EVar 37.
Definition e_s30 := EVar 38.
Definition e_s40 := EVar 39.
Definition sr_mte := (sr_upd (sr_upd (sr_upd sr_id 2 (EAlu ALU_ADD e_sp0 (ELit (-64)))) 10 (e_mt)) 18 (ELit 613952)).
Definition kn_mte : list kentry :=
  [ KRange e_mt 1 (2^63-1);
    KAlign e_mt 8;
    KRange e_can 0 (2^64-1);
    KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KRange e_s00 0 (2^64-1);
    KRange e_s10 0 (2^64-1);
    KRange e_s20 0 (2^64-1);
    KRange e_s30 0 (2^64-1);
    KRange e_s40 0 (2^64-1);
    KWord (SA (ELit 0) 613952) 8 e_can;
    KWord (SA e_sp0 (-56)) 8 e_can;
    KWord (SA e_sp0 (-8)) 8 (ELit 337128);
    KWord (SA e_sp0 (-16)) 8 e_s00;
    KWord (SA e_sp0 (-24)) 8 e_s10;
    KWord (SA e_sp0 (-32)) 8 e_s20;
    KWord (SA e_sp0 (-40)) 8 e_s30;
    KWord (SA e_sp0 (-48)) 8 e_s40;
    KWr (SA e_mt 0) (ELit 16);
    KDisj (SA e_mt 0) (ELit 16) (SA e_sp0 (-56)) (ELit 56);
    KDisj (SA e_mt 0) (ELit 16) (SA (ELit 0) 613952) (ELit 8) ].
Definition scr_mte : scripts := SCR [false] [] [].
Definition ss_mte := SS 0x51f1c sr_mte [] kn_mte 40.
Definition RUN_mte := sym_exec SEGS 100 true [0x524e8] scr_mte ss_mte [].

Definition scr_pmte : scripts := SCR [false] [] [].
Definition RES_pmte := Eval vm_compute in sym_exec SEGS 100 true [0x524e8] scr_pmte ss_mte [].
Lemma RES_pmte_ok : sym_exec SEGS 100 true [0x524e8] scr_pmte (SS 0x51f1c sr_mte [] kn_mte 40) [] = RES_pmte.
Proof. vm_compute. reflexivity. Qed.
End AXF_mte.

Module AXF_mted.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_mt := EVar 32.
Definition e_can := EVar 33.
Definition e_sp0 := EVar 34.
Definition e_s00 := EVar 35.
Definition e_s10 := EVar 36.
Definition e_s20 := EVar 37.
Definition e_s30 := EVar 38.
Definition e_s40 := EVar 39.
Definition sr_mted := (sr_upd (sr_upd (sr_upd sr_id 2 (EAlu ALU_ADD e_sp0 (ELit (-64)))) 10 (e_mt)) 18 (ELit 613952)).
Definition kn_mted : list kentry :=
  [ KRange e_mt 1 (2^63-1);
    KAlign e_mt 8;
    KRange e_can 0 (2^64-1);
    KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KRange e_s00 0 (2^64-1);
    KRange e_s10 0 (2^64-1);
    KRange e_s20 0 (2^64-1);
    KRange e_s30 0 (2^64-1);
    KRange e_s40 0 (2^64-1);
    KWord (SA (ELit 0) 613952) 8 e_can;
    KWord (SA e_sp0 (-56)) 8 e_can;
    KWord (SA e_sp0 (-8)) 8 (ELit 336140);
    KWord (SA e_sp0 (-16)) 8 e_s00;
    KWord (SA e_sp0 (-24)) 8 e_s10;
    KWord (SA e_sp0 (-32)) 8 e_s20;
    KWord (SA e_sp0 (-40)) 8 e_s30;
    KWord (SA e_sp0 (-48)) 8 e_s40;
    KWr (SA e_mt 0) (ELit 16);
    KDisj (SA e_mt 0) (ELit 16) (SA e_sp0 (-56)) (ELit 56);
    KDisj (SA e_mt 0) (ELit 16) (SA (ELit 0) 613952) (ELit 8) ].
Definition scr_mted : scripts := SCR [false] [] [].
Definition ss_mted := SS 0x51f1c sr_mted [] kn_mted 40.
Definition RUN_mted := sym_exec SEGS 100 true [0x5210c] scr_mted ss_mted [].

Definition scr_pmted : scripts := SCR [false] [] [].
Definition RES_pmted := Eval vm_compute in sym_exec SEGS 100 true [0x5210c] scr_pmted ss_mted [].
Lemma RES_pmted_ok : sym_exec SEGS 100 true [0x5210c] scr_pmted (SS 0x51f1c sr_mted [] kn_mted 40) [] = RES_pmted.
Proof. vm_compute. reflexivity. Qed.
End AXF_mted.

Module AXF_mtedz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section MTED.
Context {fx : FPState}.

Definition VALS_mted (mt can sp0 s00 s10 s20 s30 s40 : Z) : list Z := [mt; can; sp0; s00; s10; s20; s30; s40].

Record mted_pre (regs : bvmap 5 word) (m : word -> option byte) (mt can sp0 s00 s10 s20 s30 s40 : Z) : Prop := {
  mted_R2 : getr regs 2 = wa (sp0 + -64) ;
  mted_R10 : getr regs 10 = wa mt ;
  mted_R18 : getr regs 18 = wa 613952 ;
  mted_rng_mt : 1 <= mt <= 2^63-1 ;
  mted_rng_can : 0 <= can <= 2^64-1 ;
  mted_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  mted_rng_s00 : 0 <= s00 <= 2^64-1 ;
  mted_rng_s10 : 0 <= s10 <= 2^64-1 ;
  mted_rng_s20 : 0 <= s20 <= 2^64-1 ;
  mted_rng_s30 : 0 <= s30 <= 2^64-1 ;
  mted_rng_s40 : 0 <= s40 <= 2^64-1 ;
  mted_ka1 : mt mod 8 = 0 ;
  mted_ka4 : sp0 mod 16 = 0 ;
  mted_kw10 : rdn SEGS m (wa (0 + 613952)) 8 = Some (word_to_le_bytes 8 (wa can)) ;
  mted_kw11 : rdn SEGS m (wa (sp0 + -56)) 8 = Some (word_to_le_bytes 8 (wa can)) ;
  mted_kw12 : rdn SEGS m (wa (sp0 + -8)) 8 = Some (word_to_le_bytes 8 (wa 336140)) ;
  mted_kw13 : rdn SEGS m (wa (sp0 + -16)) 8 = Some (word_to_le_bytes 8 (wa s00)) ;
  mted_kw14 : rdn SEGS m (wa (sp0 + -24)) 8 = Some (word_to_le_bytes 8 (wa s10)) ;
  mted_kw15 : rdn SEGS m (wa (sp0 + -32)) 8 = Some (word_to_le_bytes 8 (wa s20)) ;
  mted_kw16 : rdn SEGS m (wa (sp0 + -40)) 8 = Some (word_to_le_bytes 8 (wa s30)) ;
  mted_kw17 : rdn SEGS m (wa (sp0 + -48)) 8 = Some (word_to_le_bytes 8 (wa s40)) ;
  mted_kwr18 : forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS m (wa (mt + 0 + d)) k = true ;
  mted_kd19 : mt + 0 + 16 <= sp0 + -56 \/ sp0 + -56 + 56 <= mt + 0 ;
  mted_kd20 : mt + 0 + 16 <= 0 + 613952 \/ 0 + 613952 + 8 <= mt + 0
}.


#[using="Type"] Lemma mted_setup : forall regs m mt can sp0 s00 s10 s20 s30 s40, mted_pre regs m mt can sp0 s00 s10 s20 s30 s40 ->
  regs_ok (Ez regs (VALS_mted mt can sp0 s00 s10 s20 s30 s40)) AXF_mted.sr_mted regs /\ know_ok SEGS (Ez regs (VALS_mted mt can sp0 s00 s10 s20 s30 s40)) m AXF_mted.kn_mted.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m mt can sp0 s00 s10 s20 s30 s40 P. destruct P as [mted_R2 mted_R10 mted_R18 mted_rng_mt mted_rng_can mted_rng_sp0 mted_rng_s00 mted_rng_s10 mted_rng_s20 mted_rng_s30 mted_rng_s40 mted_ka1 mted_ka4 mted_kw10 mted_kw11 mted_kw12 mted_kw13 mted_kw14 mted_kw15 mted_kw16 mted_kw17 mted_kwr18 mted_kd19 mted_kd20].
  set (E := Ez regs (VALS_mted mt can sp0 s00 s10 s20 s30 s40)).
  assert (Z32 : bv_unsigned (ev E 32) = mt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = can) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = s00) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = s10) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = s20) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = s30) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = s40) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mted.sr_mted.
    apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 2); [apply regs_ok_id|]|]|].
    - rewrite mted_R2, zeval_sound. cbn [zeval edenot AXF_mted.e_mt AXF_mted.e_can AXF_mted.e_sp0 AXF_mted.e_s00 AXF_mted.e_s10 AXF_mted.e_s20 AXF_mted.e_s30 AXF_mted.e_s40]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite mted_R10. reflexivity.
    - rewrite mted_R18. reflexivity. }
  unfold know_ok, AXF_mted.kn_mted.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mted.e_mt AXF_mted.e_can AXF_mted.e_sp0 AXF_mted.e_s00 AXF_mted.e_s10 AXF_mted.e_s20 AXF_mted.e_s30 AXF_mted.e_s40 a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range mt _ _ mted_rng_mt eq_refl eq_refl), ?(mod64_of_range sp0 _ _ mted_rng_sp0 eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply mted_kwr18]; assumption).
  all: try (clear - mted_rng_mt mted_rng_can mted_rng_sp0 mted_rng_s00 mted_rng_s10 mted_rng_s20 mted_rng_s30 mted_rng_s40 mted_ka1 mted_ka4; lia).
  all: first [(clear - mted_rng_mt mted_rng_can mted_rng_sp0 mted_rng_s00 mted_rng_s10 mted_rng_s20 mted_rng_s30 mted_rng_s40 mted_ka1 mted_ka4 mted_kd19; lia) | (clear - mted_rng_mt mted_rng_can mted_rng_sp0 mted_rng_s00 mted_rng_s10 mted_rng_s20 mted_rng_s30 mted_rng_s40 mted_ka1 mted_ka4 mted_kd20; lia) | lia].
Qed.


Definition mted_mem_pmted (m : word -> option byte) (regs : bvmap 5 word) (mt can sp0 s00 s10 s20 s30 s40 : Z) : word -> option byte :=
  wbytes (wbytes (m) (wa (mt + 8)) (word_to_le_bytes 8 (wa 0))) (wa (mt + 0)) (word_to_le_bytes 8 (wa 0)).

#[using="Type"] Theorem mted_pmted : forall regs m rom mt can sp0 s00 s10 s20 s30 s40, mted_pre regs m mt can sp0 s00 s10 s20 s30 s40 ->
  scs_denot SEGS m (Ez regs (VALS_mted mt can sp0 s00 s10 s20 s30 s40)) (snd (fst AXF_mted.RES_pmted)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51f1c) m rom) (mkst R (wa 0x5210c) (mted_mem_pmted m regs mt can sp0 s00 s10 s20 s30 s40) rom) /\
    getr R 1 = wa 336140 /\ getr R 2 = wa sp0 /\ getr R 8 = wa s00 /\ getr R 9 = wa s10 /\ getr R 10 = wa mt /\ getr R 11 = wa can /\ getr R 12 = wa can /\ getr R 18 = wa s20 /\ getr R 19 = wa s30 /\ getr R 20 = wa s40 /\ (forall k, In k [3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom mt can sp0 s00 s10 s20 s30 s40 P Hsc. destruct (mted_setup regs m mt can sp0 s00 s10 s20 s30 s40 P) as [HR HK].
  set (E := Ez regs (VALS_mted mt can sp0 s00 s10 s20 s30 s40)) in *. destruct P as [mted_R2 mted_R10 mted_R18 mted_rng_mt mted_rng_can mted_rng_sp0 mted_rng_s00 mted_rng_s10 mted_rng_s20 mted_rng_s30 mted_rng_s40 mted_ka1 mted_ka4 mted_kw10 mted_kw11 mted_kw12 mted_kw13 mted_kw14 mted_kw15 mted_kw16 mted_kw17 mted_kwr18 mted_kd19 mted_kd20].
  assert (Z32 : bv_unsigned (ev E 32) = mt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = can) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = s00) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = s10) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = s20) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = s30) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = s40) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x5210c] AXF_mted.scr_pmted 0x51f1c AXF_mted.sr_mted AXF_mted.kn_mted 40 _ _ _ E m rom regs AXF_mted.RES_pmted_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mted.RES_pmted fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mted_mem_pmted m regs mt can sp0 s00 s10 s20 s30 s40) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mted_mem_pmted. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MTED.
End AXF_mtedz.

Module AXF_mtez.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section MTE.
Context {fx : FPState}.

Definition VALS_mte (mt can sp0 s00 s10 s20 s30 s40 : Z) : list Z := [mt; can; sp0; s00; s10; s20; s30; s40].

Record mte_pre (regs : bvmap 5 word) (m : word -> option byte) (mt can sp0 s00 s10 s20 s30 s40 : Z) : Prop := {
  mte_R2 : getr regs 2 = wa (sp0 + -64) ;
  mte_R10 : getr regs 10 = wa mt ;
  mte_R18 : getr regs 18 = wa 613952 ;
  mte_rng_mt : 1 <= mt <= 2^63-1 ;
  mte_rng_can : 0 <= can <= 2^64-1 ;
  mte_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  mte_rng_s00 : 0 <= s00 <= 2^64-1 ;
  mte_rng_s10 : 0 <= s10 <= 2^64-1 ;
  mte_rng_s20 : 0 <= s20 <= 2^64-1 ;
  mte_rng_s30 : 0 <= s30 <= 2^64-1 ;
  mte_rng_s40 : 0 <= s40 <= 2^64-1 ;
  mte_ka1 : mt mod 8 = 0 ;
  mte_ka4 : sp0 mod 16 = 0 ;
  mte_kw10 : rdn SEGS m (wa (0 + 613952)) 8 = Some (word_to_le_bytes 8 (wa can)) ;
  mte_kw11 : rdn SEGS m (wa (sp0 + -56)) 8 = Some (word_to_le_bytes 8 (wa can)) ;
  mte_kw12 : rdn SEGS m (wa (sp0 + -8)) 8 = Some (word_to_le_bytes 8 (wa 337128)) ;
  mte_kw13 : rdn SEGS m (wa (sp0 + -16)) 8 = Some (word_to_le_bytes 8 (wa s00)) ;
  mte_kw14 : rdn SEGS m (wa (sp0 + -24)) 8 = Some (word_to_le_bytes 8 (wa s10)) ;
  mte_kw15 : rdn SEGS m (wa (sp0 + -32)) 8 = Some (word_to_le_bytes 8 (wa s20)) ;
  mte_kw16 : rdn SEGS m (wa (sp0 + -40)) 8 = Some (word_to_le_bytes 8 (wa s30)) ;
  mte_kw17 : rdn SEGS m (wa (sp0 + -48)) 8 = Some (word_to_le_bytes 8 (wa s40)) ;
  mte_kwr18 : forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS m (wa (mt + 0 + d)) k = true ;
  mte_kd19 : mt + 0 + 16 <= sp0 + -56 \/ sp0 + -56 + 56 <= mt + 0 ;
  mte_kd20 : mt + 0 + 16 <= 0 + 613952 \/ 0 + 613952 + 8 <= mt + 0
}.


#[using="Type"] Lemma mte_setup : forall regs m mt can sp0 s00 s10 s20 s30 s40, mte_pre regs m mt can sp0 s00 s10 s20 s30 s40 ->
  regs_ok (Ez regs (VALS_mte mt can sp0 s00 s10 s20 s30 s40)) AXF_mte.sr_mte regs /\ know_ok SEGS (Ez regs (VALS_mte mt can sp0 s00 s10 s20 s30 s40)) m AXF_mte.kn_mte.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m mt can sp0 s00 s10 s20 s30 s40 P. destruct P as [mte_R2 mte_R10 mte_R18 mte_rng_mt mte_rng_can mte_rng_sp0 mte_rng_s00 mte_rng_s10 mte_rng_s20 mte_rng_s30 mte_rng_s40 mte_ka1 mte_ka4 mte_kw10 mte_kw11 mte_kw12 mte_kw13 mte_kw14 mte_kw15 mte_kw16 mte_kw17 mte_kwr18 mte_kd19 mte_kd20].
  set (E := Ez regs (VALS_mte mt can sp0 s00 s10 s20 s30 s40)).
  assert (Z32 : bv_unsigned (ev E 32) = mt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = can) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = s00) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = s10) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = s20) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = s30) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = s40) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mte.sr_mte.
    apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 2); [apply regs_ok_id|]|]|].
    - rewrite mte_R2, zeval_sound. cbn [zeval edenot AXF_mte.e_mt AXF_mte.e_can AXF_mte.e_sp0 AXF_mte.e_s00 AXF_mte.e_s10 AXF_mte.e_s20 AXF_mte.e_s30 AXF_mte.e_s40]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite mte_R10. reflexivity.
    - rewrite mte_R18. reflexivity. }
  unfold know_ok, AXF_mte.kn_mte.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_mte.e_sp0 (wa sp0) 1024); [reflexivity | assumption | rewrite u_wa_small by lia; lia])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mte.e_mt AXF_mte.e_can AXF_mte.e_sp0 AXF_mte.e_s00 AXF_mte.e_s10 AXF_mte.e_s20 AXF_mte.e_s30 AXF_mte.e_s40 a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range mt _ _ mte_rng_mt eq_refl eq_refl), ?(mod64_of_range sp0 _ _ mte_rng_sp0 eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply mte_kwr18]; assumption).
  all: try (clear - mte_rng_mt mte_rng_can mte_rng_sp0 mte_rng_s00 mte_rng_s10 mte_rng_s20 mte_rng_s30 mte_rng_s40 mte_ka1 mte_ka4; lia).
  all: first [(clear - mte_rng_mt mte_rng_can mte_rng_sp0 mte_rng_s00 mte_rng_s10 mte_rng_s20 mte_rng_s30 mte_rng_s40 mte_ka1 mte_ka4 mte_kd19; lia) | (clear - mte_rng_mt mte_rng_can mte_rng_sp0 mte_rng_s00 mte_rng_s10 mte_rng_s20 mte_rng_s30 mte_rng_s40 mte_ka1 mte_ka4 mte_kd20; lia) | lia].
Qed.


Definition mte_mem_pmte (m : word -> option byte) (regs : bvmap 5 word) (mt can sp0 s00 s10 s20 s30 s40 : Z) : word -> option byte :=
  wbytes (wbytes (m) (wa (mt + 8)) (word_to_le_bytes 8 (wa 0))) (wa (mt + 0)) (word_to_le_bytes 8 (wa 0)).

#[using="Type"] Theorem mte_pmte : forall regs m rom mt can sp0 s00 s10 s20 s30 s40, mte_pre regs m mt can sp0 s00 s10 s20 s30 s40 ->
  scs_denot SEGS m (Ez regs (VALS_mte mt can sp0 s00 s10 s20 s30 s40)) (snd (fst AXF_mte.RES_pmte)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51f1c) m rom) (mkst R (wa 0x524e8) (mte_mem_pmte m regs mt can sp0 s00 s10 s20 s30 s40) rom) /\
    getr R 1 = wa 337128 /\ getr R 2 = wa sp0 /\ getr R 8 = wa s00 /\ getr R 9 = wa s10 /\ getr R 10 = wa mt /\ getr R 11 = wa can /\ getr R 12 = wa can /\ getr R 18 = wa s20 /\ getr R 19 = wa s30 /\ getr R 20 = wa s40 /\ (forall k, In k [3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom mt can sp0 s00 s10 s20 s30 s40 P Hsc. destruct (mte_setup regs m mt can sp0 s00 s10 s20 s30 s40 P) as [HR HK].
  set (E := Ez regs (VALS_mte mt can sp0 s00 s10 s20 s30 s40)) in *. destruct P as [mte_R2 mte_R10 mte_R18 mte_rng_mt mte_rng_can mte_rng_sp0 mte_rng_s00 mte_rng_s10 mte_rng_s20 mte_rng_s30 mte_rng_s40 mte_ka1 mte_ka4 mte_kw10 mte_kw11 mte_kw12 mte_kw13 mte_kw14 mte_kw15 mte_kw16 mte_kw17 mte_kwr18 mte_kd19 mte_kd20].
  assert (Z32 : bv_unsigned (ev E 32) = mt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = can) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = s00) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = s10) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = s20) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = s30) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = s40) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x524e8] AXF_mte.scr_pmte 0x51f1c AXF_mte.sr_mte AXF_mte.kn_mte 40 _ _ _ E m rom regs AXF_mte.RES_pmte_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mte.RES_pmte fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mte_mem_pmte m regs mt can sp0 s00 s10 s20 s30 s40) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mte_mem_pmte. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MTE.
End AXF_mtez.

Module AXF_sp0.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_sc := EVar 32.
Definition e_req := EVar 33.
Definition e_hd := EVar 34.
Definition e_can := EVar 35.
Definition e_sp0 := EVar 36.
Definition STK := SA e_sp0 (-1024).
Definition sr_sp0 := (sr_upd (sr_upd (sr_upd sr_id 2 (e_sp0)) 10 (e_sc)) 11 (e_req)).
Definition kn_sp0 : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KWr STK (ELit 1024);
    KRange e_sc 0 47;
    KRange e_req 0 (2^26);
    KWord (SA (ELit 0) 408992) 8 (ELit 613952);
    KWord (SA (ELit 0) 613952) 8 e_can;
    KWord (SA (EMd M_MUL (ELit 8) e_sc) 614184) 8 e_hd;
    KDisj STK (ELit 1024) (SA (ELit 0) 408992) (ELit 8);
    KDisj STK (ELit 1024) (SA (ELit 0) 613952) (ELit 8);
    KDisj STK (ELit 1024) (SA (EMd M_MUL (ELit 8) e_sc) 614184) (ELit 8) ].
Definition scr_sp0 : scripts := SCR [] [] [].
Definition ss_sp0 := SS 0x522f0 sr_sp0 [] kn_sp0 37.
Definition RUN_sp0 := sym_exec SEGS 100 true [0x52350] scr_sp0 ss_sp0 [].

Definition scr_psp0 : scripts := SCR [] [] [].
Definition RES_psp0 := Eval vm_compute in sym_exec SEGS 100 true [0x52350] scr_psp0 ss_sp0 [].
Lemma RES_psp0_ok : sym_exec SEGS 100 true [0x52350] scr_psp0 (SS 0x522f0 sr_sp0 [] kn_sp0 37) [] = RES_psp0.
Proof. vm_compute. reflexivity. Qed.
End AXF_sp0.

Module AXF_sp0z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section SP0.
Context {fx : FPState}.

Definition VALS_sp0 (sc req hd can sp0 : Z) : list Z := [sc; req; hd; can; sp0].

Record sp0_pre (regs : bvmap 5 word) (m : word -> option byte) (sc req hd can sp0 : Z) : Prop := {
  sp0_R2 : getr regs 2 = wa sp0 ;
  sp0_R10 : getr regs 10 = wa sc ;
  sp0_R11 : getr regs 11 = wa req ;
  sp0_HSTK : stk_ok SEGS m (wa sp0) 1024 ;
  sp0_rng_sc : 0 <= sc <= 47 ;
  sp0_rng_req : 0 <= req <= 2^26 ;
  sp0_rng_hd : 0 <= hd <= 2^64-1 ;
  sp0_rng_can : 0 <= can <= 2^64-1 ;
  sp0_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  sp0_ka1 : sp0 mod 16 = 0 ;
  sp0_kw5 : rdn SEGS m (wa (0 + 408992)) 8 = Some (word_to_le_bytes 8 (wa 613952)) ;
  sp0_kw6 : rdn SEGS m (wa (0 + 613952)) 8 = Some (word_to_le_bytes 8 (wa can)) ;
  sp0_kw7 : rdn SEGS m (wa (8 * sc + 614184)) 8 = Some (word_to_le_bytes 8 (wa hd)) ;
  sp0_kd8 : sp0 + -1024 + 1024 <= 0 + 408992 \/ 0 + 408992 + 8 <= sp0 + -1024 ;
  sp0_kd9 : sp0 + -1024 + 1024 <= 0 + 613952 \/ 0 + 613952 + 8 <= sp0 + -1024 ;
  sp0_kd10 : sp0 + -1024 + 1024 <= 8 * sc + 614184 \/ 8 * sc + 614184 + 8 <= sp0 + -1024
}.


#[using="Type"] Lemma sp0_setup : forall regs m sc req hd can sp0, sp0_pre regs m sc req hd can sp0 ->
  regs_ok (Ez regs (VALS_sp0 sc req hd can sp0)) AXF_sp0.sr_sp0 regs /\ know_ok SEGS (Ez regs (VALS_sp0 sc req hd can sp0)) m AXF_sp0.kn_sp0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sc req hd can sp0 P. destruct P as [sp0_R2 sp0_R10 sp0_R11 sp0_HSTK sp0_rng_sc sp0_rng_req sp0_rng_hd sp0_rng_can sp0_rng_sp0 sp0_ka1 sp0_kw5 sp0_kw6 sp0_kw7 sp0_kd8 sp0_kd9 sp0_kd10].
  set (E := Ez regs (VALS_sp0 sc req hd can sp0)).
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = req) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = hd) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = can) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_sp0.sr_sp0.
    apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 2); [apply regs_ok_id|]|]|].
    - rewrite sp0_R2. reflexivity.
    - rewrite sp0_R10. reflexivity.
    - rewrite sp0_R11. reflexivity. }
  unfold know_ok, AXF_sp0.kn_sp0.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_sp0.e_sp0 (wa sp0) 1024); [reflexivity | assumption | rewrite u_wa_small by lia; lia])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_sp0.e_sc AXF_sp0.e_req AXF_sp0.e_hd AXF_sp0.e_can AXF_sp0.e_sp0 AXF_sp0.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sc _ _ sp0_rng_sc eq_refl eq_refl), ?(mod64_of_range req _ _ sp0_rng_req eq_refl eq_refl), ?(mod64_of_range sp0 _ _ sp0_rng_sp0 eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - sp0_rng_sc sp0_rng_req sp0_rng_hd sp0_rng_can sp0_rng_sp0 sp0_ka1; lia).
  all: first [(clear - sp0_rng_sc sp0_rng_req sp0_rng_hd sp0_rng_can sp0_rng_sp0 sp0_ka1 sp0_kd8; lia) | (clear - sp0_rng_sc sp0_rng_req sp0_rng_hd sp0_rng_can sp0_rng_sp0 sp0_ka1 sp0_kd9; lia) | (clear - sp0_rng_sc sp0_rng_req sp0_rng_hd sp0_rng_can sp0_rng_sp0 sp0_ka1 sp0_kd10; lia) | lia].
Qed.


Definition sp0_mem_psp0 (m : word -> option byte) (regs : bvmap 5 word) (sc req hd can sp0 : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (sp0 + -8)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1))))))) (wa (sp0 + -16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))))) (wa (sp0 + -24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))))))) (wa (sp0 + -32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))))))) (wa (sp0 + -40)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))))) (wa (sp0 + -48)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 20))))))) (wa (sp0 + -56)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 21))))))) (wa (sp0 + -64)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 22))))))) (wa (sp0 + -72)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 23))))))) (wa (sp0 + -80)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 24))))))) (wa (sp0 + -88)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 25))))))) (wa (sp0 + -96)) (word_to_le_bytes 8 (wa can)).

#[using="Type"] Theorem sp0_psp0 : forall regs m rom sc req hd can sp0, sp0_pre regs m sc req hd can sp0 ->
  scs_denot SEGS m (Ez regs (VALS_sp0 sc req hd can sp0)) (snd (fst AXF_sp0.RES_psp0)) ->
  exists R, msteps SEGS (mkst regs (wa 0x522f0) m rom) (mkst R (wa 0x52350) (sp0_mem_psp0 m regs sc req hd can sp0) rom) /\
    getr R 2 = wa (sp0 + -144) /\ getr R 8 = wa sc /\ getr R 10 = wa can /\ getr R 11 = wa 615224 /\ getr R 12 = wa hd /\ getr R 18 = wa req /\ getr R 20 = wa 613952 /\ getr R 21 = wa ((8 * sc) + 614184) /\ getr R 22 = wa 614096 /\ getr R 23 = wa ((8 * sc) + 614096) /\ (forall k, In k [1; 3; 4; 5; 6; 7; 9; 13; 14; 15; 16; 17; 19; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc req hd can sp0 P Hsc. destruct (sp0_setup regs m sc req hd can sp0 P) as [HR HK].
  set (E := Ez regs (VALS_sp0 sc req hd can sp0)) in *. destruct P as [sp0_R2 sp0_R10 sp0_R11 sp0_HSTK sp0_rng_sc sp0_rng_req sp0_rng_hd sp0_rng_can sp0_rng_sp0 sp0_ka1 sp0_kw5 sp0_kw6 sp0_kw7 sp0_kd8 sp0_kd9 sp0_kd10].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = req) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = hd) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = can) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x52350] AXF_sp0.scr_psp0 0x522f0 AXF_sp0.sr_sp0 AXF_sp0.kn_sp0 37 _ _ _ E m rom regs AXF_sp0.RES_psp0_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_sp0.RES_psp0 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (sp0_mem_psp0 m regs sc req hd can sp0) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold sp0_mem_psp0. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End SP0.
End AXF_sp0z.

Module AXF_ta0.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_sc := EVar 32.
Definition sr_ta0 := (sr_upd sr_id 12 (ELit 0)).
Definition kn_ta0 : list kentry :=
  [ KRange e_sc 0 47 ].
Definition scr_ta0 : scripts := SCR [] [] [].
Definition ss_ta0 := SS 0x52350 sr_ta0 [] kn_ta0 33.
Definition RUN_ta0 := sym_exec SEGS 100 true [0x524d0] scr_ta0 ss_ta0 [].

Definition scr_pta0 : scripts := SCR [] [] [].
Definition RES_pta0 := Eval vm_compute in sym_exec SEGS 100 true [0x524d0] scr_pta0 ss_ta0 [].
Lemma RES_pta0_ok : sym_exec SEGS 100 true [0x524d0] scr_pta0 (SS 0x52350 sr_ta0 [] kn_ta0 33) [] = RES_pta0.
Proof. vm_compute. reflexivity. Qed.
End AXF_ta0.

Module AXF_ta0z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section TA0.
Context {fx : FPState}.

Definition VALS_ta0 (sc : Z) : list Z := [sc].

Record ta0_pre (regs : bvmap 5 word) (m : word -> option byte) (sc : Z) : Prop := {
  ta0_R12 : getr regs 12 = wa 0 ;
  ta0_rng_sc : 0 <= sc <= 47
}.


#[using="Type"] Lemma ta0_setup : forall regs m sc, ta0_pre regs m sc ->
  regs_ok (Ez regs (VALS_ta0 sc)) AXF_ta0.sr_ta0 regs /\ know_ok SEGS (Ez regs (VALS_ta0 sc)) m AXF_ta0.kn_ta0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sc P. destruct P as [ta0_R12 ta0_rng_sc].
  set (E := Ez regs (VALS_ta0 sc)).
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_ta0.sr_ta0.
    apply (regs_ok_pin E _ regs 12); [apply regs_ok_id|].
    - rewrite ta0_R12. reflexivity. }
  unfold know_ok, AXF_ta0.kn_ta0.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_ta0.e_sc a_base a_off].
  all: rewrite ?Z32.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sc _ _ ta0_rng_sc eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - ta0_rng_sc; lia).
  all: first [lia].
Qed.


Definition ta0_mem_pta0 (m : word -> option byte) (regs : bvmap 5 word) (sc : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem ta0_pta0 : forall regs m rom sc, ta0_pre regs m sc ->
  scs_denot SEGS m (Ez regs (VALS_ta0 sc)) (snd (fst AXF_ta0.RES_pta0)) ->
  exists R, msteps SEGS (mkst regs (wa 0x52350) m rom) (mkst R (wa 0x524d0) (ta0_mem_pta0 m regs sc) rom) /\
    getr R 12 = wa 0 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc P Hsc. destruct (ta0_setup regs m sc P) as [HR HK].
  set (E := Ez regs (VALS_ta0 sc)) in *. destruct P as [ta0_R12 ta0_rng_sc].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x524d0] AXF_ta0.scr_pta0 0x52350 AXF_ta0.sr_ta0 AXF_ta0.kn_ta0 33 _ _ _ E m rom regs AXF_ta0.RES_pta0_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_ta0.RES_pta0 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (ta0_mem_pta0 m regs sc) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold ta0_mem_pta0. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End TA0.
End AXF_ta0z.

Module AXF_ta1a.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_G := EVar 32.
Definition e_avail := EVar 33.
Definition sr_ta1a := (sr_upd sr_id 12 (e_G)).
Definition kn_ta1a : list kentry :=
  [ KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange e_avail 1 (2^32-1);
    KWord (SA e_G 24) 4 e_avail ].
Definition scr_ta1a : scripts := SCR [false] [] [].
Definition ss_ta1a := SS 0x52350 sr_ta1a [] kn_ta1a 34.
Definition RUN_ta1a := sym_exec SEGS 100 true [0x52490] scr_ta1a ss_ta1a [].

Definition scr_pta1a : scripts := SCR [false] [] [].
Definition RES_pta1a := Eval vm_compute in sym_exec SEGS 100 true [0x52490] scr_pta1a ss_ta1a [].
Lemma RES_pta1a_ok : sym_exec SEGS 100 true [0x52490] scr_pta1a (SS 0x52350 sr_ta1a [] kn_ta1a 34) [] = RES_pta1a.
Proof. vm_compute. reflexivity. Qed.
End AXF_ta1a.

Module AXF_ta1az.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section TA1A.
Context {fx : FPState}.

Definition VALS_ta1a (G avail : Z) : list Z := [G; avail].

Record ta1a_pre (regs : bvmap 5 word) (m : word -> option byte) (G avail : Z) : Prop := {
  ta1a_R12 : getr regs 12 = wa G ;
  ta1a_rng_G : 1 <= G <= 2^63-1 ;
  ta1a_rng_avail : 1 <= avail <= 2^32-1 ;
  ta1a_ka1 : G mod 8 = 0 ;
  ta1a_kw3 : rdn SEGS m (wa (G + 24)) 4 = Some (word_to_le_bytes 4 (wa avail))
}.


#[using="Type"] Lemma ta1a_setup : forall regs m G avail, ta1a_pre regs m G avail ->
  regs_ok (Ez regs (VALS_ta1a G avail)) AXF_ta1a.sr_ta1a regs /\ know_ok SEGS (Ez regs (VALS_ta1a G avail)) m AXF_ta1a.kn_ta1a.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G avail P. destruct P as [ta1a_R12 ta1a_rng_G ta1a_rng_avail ta1a_ka1 ta1a_kw3].
  set (E := Ez regs (VALS_ta1a G avail)).
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = avail) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_ta1a.sr_ta1a.
    apply (regs_ok_pin E _ regs 12); [apply regs_ok_id|].
    - rewrite ta1a_R12. reflexivity. }
  unfold know_ok, AXF_ta1a.kn_ta1a.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_ta1a.e_G AXF_ta1a.e_avail a_base a_off].
  all: rewrite ?Z32, ?Z33.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range G _ _ ta1a_rng_G eq_refl eq_refl), ?(mod64_of_range avail _ _ ta1a_rng_avail eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - ta1a_rng_G ta1a_rng_avail ta1a_ka1; lia).
  all: first [lia].
Qed.


Definition ta1a_mem_pta1a (m : word -> option byte) (regs : bvmap 5 word) (G avail : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem ta1a_pta1a : forall regs m rom G avail, ta1a_pre regs m G avail ->
  scs_denot SEGS m (Ez regs (VALS_ta1a G avail)) (snd (fst AXF_ta1a.RES_pta1a)) ->
  exists R, msteps SEGS (mkst regs (wa 0x52350) m rom) (mkst R (wa 0x52490) (ta1a_mem_pta1a m regs G avail) rom) /\
    getr R 10 = wa G /\ getr R 11 = wa (ext_Z true 0 4 avail) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G avail P Hsc. destruct (ta1a_setup regs m G avail P) as [HR HK].
  set (E := Ez regs (VALS_ta1a G avail)) in *. destruct P as [ta1a_R12 ta1a_rng_G ta1a_rng_avail ta1a_ka1 ta1a_kw3].
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = avail) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x52490] AXF_ta1a.scr_pta1a 0x52350 AXF_ta1a.sr_ta1a AXF_ta1a.kn_ta1a 34 _ _ _ E m rom regs AXF_ta1a.RES_pta1a_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_ta1a.RES_pta1a fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (ta1a_mem_pta1a m regs G avail) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold ta1a_mem_pta1a. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End TA1A.
End AXF_ta1az.

Module AXF_tad1.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_sc := EVar 32.
Definition e_G := EVar 33.
Definition ACT := SA (EMd M_MUL (ELit 8) e_sc) 614184.
Definition sr_tad1 := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 8 (e_sc)) 12 (e_G)) 20 (ELit 613952)) 21 (EAlu ALU_ADD (EMd M_MUL (ELit 8) e_sc) (ELit 614184))) 22 (ELit 614096)) 23 (EAlu ALU_ADD (EMd M_MUL (ELit 8) e_sc) (ELit 614096))).
Definition kn_tad1 : list kentry :=
  [ KRange e_sc 0 47;
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KWord (SA e_G 24) 4 (ELit 0);
    KWord (SA e_G 28) 4 (ELit 0);
    KWord (SA e_G 8) 8 e_G;
    KWr ACT (ELit 8);
    KWr (SA e_G 0) (ELit 16);
    KDisj ACT (ELit 8) (SA e_G 0) (ELit 40) ].
Definition scr_tad1 : scripts := SCR [] [] [].
Definition ss_tad1 := SS 0x52350 sr_tad1 [] kn_tad1 34.
Definition RUN_tad1 := sym_exec SEGS 100 true [0x524d0] scr_tad1 ss_tad1 [].

Definition scr_ptad1 : scripts := SCR [] [] [].
Definition RES_ptad1 := Eval vm_compute in sym_exec SEGS 100 true [0x524d0] scr_ptad1 ss_tad1 [].
Lemma RES_ptad1_ok : sym_exec SEGS 100 true [0x524d0] scr_ptad1 (SS 0x52350 sr_tad1 [] kn_tad1 34) [] = RES_ptad1.
Proof. vm_compute. reflexivity. Qed.
End AXF_tad1.

Module AXF_tad1z.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section TAD1.
Context {fx : FPState}.

Definition VALS_tad1 (sc G : Z) : list Z := [sc; G].

Record tad1_pre (regs : bvmap 5 word) (m : word -> option byte) (sc G : Z) : Prop := {
  tad1_R8 : getr regs 8 = wa sc ;
  tad1_R12 : getr regs 12 = wa G ;
  tad1_R20 : getr regs 20 = wa 613952 ;
  tad1_R21 : getr regs 21 = wa ((8 * sc) + 614184) ;
  tad1_R22 : getr regs 22 = wa 614096 ;
  tad1_R23 : getr regs 23 = wa ((8 * sc) + 614096) ;
  tad1_rng_sc : 0 <= sc <= 47 ;
  tad1_rng_G : 1 <= G <= 2^63-1 ;
  tad1_ka2 : G mod 8 = 0 ;
  tad1_kw3 : rdn SEGS m (wa (G + 24)) 4 = Some (word_to_le_bytes 4 (wa 0)) ;
  tad1_kw4 : rdn SEGS m (wa (G + 28)) 4 = Some (word_to_le_bytes 4 (wa 0)) ;
  tad1_kw5 : rdn SEGS m (wa (G + 8)) 8 = Some (word_to_le_bytes 8 (wa G)) ;
  tad1_kwr6 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (8 * sc + 614184 + d)) k = true ;
  tad1_kwr7 : forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS m (wa (G + 0 + d)) k = true ;
  tad1_kd8 : 8 * sc + 614184 + 8 <= G + 0 \/ G + 0 + 40 <= 8 * sc + 614184
}.


#[using="Type"] Lemma tad1_setup : forall regs m sc G, tad1_pre regs m sc G ->
  regs_ok (Ez regs (VALS_tad1 sc G)) AXF_tad1.sr_tad1 regs /\ know_ok SEGS (Ez regs (VALS_tad1 sc G)) m AXF_tad1.kn_tad1.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sc G P. destruct P as [tad1_R8 tad1_R12 tad1_R20 tad1_R21 tad1_R22 tad1_R23 tad1_rng_sc tad1_rng_G tad1_ka2 tad1_kw3 tad1_kw4 tad1_kw5 tad1_kwr6 tad1_kwr7 tad1_kd8].
  set (E := Ez regs (VALS_tad1 sc G)).
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_tad1.sr_tad1.
    apply (regs_ok_pin E _ regs 23); [apply (regs_ok_pin E _ regs 22); [apply (regs_ok_pin E _ regs 21); [apply (regs_ok_pin E _ regs 20); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|]|]|]|]|].
    - rewrite tad1_R8. reflexivity.
    - rewrite tad1_R12. reflexivity.
    - rewrite tad1_R20. reflexivity.
    - rewrite tad1_R21, zeval_sound. cbn [zeval edenot AXF_tad1.e_sc AXF_tad1.e_G AXF_tad1.ACT]. rewrite ?Z32, ?Z33. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite tad1_R22. reflexivity.
    - rewrite tad1_R23, zeval_sound. cbn [zeval edenot AXF_tad1.e_sc AXF_tad1.e_G AXF_tad1.ACT]. rewrite ?Z32, ?Z33. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)]. }
  unfold know_ok, AXF_tad1.kn_tad1.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_tad1.e_sc AXF_tad1.e_G AXF_tad1.ACT a_base a_off].
  all: rewrite ?Z32, ?Z33.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sc _ _ tad1_rng_sc eq_refl eq_refl), ?(mod64_of_range G _ _ tad1_rng_G eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply tad1_kwr6 | apply tad1_kwr7]; assumption).
  all: try (clear - tad1_rng_sc tad1_rng_G tad1_ka2; lia).
  all: first [(clear - tad1_rng_sc tad1_rng_G tad1_ka2 tad1_kd8; lia) | lia].
Qed.


Definition tad1_mem_ptad1 (m : word -> option byte) (regs : bvmap 5 word) (sc G : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (m) (wa (8 * sc + 614184)) (word_to_le_bytes 8 (wa 0))) (wa (G + 0)) (word_to_le_bytes 8 (wa 0))) (wa (G + 8)) (word_to_le_bytes 8 (wa 0)).

#[using="Type"] Theorem tad1_ptad1 : forall regs m rom sc G, tad1_pre regs m sc G ->
  scs_denot SEGS m (Ez regs (VALS_tad1 sc G)) (snd (fst AXF_tad1.RES_ptad1)) ->
  exists R, msteps SEGS (mkst regs (wa 0x52350) m rom) (mkst R (wa 0x524d0) (tad1_mem_ptad1 m regs sc G) rom) /\
    getr R 8 = wa sc /\ getr R 10 = wa 0 /\ getr R 11 = wa 0 /\ getr R 12 = wa G /\ getr R 20 = wa 613952 /\ getr R 21 = wa ((8 * sc) + 614184) /\ getr R 22 = wa 614096 /\ getr R 23 = wa ((8 * sc) + 614096) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 9; 13; 14; 15; 16; 17; 18; 19; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc G P Hsc. destruct (tad1_setup regs m sc G P) as [HR HK].
  set (E := Ez regs (VALS_tad1 sc G)) in *. destruct P as [tad1_R8 tad1_R12 tad1_R20 tad1_R21 tad1_R22 tad1_R23 tad1_rng_sc tad1_rng_G tad1_ka2 tad1_kw3 tad1_kw4 tad1_kw5 tad1_kwr6 tad1_kwr7 tad1_kd8].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x524d0] AXF_tad1.scr_ptad1 0x52350 AXF_tad1.sr_tad1 AXF_tad1.kn_tad1 34 _ _ _ E m rom regs AXF_tad1.RES_ptad1_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_tad1.RES_ptad1 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (tad1_mem_ptad1 m regs sc G) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold tad1_mem_ptad1. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End TAD1.
End AXF_tad1z.

Module AXF_tadn.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_sc := EVar 32.
Definition e_G := EVar 33.
Definition e_nx := EVar 34.
Definition e_pv := EVar 35.
Definition ACT := SA (EMd M_MUL (ELit 8) e_sc) 614184.
Definition sr_tadn := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 8 (e_sc)) 12 (e_G)) 20 (ELit 613952)) 21 (EAlu ALU_ADD (EMd M_MUL (ELit 8) e_sc) (ELit 614184))) 22 (ELit 614096)) 23 (EAlu ALU_ADD (EMd M_MUL (ELit 8) e_sc) (ELit 614096))).
Definition kn_tadn : list kentry :=
  [ KRange e_sc 0 47;
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange e_nx 1 (2^63-1);
    KRange e_pv 1 (2^63-1);
    KWord (SA e_G 24) 4 (ELit 0);
    KWord (SA e_G 28) 4 (ELit 0);
    KWord (SA e_G 8) 8 e_nx;
    KWord (SA e_G 0) 8 e_pv;
    KWord ACT 8 e_G;
    KWr ACT (ELit 8);
    KWr (SA e_G 0) (ELit 16);
    KWr (SA e_pv 8) (ELit 8);
    KWr (SA e_nx 0) (ELit 8);
    KDisj ACT (ELit 8) (SA e_G 0) (ELit 40);
    KDisj ACT (ELit 8) (SA e_pv 8) (ELit 8);
    KDisj ACT (ELit 8) (SA e_nx 0) (ELit 8);
    KDisj (SA e_pv 8) (ELit 8) (SA e_G 0) (ELit 40);
    KDisj (SA e_nx 0) (ELit 8) (SA e_G 0) (ELit 40) ].
Definition scr_tadn : scripts := SCR [false] [] [].
Definition ss_tadn := SS 0x52350 sr_tadn [] kn_tadn 36.
Definition RUN_tadn := sym_exec SEGS 100 true [0x523b8] scr_tadn ss_tadn [].

Definition scr_ptadn : scripts := SCR [false] [] [].
Definition RES_ptadn := Eval vm_compute in sym_exec SEGS 100 true [0x523b8] scr_ptadn ss_tadn [].
Lemma RES_ptadn_ok : sym_exec SEGS 100 true [0x523b8] scr_ptadn (SS 0x52350 sr_tadn [] kn_tadn 36) [] = RES_ptadn.
Proof. vm_compute. reflexivity. Qed.
End AXF_tadn.

Module AXF_tadnz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section TADN.
Context {fx : FPState}.

Definition VALS_tadn (sc G nx pv : Z) : list Z := [sc; G; nx; pv].

Record tadn_pre (regs : bvmap 5 word) (m : word -> option byte) (sc G nx pv : Z) : Prop := {
  tadn_R8 : getr regs 8 = wa sc ;
  tadn_R12 : getr regs 12 = wa G ;
  tadn_R20 : getr regs 20 = wa 613952 ;
  tadn_R21 : getr regs 21 = wa ((8 * sc) + 614184) ;
  tadn_R22 : getr regs 22 = wa 614096 ;
  tadn_R23 : getr regs 23 = wa ((8 * sc) + 614096) ;
  tadn_rng_sc : 0 <= sc <= 47 ;
  tadn_rng_G : 1 <= G <= 2^63-1 ;
  tadn_rng_nx : 1 <= nx <= 2^63-1 ;
  tadn_rng_pv : 1 <= pv <= 2^63-1 ;
  tadn_ka2 : G mod 8 = 0 ;
  tadn_kw5 : rdn SEGS m (wa (G + 24)) 4 = Some (word_to_le_bytes 4 (wa 0)) ;
  tadn_kw6 : rdn SEGS m (wa (G + 28)) 4 = Some (word_to_le_bytes 4 (wa 0)) ;
  tadn_kw7 : rdn SEGS m (wa (G + 8)) 8 = Some (word_to_le_bytes 8 (wa nx)) ;
  tadn_kw8 : rdn SEGS m (wa (G + 0)) 8 = Some (word_to_le_bytes 8 (wa pv)) ;
  tadn_kw9 : rdn SEGS m (wa (8 * sc + 614184)) 8 = Some (word_to_le_bytes 8 (wa G)) ;
  tadn_kwr10 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (8 * sc + 614184 + d)) k = true ;
  tadn_kwr11 : forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS m (wa (G + 0 + d)) k = true ;
  tadn_kwr12 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (pv + 8 + d)) k = true ;
  tadn_kwr13 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (nx + 0 + d)) k = true ;
  tadn_kd14 : 8 * sc + 614184 + 8 <= G + 0 \/ G + 0 + 40 <= 8 * sc + 614184 ;
  tadn_kd15 : 8 * sc + 614184 + 8 <= pv + 8 \/ pv + 8 + 8 <= 8 * sc + 614184 ;
  tadn_kd16 : 8 * sc + 614184 + 8 <= nx + 0 \/ nx + 0 + 8 <= 8 * sc + 614184 ;
  tadn_kd17 : pv + 8 + 8 <= G + 0 \/ G + 0 + 40 <= pv + 8 ;
  tadn_kd18 : nx + 0 + 8 <= G + 0 \/ G + 0 + 40 <= nx + 0
}.


#[using="Type"] Lemma tadn_setup : forall regs m sc G nx pv, tadn_pre regs m sc G nx pv ->
  regs_ok (Ez regs (VALS_tadn sc G nx pv)) AXF_tadn.sr_tadn regs /\ know_ok SEGS (Ez regs (VALS_tadn sc G nx pv)) m AXF_tadn.kn_tadn.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sc G nx pv P. destruct P as [tadn_R8 tadn_R12 tadn_R20 tadn_R21 tadn_R22 tadn_R23 tadn_rng_sc tadn_rng_G tadn_rng_nx tadn_rng_pv tadn_ka2 tadn_kw5 tadn_kw6 tadn_kw7 tadn_kw8 tadn_kw9 tadn_kwr10 tadn_kwr11 tadn_kwr12 tadn_kwr13 tadn_kd14 tadn_kd15 tadn_kd16 tadn_kd17 tadn_kd18].
  set (E := Ez regs (VALS_tadn sc G nx pv)).
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = nx) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = pv) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_tadn.sr_tadn.
    apply (regs_ok_pin E _ regs 23); [apply (regs_ok_pin E _ regs 22); [apply (regs_ok_pin E _ regs 21); [apply (regs_ok_pin E _ regs 20); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|]|]|]|]|].
    - rewrite tadn_R8. reflexivity.
    - rewrite tadn_R12. reflexivity.
    - rewrite tadn_R20. reflexivity.
    - rewrite tadn_R21, zeval_sound. cbn [zeval edenot AXF_tadn.e_sc AXF_tadn.e_G AXF_tadn.e_nx AXF_tadn.e_pv AXF_tadn.ACT]. rewrite ?Z32, ?Z33, ?Z34, ?Z35. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite tadn_R22. reflexivity.
    - rewrite tadn_R23, zeval_sound. cbn [zeval edenot AXF_tadn.e_sc AXF_tadn.e_G AXF_tadn.e_nx AXF_tadn.e_pv AXF_tadn.ACT]. rewrite ?Z32, ?Z33, ?Z34, ?Z35. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)]. }
  unfold know_ok, AXF_tadn.kn_tadn.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_tadn.e_sc AXF_tadn.e_G AXF_tadn.e_nx AXF_tadn.e_pv AXF_tadn.ACT a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sc _ _ tadn_rng_sc eq_refl eq_refl), ?(mod64_of_range G _ _ tadn_rng_G eq_refl eq_refl), ?(mod64_of_range nx _ _ tadn_rng_nx eq_refl eq_refl), ?(mod64_of_range pv _ _ tadn_rng_pv eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply tadn_kwr10 | apply tadn_kwr11 | apply tadn_kwr12 | apply tadn_kwr13]; assumption).
  all: try (clear - tadn_rng_sc tadn_rng_G tadn_rng_nx tadn_rng_pv tadn_ka2; lia).
  all: first [(clear - tadn_rng_sc tadn_rng_G tadn_rng_nx tadn_rng_pv tadn_ka2 tadn_kd14; lia) | (clear - tadn_rng_sc tadn_rng_G tadn_rng_nx tadn_rng_pv tadn_ka2 tadn_kd15; lia) | (clear - tadn_rng_sc tadn_rng_G tadn_rng_nx tadn_rng_pv tadn_ka2 tadn_kd16; lia) | (clear - tadn_rng_sc tadn_rng_G tadn_rng_nx tadn_rng_pv tadn_ka2 tadn_kd17; lia) | (clear - tadn_rng_sc tadn_rng_G tadn_rng_nx tadn_rng_pv tadn_ka2 tadn_kd18; lia) | lia].
Qed.


Definition tadn_mem_ptadn (m : word -> option byte) (regs : bvmap 5 word) (sc G nx pv : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (pv + 8)) (word_to_le_bytes 8 (wa nx))) (wa (nx + 0)) (word_to_le_bytes 8 (wa pv))) (wa (8 * sc + 614184)) (word_to_le_bytes 8 (wa nx))) (wa (G + 0)) (word_to_le_bytes 8 (wa 0))) (wa (G + 8)) (word_to_le_bytes 8 (wa 0)).

#[using="Type"] Theorem tadn_ptadn : forall regs m rom sc G nx pv, tadn_pre regs m sc G nx pv ->
  scs_denot SEGS m (Ez regs (VALS_tadn sc G nx pv)) (snd (fst AXF_tadn.RES_ptadn)) ->
  exists R, msteps SEGS (mkst regs (wa 0x52350) m rom) (mkst R (wa 0x523b8) (tadn_mem_ptadn m regs sc G nx pv) rom) /\
    getr R 8 = wa sc /\ getr R 10 = wa nx /\ getr R 11 = wa nx /\ getr R 12 = wa G /\ getr R 20 = wa 613952 /\ getr R 21 = wa ((8 * sc) + 614184) /\ getr R 22 = wa 614096 /\ getr R 23 = wa ((8 * sc) + 614096) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 9; 13; 14; 15; 16; 17; 18; 19; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc G nx pv P Hsc. destruct (tadn_setup regs m sc G nx pv P) as [HR HK].
  set (E := Ez regs (VALS_tadn sc G nx pv)) in *. destruct P as [tadn_R8 tadn_R12 tadn_R20 tadn_R21 tadn_R22 tadn_R23 tadn_rng_sc tadn_rng_G tadn_rng_nx tadn_rng_pv tadn_ka2 tadn_kw5 tadn_kw6 tadn_kw7 tadn_kw8 tadn_kw9 tadn_kwr10 tadn_kwr11 tadn_kwr12 tadn_kwr13 tadn_kd14 tadn_kd15 tadn_kd16 tadn_kd17 tadn_kd18].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = nx) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = pv) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x523b8] AXF_tadn.scr_ptadn 0x52350 AXF_tadn.sr_tadn AXF_tadn.kn_tadn 36 _ _ _ E m rom regs AXF_tadn.RES_ptadn_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_tadn.RES_ptadn fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (tadn_mem_ptadn m regs sc G nx pv) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold tadn_mem_ptadn. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End TADN.
End AXF_tadnz.

Module AXF_tar.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Definition e_sc := EVar 32.
Definition e_G := EVar 33.
Definition e_freed := EVar 34.
Definition e_nx := EVar 35.
Definition ACT := SA (EMd M_MUL (ELit 8) e_sc) 614184.
Definition sr_tar := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 8 (e_sc)) 12 (e_G)) 20 (ELit 613952)) 21 (EAlu ALU_ADD (EMd M_MUL (ELit 8) e_sc) (ELit 614184))) 22 (ELit 614096)) 23 (EAlu ALU_ADD (EMd M_MUL (ELit 8) e_sc) (ELit 614096))).
Definition kn_tar : list kentry :=
  [ KRange e_sc 0 47;
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange e_freed 1 (2^32-1);
    KRange e_nx 1 (2^63-1);
    KWord (SA e_G 24) 4 (ELit 0);
    KWord (SA e_G 28) 4 e_freed;
    KWord (SA e_G 8) 8 e_nx;
    KWr ACT (ELit 8);
    KDisj ACT (ELit 8) (SA e_G 0) (ELit 40) ].
Definition scr_tar : scripts := SCR [false] [] [].
Definition ss_tar := SS 0x52350 sr_tar [] kn_tar 36.
Definition RUN_tar := sym_exec SEGS 100 true [0x523b8] scr_tar ss_tar [].

Definition scr_ptar : scripts := SCR [false] [] [].
Definition RES_ptar := Eval vm_compute in sym_exec SEGS 100 true [0x523b8] scr_ptar ss_tar [].
Lemma RES_ptar_ok : sym_exec SEGS 100 true [0x523b8] scr_ptar (SS 0x52350 sr_tar [] kn_tar 36) [] = RES_ptar.
Proof. vm_compute. reflexivity. Qed.
End AXF_tar.

Module AXF_tarz.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ .

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

Section TAR.
Context {fx : FPState}.

Definition VALS_tar (sc G freed nx : Z) : list Z := [sc; G; freed; nx].

Record tar_pre (regs : bvmap 5 word) (m : word -> option byte) (sc G freed nx : Z) : Prop := {
  tar_R8 : getr regs 8 = wa sc ;
  tar_R12 : getr regs 12 = wa G ;
  tar_R20 : getr regs 20 = wa 613952 ;
  tar_R21 : getr regs 21 = wa ((8 * sc) + 614184) ;
  tar_R22 : getr regs 22 = wa 614096 ;
  tar_R23 : getr regs 23 = wa ((8 * sc) + 614096) ;
  tar_rng_sc : 0 <= sc <= 47 ;
  tar_rng_G : 1 <= G <= 2^63-1 ;
  tar_rng_freed : 1 <= freed <= 2^32-1 ;
  tar_rng_nx : 1 <= nx <= 2^63-1 ;
  tar_ka2 : G mod 8 = 0 ;
  tar_kw5 : rdn SEGS m (wa (G + 24)) 4 = Some (word_to_le_bytes 4 (wa 0)) ;
  tar_kw6 : rdn SEGS m (wa (G + 28)) 4 = Some (word_to_le_bytes 4 (wa freed)) ;
  tar_kw7 : rdn SEGS m (wa (G + 8)) 8 = Some (word_to_le_bytes 8 (wa nx)) ;
  tar_kwr8 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (8 * sc + 614184 + d)) k = true ;
  tar_kd9 : 8 * sc + 614184 + 8 <= G + 0 \/ G + 0 + 40 <= 8 * sc + 614184
}.


#[using="Type"] Lemma tar_setup : forall regs m sc G freed nx, tar_pre regs m sc G freed nx ->
  regs_ok (Ez regs (VALS_tar sc G freed nx)) AXF_tar.sr_tar regs /\ know_ok SEGS (Ez regs (VALS_tar sc G freed nx)) m AXF_tar.kn_tar.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sc G freed nx P. destruct P as [tar_R8 tar_R12 tar_R20 tar_R21 tar_R22 tar_R23 tar_rng_sc tar_rng_G tar_rng_freed tar_rng_nx tar_ka2 tar_kw5 tar_kw6 tar_kw7 tar_kwr8 tar_kd9].
  set (E := Ez regs (VALS_tar sc G freed nx)).
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = freed) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = nx) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_tar.sr_tar.
    apply (regs_ok_pin E _ regs 23); [apply (regs_ok_pin E _ regs 22); [apply (regs_ok_pin E _ regs 21); [apply (regs_ok_pin E _ regs 20); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|]|]|]|]|].
    - rewrite tar_R8. reflexivity.
    - rewrite tar_R12. reflexivity.
    - rewrite tar_R20. reflexivity.
    - rewrite tar_R21, zeval_sound. cbn [zeval edenot AXF_tar.e_sc AXF_tar.e_G AXF_tar.e_freed AXF_tar.e_nx AXF_tar.ACT]. rewrite ?Z32, ?Z33, ?Z34, ?Z35. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite tar_R22. reflexivity.
    - rewrite tar_R23, zeval_sound. cbn [zeval edenot AXF_tar.e_sc AXF_tar.e_G AXF_tar.e_freed AXF_tar.e_nx AXF_tar.ACT]. rewrite ?Z32, ?Z33, ?Z34, ?Z35. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)]. }
  unfold know_ok, AXF_tar.kn_tar.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_tar.e_sc AXF_tar.e_G AXF_tar.e_freed AXF_tar.e_nx AXF_tar.ACT a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sc _ _ tar_rng_sc eq_refl eq_refl), ?(mod64_of_range G _ _ tar_rng_G eq_refl eq_refl), ?(mod64_of_range freed _ _ tar_rng_freed eq_refl eq_refl), ?(mod64_of_range nx _ _ tar_rng_nx eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply tar_kwr8]; assumption).
  all: try (clear - tar_rng_sc tar_rng_G tar_rng_freed tar_rng_nx tar_ka2; lia).
  all: first [(clear - tar_rng_sc tar_rng_G tar_rng_freed tar_rng_nx tar_ka2 tar_kd9; lia) | lia].
Qed.


Definition tar_mem_ptar (m : word -> option byte) (regs : bvmap 5 word) (sc G freed nx : Z) : word -> option byte :=
  wbytes (m) (wa (8 * sc + 614184)) (word_to_le_bytes 8 (wa nx)).

#[using="Type"] Theorem tar_ptar : forall regs m rom sc G freed nx, tar_pre regs m sc G freed nx ->
  scs_denot SEGS m (Ez regs (VALS_tar sc G freed nx)) (snd (fst AXF_tar.RES_ptar)) ->
  exists R, msteps SEGS (mkst regs (wa 0x52350) m rom) (mkst R (wa 0x523b8) (tar_mem_ptar m regs sc G freed nx) rom) /\
    getr R 8 = wa sc /\ getr R 10 = wa nx /\ getr R 12 = wa G /\ getr R 20 = wa 613952 /\ getr R 21 = wa ((8 * sc) + 614184) /\ getr R 22 = wa 614096 /\ getr R 23 = wa ((8 * sc) + 614096) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 9; 13; 14; 15; 16; 17; 18; 19; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc G freed nx P Hsc. destruct (tar_setup regs m sc G freed nx P) as [HR HK].
  set (E := Ez regs (VALS_tar sc G freed nx)) in *. destruct P as [tar_R8 tar_R12 tar_R20 tar_R21 tar_R22 tar_R23 tar_rng_sc tar_rng_G tar_rng_freed tar_rng_nx tar_ka2 tar_kw5 tar_kw6 tar_kw7 tar_kwr8 tar_kd9].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = freed) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = nx) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x523b8] AXF_tar.scr_ptar 0x52350 AXF_tar.sr_tar AXF_tar.kn_tar 36 _ _ _ E m rom regs AXF_tar.RES_ptar_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_tar.RES_ptar fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (tar_mem_ptar m regs sc G freed nx) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold tar_mem_ptar. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End TAR.
End AXF_tarz.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Record ntf_frame (regs : bvmap 5 word) (m : word -> option byte) (sp0 canary ra s0 s1 s2 s3 : Z) : Prop := {
  nf_R2 : getr regs 2 = wa (sp0 - 96) ; nf_R9 : getr regs 9 = wa 0x95e40 ;
  nf_Rsp : 2^20 <= sp0 <= 2^47 ; nf_Asp : sp0 mod 16 = 0 ; nf_HSTK : stk_ok SEGS m (wa sp0) 1024 ;
  nf_Rcan : 0 <= canary <= 2^64-1 ; nf_Rra : 0 <= ra <= 2^64-1 ; nf_Rs0 : 0 <= s0 <= 2^64-1 ; nf_Rs1 : 0 <= s1 <= 2^64-1 ;
  nf_Rs2 : 0 <= s2 <= 2^64-1 ; nf_Rs3 : 0 <= s3 <= 2^64-1 ;
  nf_Mra : rdn SEGS m (wa (sp0 + -8)) 8 = Some (word_to_le_bytes 8 (wa ra)) ;
  nf_Ms0 : rdn SEGS m (wa (sp0 + -16)) 8 = Some (word_to_le_bytes 8 (wa s0)) ;
  nf_Ms1 : rdn SEGS m (wa (sp0 + -24)) 8 = Some (word_to_le_bytes 8 (wa s1)) ;
  nf_Ms2 : rdn SEGS m (wa (sp0 + -32)) 8 = Some (word_to_le_bytes 8 (wa s2)) ;
  nf_Ms3 : rdn SEGS m (wa (sp0 + -40)) 8 = Some (word_to_le_bytes 8 (wa s3)) ;
  nf_Mcan : rdn SEGS m (wa (sp0 + -48)) 8 = Some (word_to_le_bytes 8 (wa canary)) ;
  nf_Mgd : rdn SEGS m (wa (0 + 0x95e40)) 8 = Some (word_to_le_bytes 8 (wa canary))
}.

(* [comment removed for export] *)
Definition ntf_exit (R regs : bvmap 5 word) (ra s0 s1 s2 s3 sp0 base len : Z) : Prop :=
  getr R 1 = wa ra /\ getr R 2 = wa sp0 /\ getr R 8 = wa s0 /\ getr R 9 = wa s1 /\ getr R 18 = wa s2 /\ getr R 19 = wa s3 /\
  getr R 10 = wa base /\ getr R 11 = wa len /\
  (forall n, In n [3;4;20;21;22;23;24;25;26;27]%nat -> getr R (Z_to_bv 5 (Z.of_nat n)) = getr regs (Z_to_bv 5 (Z.of_nat n))).


Definition ee12_mem (m : word -> option byte) (G freed idx : Z) : word -> option byte :=
  wbytes m (wa (G + 28)) (word_to_le_bytes 4 (wa (Z.lor freed (2^idx)))).
Definition ee3_mem (m : word -> option byte) (G sc freed idx : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes m (wa (G + 0)) (word_to_le_bytes 8 (wa G))) (wa (G + 8)) (word_to_le_bytes 8 (wa G)))
    (wa (8 * sc + 614184)) (word_to_le_bytes 8 (wa G))) (wa (G + 28)) (word_to_le_bytes 4 (wa (Z.lor freed (2^idx)))).
Definition ee4_mem (m : word -> option byte) (G freed idx H HP : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes m (wa (G + 8)) (word_to_le_bytes 8 (wa H))) (wa (G + 0)) (word_to_le_bytes 8 (wa HP)))
    (wa (HP + 8)) (word_to_le_bytes 8 (wa G))) (wa (H + 0)) (word_to_le_bytes 8 (wa G))) (wa (G + 28)) (word_to_le_bytes 4 (wa (Z.lor freed (2^idx)))).

Lemma sllw1_wa : forall idx, 0 <= idx <= 31 -> wa (bv_swrap 32 (2^idx)) = wa (bv_swrap 32 (Z.shiftl 1 (idx mod 32))).
Proof. intros idx H. rewrite (Z.mod_small idx 32) by lia. rewrite Z.shiftl_1_l. reflexivity. Qed.

Lemma or_store4 : forall freed idx, 0 <= freed <= 2^32-1 -> 0 <= idx <= 31 ->
  word_to_le_bytes 4 (wa (Z.lor (ext_Z true 0 4 freed mod 2^64) (bv_swrap 32 (Z.shiftl 1 (idx mod 32)) mod 2^64)))
  = word_to_le_bytes 4 (wa (Z.lor freed (2^idx))).
Proof.
  intros freed idx Hf Hi. apply le_wa_eqm; [|apply Nat.leb_le; reflexivity]. change (8 * Z.of_nat 4) with 32.
  rewrite ext4_swrap, (Z.mod_small idx 32) by lia. rewrite Z.shiftl_1_l, sx32_lor, mod64_32, swrap32_mod. reflexivity.
Qed.

Ltac dsc_rw :=
  match goal with
  | H : bv_unsigned (ev ?E ?n) = ?v |- context [bv_unsigned (ev ?E ?n)] => rewrite H
  end.
Ltac dsc_mod :=
  match goal with
  | H : ?lo <= ?x <= ?hi |- context [?x mod 2^64] => rewrite (mod64_of_range x lo hi H eq_refl eq_refl)
  end.
Lemma aor_same : forall f, 0 <= f <= 2^32-1 ->
  (bv_swrap 32 (ext_Z true 0 4 f + 0) mod 2^64 =? ext_Z true 0 4 f mod 2^64) = true.
Proof.
  intros f H. rewrite ext4_swrap, Z.add_0_r. apply Z.eqb_eq. f_equal.
  rewrite (swrap32_eq_mod (bv_swrap 32 f)), swrap32_mod, <- swrap32_eq_mod. reflexivity.
Qed.
Lemma mask_zero_eq : forall a f, 0 <= a <= 2^32-1 -> 0 <= f <= 2^32-1 ->
  (Z.lor (ext_Z true 0 4 a mod 2^64) (ext_Z true 0 4 f mod 2^64) mod 2^64 =? 0) = (Z.lor a f =? 0).
Proof.
  intros a f Ha Hf. rewrite !ext4_swrap, sx32_lor, Z.mod_mod, sx32_zero by lia.
  rewrite Z.mod_small by (apply lor_lt32; lia). reflexivity.
Qed.

Ltac SCS :=
  repeat (first [apply Forall_nil | apply Forall_cons]);
  apply sc_br_z; cbn [zeval edenot]; repeat dsc_rw;
  rewrite ?br_eq_z, ?br_ne_z, ?br_geu_z, ?br_ltu_z; repeat dsc_mod; litmods;
  repeat match goal with
  | H : 0 <= ?f <= 2^32-1 |- context [bv_swrap 32 (ext_Z true 0 4 ?f + 0)] => rewrite (aor_same f H)
  | H : 0 <= ?a <= 2^32-1, H2 : 0 <= ?f <= 2^32-1 |- context [Z.lor (ext_Z true 0 4 ?a mod 2^64) (ext_Z true 0 4 ?f mod 2^64) mod 2^64 =? 0] =>
      rewrite (mask_zero_eq a f H H2)
  end;
  first [ (apply negb_false_iff; reflexivity) | (apply negb_true_iff; apply Z.eqb_neq; assumption)
        | (apply negb_false_iff; apply Z.eqb_eq; assumption) | (apply Z.eqb_eq; assumption) | (apply Z.eqb_neq; assumption) | reflexivity | assumption | (apply negb_true_iff; assumption) | (apply negb_false_iff; assumption) | idtac ].

(* [comment removed for export] *)
Record ee_pre (regs : bvmap 5 word) (m : word -> option byte) (G idx sc avail freed sp0 canary ra s0 s1 s2 s3 : Z) : Prop := {
  ep_F : ntf_frame regs m sp0 canary ra s0 s1 s2 s3 ;
  ep_R10 : getr regs 10 = wa G ; ep_R11 : getr regs 11 = wa (bv_swrap 32 (2^idx)) ; ep_R12 : getr regs 12 = wa sc ;
  ep_R13 : getr regs 13 = wa (bv_swrap 32 (Z.lor avail freed)) ;
  ep_RG : 1 <= G <= 2^63-1 ; ep_AG : G mod 8 = 0 ; ep_Ridx : 0 <= idx <= 31 ; ep_Rsc : 0 <= sc <= 47 ;
  ep_Rav : 0 <= avail <= 2^32-1 ; ep_Rfr : 0 <= freed <= 2^32-1 ;
  ep_Mfr : rdn SEGS m (wa (G + 28)) 4 = Some (word_to_le_bytes 4 (wa freed)) ;
  ep_WG : forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (G + 28 + d)) k = true ;
  ep_DSG : G + 40 <= sp0 - 1024 ;
  ep_DGd : G + 40 <= 0x95e40 \/ 0x95e40 + 8 <= G ;
  ep_DSA : sp0 <= 614184 \/ 614584 <= sp0 - 1024 ;
  ep_DSd : sp0 <= 0x95e40 \/ 0x95e40 + 8 <= sp0 - 1024
}.

Definition E_ee (regs : bvmap 5 word) (vals : list Z) : env :=
  Env (reg_ev regs (fun n => wa (nth (n - 32) vals 0))) (fun _ => []).

Lemma ev_atom : forall regs vals n v, Nat.ltb n 32 = false -> nth (n - 32) vals 0 = v -> 0 <= v < 2^64 ->
  bv_unsigned (ev (E_ee regs vals) n) = v.
Proof.
  intros regs vals n v Hn Hv Hr. unfold E_ee. cbn [ev]. unfold reg_ev. rewrite Hn, Hv. apply u_wa_small. exact Hr.
Qed.

(* [comment removed for export] *)
Ltac atoms E :=
  repeat match goal with
  | |- context [bv_unsigned (ev E ?n)] =>
      lazymatch n with
      | S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S _))))))))))))))))))))))))))))))) =>
        let v := eval cbv in (nth (n - 32) (match E with Env _ _ => [] end) 0) in idtac
      end; fail
  end.

Ltac reg_pin R :=
  first [ (rewrite R; reflexivity)
        | (rewrite R, zeval_sound; apply wa_eqm; cbn [zeval edenot]) ].

Ltac srg HR' := rewrite (HR' _); lazymatch goal with |- edenot _ (sr_get ?l ?r) = _ => let t := eval vm_compute in (sr_get l r) in change (sr_get l r) with t end.

Ltac exit_post HR' :=
  unfold ntf_exit;
  split; [srg HR'; reflexivity|]; split; [srg HR'; reflexivity|]; split; [srg HR'; reflexivity|];
  split; [srg HR'; reflexivity|]; split; [srg HR'; reflexivity|]; split; [srg HR'; reflexivity|];
  split; [srg HR'; reflexivity|]; split; [srg HR'; reflexivity|];
  let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn; cbn [In] in Hn;
  repeat (destruct Hn as [<-|Hn]; [rewrite (HR' _); reflexivity|]); destruct Hn.

Section EE1.
Context {fx : FPState}.

#[using="Type"] Lemma ee_setup : forall regs m G idx sc avail freed sp0 canary ra s0 s1 s2 s3 H,
  ee_pre regs m G idx sc avail freed sp0 canary ra s0 s1 s2 s3 -> 0 <= H <= 2^64-1 ->
  rdn SEGS m (wa (8 * sc + 614184)) 8 = Some (word_to_le_bytes 8 (wa H)) ->
  regs_ok (E_ee regs [G; idx; sc; avail; freed; sp0; canary; H; ra; s0; s1; s2; s3]) AXF_ee.sr_ee regs /\
  know_ok SEGS (E_ee regs [G; idx; sc; avail; freed; sp0; canary; H; ra; s0; s1; s2; s3]) m AXF_ee.kn_ee.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G idx sc avail freed sp0 canary ra s0 s1 s2 s3 H EP RH MH.
  destruct EP as [[R2 R9 Rsp Asp HSTK Rcan Rra Rs0 Rs1 Rs2 Rs3 Mra Ms0 Ms1 Ms2 Ms3 Mcan Mgd] R10 R11 R12 R13 RG AG Ridx Rsc Rav Rfr Mfr WG DSG DGd DSA DSd].
  set (E := E_ee regs [G; idx; sc; avail; freed; sp0; canary; H; ra; s0; s1; s2; s3]).
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = idx) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sc) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = avail) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = freed) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = sp0) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = canary) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = H) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = ra) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = s0) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = s1) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z43 : bv_unsigned (ev E 43) = s2) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z44 : bv_unsigned (ev E 44) = s3) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_ee.sr_ee.
    apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10);
      [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E sr_id regs 2); [apply regs_ok_id|] |] |] |] |] |].
    - rewrite R2, zeval_sound. cbn [zeval edenot AXF_ee.e_sp0]. rewrite Z37. reflexivity.
    - rewrite R9. reflexivity.
    - rewrite R10. reflexivity.
    - rewrite R11, zeval_sound. cbn [zeval edenot AXF_ee.e_idx]. rewrite Z33. litmods. rewrite (Z.mod_small idx 32) by (clear - Ridx; lia).
      rewrite Z.shiftl_1_l. reflexivity.
    - rewrite R12. reflexivity.
    - rewrite R13, zeval_sound. cbn [zeval edenot AXF_ee.e_avail AXF_ee.e_freed]. rewrite Z35, Z36.
      rewrite (Z.mod_small avail (2^64)) by (clear - Rav; lia). rewrite (Z.mod_small freed (2^64)) by (clear - Rfr; lia).
      rewrite !ext4_swrap, sx32_lor. apply wa_eqm. rewrite Z.mod_mod by lia. reflexivity. }
  unfold know_ok, AXF_ee.kn_ee.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_ee.e_sp0 (wa sp0) 1024); [reflexivity | exact HSTK | rewrite u_wa_small by (clear - Rsp; lia); clear - Rsp; lia])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_ee.e_G AXF_ee.e_idx AXF_ee.e_sc AXF_ee.e_avail AXF_ee.e_freed AXF_ee.e_sp0 AXF_ee.e_canary AXF_ee.e_H
            AXF_ee.e_ra AXF_ee.e_s0 AXF_ee.e_s1 AXF_ee.e_s2 AXF_ee.e_s3 AXF_ee.STK AXF_ee.ACT a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42, ?Z43, ?Z44.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sp0 _ _ Rsp eq_refl eq_refl), ?(mod64_of_range G _ _ RG eq_refl eq_refl),
               ?(mod64_of_range idx _ _ Ridx eq_refl eq_refl), ?(mod64_of_range sc _ _ Rsc eq_refl eq_refl),
               ?(mod64_of_range avail _ _ Rav eq_refl eq_refl), ?(mod64_of_range freed _ _ Rfr eq_refl eq_refl).
  all: litmods.
  all: rewrite ?(Z.mod_small (8 * sc) (2^64)) by (clear - Rsc; lia).
  all: try assumption.
  all: try (intros d k Hd Hk; apply WG; assumption).
  all: try (clear - Rsc; lia).
  all: try (clear - Rsp DSG RG; lia).
  all: try (clear - DGd; lia).
  all: try (clear - DSA Rsc; lia).
  all: try (clear - DSd; lia).
Qed.

#[using="Type"] Theorem ee12_arm : forall regs m rom G idx sc avail freed sp0 canary ra s0 s1 s2 s3 H,
  ee_pre regs m G idx sc avail freed sp0 canary ra s0 s1 s2 s3 -> 0 <= H <= 2^64-1 ->
  rdn SEGS m (wa (8 * sc + 614184)) 8 = Some (word_to_le_bytes 8 (wa H)) ->
  (Z.lor avail freed <> 0 \/ (Z.lor avail freed = 0 /\ H = G)) ->
  exists R, msteps SEGS (mkst regs (wa 0x51a2c) m rom) (mkst R (wa 0x51ca0) (ee12_mem m G freed idx) rom)
         /\ ntf_exit R regs ra s0 s1 s2 s3 sp0 0 0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G idx sc avail freed sp0 canary ra s0 s1 s2 s3 H EP RH MH CASE.
  destruct (ee_setup regs m G idx sc avail freed sp0 canary ra s0 s1 s2 s3 H EP RH MH) as [HR HK].
  set (E := E_ee regs [G; idx; sc; avail; freed; sp0; canary; H; ra; s0; s1; s2; s3]) in *.
  destruct EP as [[R2 R9 Rsp Asp HSTK Rcan Rra Rs0 Rs1 Rs2 Rs3 Mra Ms0 Ms1 Ms2 Ms3 Mcan Mgd] R10 R11 R12 R13 RG AG Ridx Rsc Rav Rfr Mfr WG DSG DGd DSA DSd].
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = idx) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sc) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = avail) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = freed) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = H) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  destruct CASE as [Fm | [Fm FH]].
  - destruct (run_sound SEGS 200 [] AXF_ee.scr_ee1 0x51a2c AXF_ee.sr_ee AXF_ee.kn_ee 45 _ _ _ E m rom regs AXF_ee.RES_ee1_ok HR HK) as (R & HR' & _ & Hms).
    { cbn [AXF_ee.RES_ee1 fst snd]. SCS. }
    exists R. split.
    + cbn [AXF_ee.RES_ee1 fst snd s_pc s_log] in Hms.
      lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (ee12_mem m G freed idx) with M; [exact Hms|] end.
      clear Hms HR'. cbn [mem_denot]. unfold ee12_mem. apply (f_equal3 wbytes); [reflexivity | |].
      * rewrite adenot_z. cbn [zeval edenot AXF_ee.e_G]. rewrite Z32. reflexivity.
      * rewrite zeval_sound. cbn [zeval edenot]. rewrite Z33, Z36. repeat dsc_mod. litmods. apply or_store4; assumption.
    + cbn [AXF_ee.RES_ee1 fst snd s_regs] in HR'. clear Hms. exit_post HR'.
  - destruct (run_sound SEGS 200 [] AXF_ee.scr_ee2 0x51a2c AXF_ee.sr_ee AXF_ee.kn_ee 45 _ _ _ E m rom regs AXF_ee.RES_ee2_ok HR HK) as (R & HR' & _ & Hms).
    { cbn [AXF_ee.RES_ee2 fst snd]. SCS. }
    exists R. split.
    + cbn [AXF_ee.RES_ee2 fst snd s_pc s_log] in Hms.
      lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (ee12_mem m G freed idx) with M; [exact Hms|] end.
      clear Hms HR'. cbn [mem_denot]. unfold ee12_mem. apply (f_equal3 wbytes); [reflexivity | |].
      * rewrite adenot_z. cbn [zeval edenot AXF_ee.e_G]. rewrite Z32. reflexivity.
      * rewrite zeval_sound. cbn [zeval edenot]. rewrite Z33, Z36. repeat dsc_mod. litmods. apply or_store4; assumption.
    + cbn [AXF_ee.RES_ee2 fst snd s_regs] in HR'. clear Hms. exit_post HR'.
Qed.
End EE1.

Section EE3.
Context {fx : FPState}.

#[using="Type"] Lemma ee3_setup : forall regs m G idx sc avail freed sp0 canary ra s0 s1 s2 s3,
  ee_pre regs m G idx sc avail freed sp0 canary ra s0 s1 s2 s3 ->
  rdn SEGS m (wa (8 * sc + 614184)) 8 = Some (word_to_le_bytes 8 (wa 0)) ->
  rdn SEGS m (wa (G + 0)) 8 = Some (word_to_le_bytes 8 (wa 0)) ->
  rdn SEGS m (wa (G + 8)) 8 = Some (word_to_le_bytes 8 (wa 0)) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS m (wa (G + 0 + d)) k = true) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (8 * sc + 614184 + d)) k = true) ->
  (G + 40 <= 8 * sc + 614184 \/ 8 * sc + 614184 + 8 <= G) ->
  regs_ok (E_ee regs [G; idx; sc; avail; freed; sp0; canary; 0; ra; s0; s1; s2; s3]) AXF_ee3.sr_ee3 regs /\
  know_ok SEGS (E_ee regs [G; idx; sc; avail; freed; sp0; canary; 0; ra; s0; s1; s2; s3]) m AXF_ee3.kn_ee3.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G idx sc avail freed sp0 canary ra s0 s1 s2 s3 EP MA MP MN WG0 WA DGA.
  destruct EP as [[R2 R9 Rsp Asp HSTK Rcan Rra Rs0 Rs1 Rs2 Rs3 Mra Ms0 Ms1 Ms2 Ms3 Mcan Mgd] R10 R11 R12 R13 RG AG Ridx Rsc Rav Rfr Mfr WG DSG DGd DSA DSd].
  set (E := E_ee regs [G; idx; sc; avail; freed; sp0; canary; 0; ra; s0; s1; s2; s3]).
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = idx) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sc) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = avail) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = freed) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = sp0) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = canary) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = ra) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = s0) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = s1) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z43 : bv_unsigned (ev E 43) = s2) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z44 : bv_unsigned (ev E 44) = s3) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_ee3.sr_ee3.
    apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10);
      [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E sr_id regs 2); [apply regs_ok_id|] |] |] |] |] |].
    - rewrite R2, zeval_sound. cbn [zeval edenot AXF_ee3.e_sp0]. rewrite Z37. reflexivity.
    - rewrite R9. reflexivity.
    - rewrite R10. reflexivity.
    - rewrite R11, zeval_sound. cbn [zeval edenot AXF_ee3.e_idx]. rewrite Z33. litmods. rewrite (Z.mod_small idx 32) by (clear - Ridx; lia).
      rewrite Z.shiftl_1_l. reflexivity.
    - rewrite R12. reflexivity.
    - rewrite R13, zeval_sound. cbn [zeval edenot AXF_ee3.e_avail AXF_ee3.e_freed]. rewrite Z35, Z36.
      rewrite (Z.mod_small avail (2^64)) by (clear - Rav; lia). rewrite (Z.mod_small freed (2^64)) by (clear - Rfr; lia).
      rewrite !ext4_swrap, sx32_lor. apply wa_eqm. rewrite Z.mod_mod by lia. reflexivity. }
  unfold know_ok, AXF_ee3.kn_ee3.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_ee3.e_sp0 (wa sp0) 1024); [reflexivity | exact HSTK | rewrite u_wa_small by (clear - Rsp; lia); clear - Rsp; lia])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_ee3.e_G AXF_ee3.e_idx AXF_ee3.e_sc AXF_ee3.e_avail AXF_ee3.e_freed AXF_ee3.e_sp0 AXF_ee3.e_canary
            AXF_ee3.e_ra AXF_ee3.e_s0 AXF_ee3.e_s1 AXF_ee3.e_s2 AXF_ee3.e_s3 AXF_ee3.STK AXF_ee3.ACT a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z40, ?Z41, ?Z42, ?Z43, ?Z44.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sp0 _ _ Rsp eq_refl eq_refl), ?(mod64_of_range G _ _ RG eq_refl eq_refl),
               ?(mod64_of_range idx _ _ Ridx eq_refl eq_refl), ?(mod64_of_range sc _ _ Rsc eq_refl eq_refl),
               ?(mod64_of_range avail _ _ Rav eq_refl eq_refl), ?(mod64_of_range freed _ _ Rfr eq_refl eq_refl).
  all: litmods.
  all: rewrite ?(Z.mod_small (8 * sc) (2^64)) by (clear - Rsc; lia).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply WG | apply WG0 | apply WA]; assumption).
  all: try (clear - Rsc; lia).
  all: try (clear - Rsp DSG RG; lia).
  all: try (clear - DGd; lia).
  all: try (clear - DSA Rsc; lia).
  all: try (clear - DSd; lia).
  all: try (clear - DGA; lia).
  all: try (clear - Rsc; lia).
Qed.

#[using="Type"] Theorem ee3_arm : forall regs m rom G idx sc avail freed sp0 canary ra s0 s1 s2 s3,
  ee_pre regs m G idx sc avail freed sp0 canary ra s0 s1 s2 s3 ->
  rdn SEGS m (wa (8 * sc + 614184)) 8 = Some (word_to_le_bytes 8 (wa 0)) ->
  rdn SEGS m (wa (G + 0)) 8 = Some (word_to_le_bytes 8 (wa 0)) ->
  rdn SEGS m (wa (G + 8)) 8 = Some (word_to_le_bytes 8 (wa 0)) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS m (wa (G + 0 + d)) k = true) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (8 * sc + 614184 + d)) k = true) ->
  (G + 40 <= 8 * sc + 614184 \/ 8 * sc + 614184 + 8 <= G) ->
  Z.lor avail freed = 0 ->
  exists R, msteps SEGS (mkst regs (wa 0x51a2c) m rom) (mkst R (wa 0x51ca0) (ee3_mem m G sc freed idx) rom)
         /\ ntf_exit R regs ra s0 s1 s2 s3 sp0 0 0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G idx sc avail freed sp0 canary ra s0 s1 s2 s3 EP MA MP MN WG0 WA DGA Fm.
  destruct (ee3_setup regs m G idx sc avail freed sp0 canary ra s0 s1 s2 s3 EP MA MP MN WG0 WA DGA) as [HR HK].
  set (E := E_ee regs [G; idx; sc; avail; freed; sp0; canary; 0; ra; s0; s1; s2; s3]) in *.
  destruct EP as [[R2 R9 Rsp Asp HSTK Rcan Rra Rs0 Rs1 Rs2 Rs3 Mra Ms0 Ms1 Ms2 Ms3 Mcan Mgd] R10 R11 R12 R13 RG AG Ridx Rsc Rav Rfr Mfr WG DSG DGd DSA DSd].
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = idx) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sc) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = avail) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = freed) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 200 [] AXF_ee3.scr_pee3 0x51a2c AXF_ee3.sr_ee3 AXF_ee3.kn_ee3 45 _ _ _ E m rom regs AXF_ee3.RES_pee3_ok HR HK) as (R & HR' & _ & Hms).
  { cbn [AXF_ee3.RES_pee3 fst snd]. SCS. }
  exists R. split.
  - cbn [AXF_ee3.RES_pee3 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (ee3_mem m G sc freed idx) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold ee3_mem.
    repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try (rewrite adenot_z; cbn [zeval edenot AXF_ee3.e_G AXF_ee3.ACT AXF_ee3.e_sc]; rewrite ?Z32, ?Z34; repeat dsc_mod; litmods;
              rewrite ?(Z.mod_small (8 * sc) (2^64)) by (clear - Rsc; lia); reflexivity).
    all: try (rewrite zeval_sound; cbn [zeval edenot]; rewrite ?Z33, ?Z36; repeat dsc_mod; litmods; apply or_store4; assumption).
  - cbn [AXF_ee3.RES_pee3 fst snd s_regs] in HR'. clear Hms. exit_post HR'.
Qed.
End EE3.

Section EE4.
Context {fx : FPState}.

#[using="Type"] Lemma ee4_setup : forall regs m G idx sc avail freed sp0 canary ra s0 s1 s2 s3 H HP,
  ee_pre regs m G idx sc avail freed sp0 canary ra s0 s1 s2 s3 ->
  1 <= H <= 2^63-1 -> 1 <= HP <= 2^63-1 ->
  rdn SEGS m (wa (8 * sc + 614184)) 8 = Some (word_to_le_bytes 8 (wa H)) ->
  rdn SEGS m (wa (G + 0)) 8 = Some (word_to_le_bytes 8 (wa 0)) ->
  rdn SEGS m (wa (G + 8)) 8 = Some (word_to_le_bytes 8 (wa 0)) ->
  rdn SEGS m (wa (H + 0)) 8 = Some (word_to_le_bytes 8 (wa HP)) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS m (wa (G + 0 + d)) k = true) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (H + 0 + d)) k = true) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (HP + 8 + d)) k = true) ->
  H + 40 <= sp0 - 1024 -> HP + 40 <= sp0 - 1024 ->
  (G + 40 <= H \/ H + 40 <= G) -> (G + 40 <= HP \/ HP + 40 <= G) ->
  (H + 40 <= 0x95e40 \/ 0x95e40 + 8 <= H) -> (HP + 40 <= 0x95e40 \/ 0x95e40 + 8 <= HP) ->
  (H + 40 <= 8 * sc + 614184 \/ 8 * sc + 614184 + 8 <= H) -> (HP + 40 <= 8 * sc + 614184 \/ 8 * sc + 614184 + 8 <= HP) ->
  (G + 40 <= 8 * sc + 614184 \/ 8 * sc + 614184 + 8 <= G) ->
  regs_ok (E_ee regs [G; idx; sc; avail; freed; sp0; canary; H; ra; s0; s1; s2; s3; HP]) AXF_ee4.sr_ee4 regs /\
  know_ok SEGS (E_ee regs [G; idx; sc; avail; freed; sp0; canary; H; ra; s0; s1; s2; s3; HP]) m AXF_ee4.kn_ee4.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G idx sc avail freed sp0 canary ra s0 s1 s2 s3 H HP EP RH RHP MA MP MN MH WG0 WH WHP DSH DSHP DGH DGHP DHd DHPd DHA DHPA DGA.
  destruct EP as [[R2 R9 Rsp Asp HSTK Rcan Rra Rs0 Rs1 Rs2 Rs3 Mra Ms0 Ms1 Ms2 Ms3 Mcan Mgd] R10 R11 R12 R13 RG AG Ridx Rsc Rav Rfr Mfr WG DSG DGd DSA DSd].
  set (E := E_ee regs [G; idx; sc; avail; freed; sp0; canary; H; ra; s0; s1; s2; s3; HP]).
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = idx) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sc) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = avail) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = freed) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = sp0) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = canary) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = ra) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = s0) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = s1) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z43 : bv_unsigned (ev E 43) = s2) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z44 : bv_unsigned (ev E 44) = s3) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = H) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z45 : bv_unsigned (ev E 45) = HP) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_ee4.sr_ee4.
    apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10);
      [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E sr_id regs 2); [apply regs_ok_id|] |] |] |] |] |].
    - rewrite R2, zeval_sound. cbn [zeval edenot AXF_ee4.e_sp0]. rewrite Z37. reflexivity.
    - rewrite R9. reflexivity.
    - rewrite R10. reflexivity.
    - rewrite R11, zeval_sound. cbn [zeval edenot AXF_ee4.e_idx]. rewrite Z33. litmods. rewrite (Z.mod_small idx 32) by (clear - Ridx; lia).
      rewrite Z.shiftl_1_l. reflexivity.
    - rewrite R12. reflexivity.
    - rewrite R13, zeval_sound. cbn [zeval edenot AXF_ee4.e_avail AXF_ee4.e_freed]. rewrite Z35, Z36.
      rewrite (Z.mod_small avail (2^64)) by (clear - Rav; lia). rewrite (Z.mod_small freed (2^64)) by (clear - Rfr; lia).
      rewrite !ext4_swrap, sx32_lor. apply wa_eqm. rewrite Z.mod_mod by lia. reflexivity. }
  unfold know_ok, AXF_ee4.kn_ee4.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_ee4.e_sp0 (wa sp0) 1024); [reflexivity | exact HSTK | rewrite u_wa_small by (clear - Rsp; lia); clear - Rsp; lia])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_ee4.e_G AXF_ee4.e_idx AXF_ee4.e_sc AXF_ee4.e_avail AXF_ee4.e_freed AXF_ee4.e_sp0 AXF_ee4.e_canary
            AXF_ee4.e_H AXF_ee4.e_HP AXF_ee4.e_ra AXF_ee4.e_s0 AXF_ee4.e_s1 AXF_ee4.e_s2 AXF_ee4.e_s3 AXF_ee4.STK AXF_ee4.ACT a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42, ?Z43, ?Z44, ?Z45.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sp0 _ _ Rsp eq_refl eq_refl), ?(mod64_of_range G _ _ RG eq_refl eq_refl),
               ?(mod64_of_range idx _ _ Ridx eq_refl eq_refl), ?(mod64_of_range sc _ _ Rsc eq_refl eq_refl),
               ?(mod64_of_range avail _ _ Rav eq_refl eq_refl), ?(mod64_of_range freed _ _ Rfr eq_refl eq_refl),
               ?(mod64_of_range H _ _ RH eq_refl eq_refl), ?(mod64_of_range HP _ _ RHP eq_refl eq_refl).
  all: litmods.
  all: rewrite ?(Z.mod_small (8 * sc) (2^64)) by (clear - Rsc; lia).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply WG | apply WG0 | apply WH | apply WHP]; assumption).
  all: try (clear - Rsc; lia).
  all: try (clear - Rsp DSG RG; lia).
  all: try (clear - DGd; lia).
  all: try (clear - DSA Rsc; lia).
  all: try (clear - DSd; lia).
  all: try (clear - DGA; lia).
  all: try (clear - Rsc; lia).
  all: try (clear - DSH; lia). all: try (clear - DSHP; lia). all: try (clear - DGH; lia). all: try (clear - DGHP; lia).
  all: try (clear - DHd; lia). all: try (clear - DHPd; lia). all: try (clear - DHA; lia). all: try (clear - DHPA; lia).
  all: try (clear - Rsp DSH RH; lia). all: try (clear - Rsp DSHP RHP; lia).
Qed.

#[using="Type"] Theorem ee4_arm : forall regs m rom G idx sc avail freed sp0 canary ra s0 s1 s2 s3 H HP,
  ee_pre regs m G idx sc avail freed sp0 canary ra s0 s1 s2 s3 ->
  1 <= H <= 2^63-1 -> 1 <= HP <= 2^63-1 ->
  rdn SEGS m (wa (8 * sc + 614184)) 8 = Some (word_to_le_bytes 8 (wa H)) ->
  rdn SEGS m (wa (G + 0)) 8 = Some (word_to_le_bytes 8 (wa 0)) ->
  rdn SEGS m (wa (G + 8)) 8 = Some (word_to_le_bytes 8 (wa 0)) ->
  rdn SEGS m (wa (H + 0)) 8 = Some (word_to_le_bytes 8 (wa HP)) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS m (wa (G + 0 + d)) k = true) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (H + 0 + d)) k = true) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (HP + 8 + d)) k = true) ->
  H + 40 <= sp0 - 1024 -> HP + 40 <= sp0 - 1024 ->
  (G + 40 <= H \/ H + 40 <= G) -> (G + 40 <= HP \/ HP + 40 <= G) ->
  (H + 40 <= 0x95e40 \/ 0x95e40 + 8 <= H) -> (HP + 40 <= 0x95e40 \/ 0x95e40 + 8 <= HP) ->
  (H + 40 <= 8 * sc + 614184 \/ 8 * sc + 614184 + 8 <= H) -> (HP + 40 <= 8 * sc + 614184 \/ 8 * sc + 614184 + 8 <= HP) ->
  (G + 40 <= 8 * sc + 614184 \/ 8 * sc + 614184 + 8 <= G) ->
  Z.lor avail freed = 0 -> H <> G ->
  exists R, msteps SEGS (mkst regs (wa 0x51a2c) m rom) (mkst R (wa 0x51ca0) (ee4_mem m G freed idx H HP) rom)
         /\ ntf_exit R regs ra s0 s1 s2 s3 sp0 0 0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G idx sc avail freed sp0 canary ra s0 s1 s2 s3 H HP EP RH RHP MA MP MN MH WG0 WH WHP DSH DSHP DGH DGHP DHd DHPd DHA DHPA DGA Fm FHG.
  destruct (ee4_setup regs m G idx sc avail freed sp0 canary ra s0 s1 s2 s3 H HP EP RH RHP MA MP MN MH WG0 WH WHP DSH DSHP DGH DGHP DHd DHPd DHA DHPA DGA) as [HR HK].
  set (E := E_ee regs [G; idx; sc; avail; freed; sp0; canary; H; ra; s0; s1; s2; s3; HP]) in *.
  destruct EP as [[R2 R9 Rsp Asp HSTK Rcan Rra Rs0 Rs1 Rs2 Rs3 Mra Ms0 Ms1 Ms2 Ms3 Mcan Mgd] R10 R11 R12 R13 RG AG Ridx Rsc Rav Rfr Mfr WG DSG DGd DSA DSd].
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = idx) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sc) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = avail) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = freed) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = H) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  assert (Z45 : bv_unsigned (ev E 45) = HP) by (apply ev_atom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 200 [] AXF_ee4.scr_pee4 0x51a2c AXF_ee4.sr_ee4 AXF_ee4.kn_ee4 46 _ _ _ E m rom regs AXF_ee4.RES_pee4_ok HR HK) as (R & HR' & _ & Hms).
  { cbn [AXF_ee4.RES_pee4 fst snd]. SCS. }
  exists R. split.
  - cbn [AXF_ee4.RES_pee4 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (ee4_mem m G freed idx H HP) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold ee4_mem.
    repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try (rewrite adenot_z; cbn [zeval edenot AXF_ee4.e_G AXF_ee4.e_H AXF_ee4.e_HP]; rewrite ?Z32, ?Z39, ?Z45; repeat dsc_mod; litmods;
              rewrite ?(Z.mod_small (8 * sc) (2^64)) by (clear - Rsc; lia); reflexivity).
    all: try (rewrite zeval_sound; cbn [zeval edenot]; rewrite ?Z33, ?Z36; repeat dsc_mod; litmods; apply or_store4; assumption).
  - cbn [AXF_ee4.RES_pee4 fst snd s_regs] in HR'. clear Hms. exit_post HR'.
Qed.
End EE4.
