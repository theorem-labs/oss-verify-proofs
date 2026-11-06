(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AxBits.

Module AXF_dec.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

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
    KWord (SA SC 622593) 1 e_bnc;
    KWord (SA SC8 622184) 8 e_usg;
    KWord (SA (ELit 0) 0x65b58) 8 (ELit 0x97c00);
    KWord (SA (ELit 0) 0x97c00) 8 e_canary;
    KDisj STK (ELit 1024) (SA e_G 0) (ELit 40);
    KDisj STK (ELit 1024) (SA TB1 98984) (ELit 2);
    KDisj STK (ELit 1024) (SA SC2 98984) (ELit 2);
    KDisj STK (ELit 1024) (SA SC 622593) (ELit 1);
    KDisj STK (ELit 1024) (SA SC8 622184) (ELit 8) ].
Definition scr_dec : scripts := SCR [] [] [].
Definition ss_dec := SS 0x53688 sr_dec [] kn_dec 43.
Definition RUN_dec := sym_exec SEGS 200 true [0x5379c; 0x537e4] scr_dec ss_dec [].

Definition scr_dE2 : scripts := SCR [false; true] [] [].
Definition RES_dE2 := Eval vm_compute in sym_exec SEGS 200 true [0x5379c; 0x537e4] scr_dE2 ss_dec [].
Lemma RES_dE2_ok : sym_exec SEGS 200 true [0x5379c; 0x537e4] scr_dE2 (SS 0x53688 sr_dec [] kn_dec 43) [] = RES_dE2.
Proof. vm_compute. reflexivity. Qed.

Definition scr_dG2 : scripts := SCR [false; false; false; true; true] [] [].
Definition RES_dG2 := Eval vm_compute in sym_exec SEGS 200 true [0x5379c; 0x537e4] scr_dG2 ss_dec [].
Lemma RES_dG2_ok : sym_exec SEGS 200 true [0x5379c; 0x537e4] scr_dG2 (SS 0x53688 sr_dec [] kn_dec 43) [] = RES_dG2.
Proof. vm_compute. reflexivity. Qed.

Definition scr_dG3b : scripts := SCR [false; false; false; false; true; false; true] [] [].
Definition RES_dG3b := Eval vm_compute in sym_exec SEGS 200 true [0x5379c; 0x537e4] scr_dG3b ss_dec [].
Lemma RES_dG3b_ok : sym_exec SEGS 200 true [0x5379c; 0x537e4] scr_dG3b (SS 0x53688 sr_dec [] kn_dec 43) [] = RES_dG3b.
Proof. vm_compute. reflexivity. Qed.

Definition scr_dG4b : scripts := SCR [false; false; false; false; true; false; false; true] [] [].
Definition RES_dG4b := Eval vm_compute in sym_exec SEGS 200 true [0x5379c; 0x537e4] scr_dG4b ss_dec [].
Lemma RES_dG4b_ok : sym_exec SEGS 200 true [0x5379c; 0x537e4] scr_dG4b (SS 0x53688 sr_dec [] kn_dec 43) [] = RES_dG4b.
Proof. vm_compute. reflexivity. Qed.

Definition scr_dG5b : scripts := SCR [false; false; false; false; true; false; false; false; true] [] [].
Definition RES_dG5b := Eval vm_compute in sym_exec SEGS 200 true [0x5379c; 0x537e4] scr_dG5b ss_dec [].
Lemma RES_dG5b_ok : sym_exec SEGS 200 true [0x5379c; 0x537e4] scr_dG5b (SS 0x53688 sr_dec [] kn_dec 43) [] = RES_dG5b.
Proof. vm_compute. reflexivity. Qed.

Definition scr_dE4b : scripts := SCR [false; false; false; false; true; false; false; false; false; true] [] [].
Definition RES_dE4b := Eval vm_compute in sym_exec SEGS 200 true [0x5379c; 0x537e4] scr_dE4b ss_dec [].
Lemma RES_dE4b_ok : sym_exec SEGS 200 true [0x5379c; 0x537e4] scr_dE4b (SS 0x53688 sr_dec [] kn_dec 43) [] = RES_dE4b.
Proof. vm_compute. reflexivity. Qed.

Definition scr_dE5b : scripts := SCR [false; false; false; false; true; false; false; false; false; false; true] [] [].
Definition RES_dE5b := Eval vm_compute in sym_exec SEGS 200 true [0x5379c; 0x537e4] scr_dE5b ss_dec [].
Lemma RES_dE5b_ok : sym_exec SEGS 200 true [0x5379c; 0x537e4] scr_dE5b (SS 0x53688 sr_dec [] kn_dec 43) [] = RES_dE5b.
Proof. vm_compute. reflexivity. Qed.

Definition scr_dG6b : scripts := SCR [false; false; false; false; true; false; false; false; false; false; false] [] [].
Definition RES_dG6b := Eval vm_compute in sym_exec SEGS 200 true [0x5379c; 0x537e4] scr_dG6b ss_dec [].
Lemma RES_dG6b_ok : sym_exec SEGS 200 true [0x5379c; 0x537e4] scr_dG6b (SS 0x53688 sr_dec [] kn_dec 43) [] = RES_dG6b.
Proof. vm_compute. reflexivity. Qed.

Definition scr_dG1a : scripts := SCR [false; false; false; false; false; true; true] [] [].
Definition RES_dG1a := Eval vm_compute in sym_exec SEGS 200 true [0x5379c; 0x537e4] scr_dG1a ss_dec [].
Lemma RES_dG1a_ok : sym_exec SEGS 200 true [0x5379c; 0x537e4] scr_dG1a (SS 0x53688 sr_dec [] kn_dec 43) [] = RES_dG1a.
Proof. vm_compute. reflexivity. Qed.

Definition scr_dG3a : scripts := SCR [false; false; false; false; false; true; false; true] [] [].
Definition RES_dG3a := Eval vm_compute in sym_exec SEGS 200 true [0x5379c; 0x537e4] scr_dG3a ss_dec [].
Lemma RES_dG3a_ok : sym_exec SEGS 200 true [0x5379c; 0x537e4] scr_dG3a (SS 0x53688 sr_dec [] kn_dec 43) [] = RES_dG3a.
Proof. vm_compute. reflexivity. Qed.

Definition scr_dG4a : scripts := SCR [false; false; false; false; false; true; false; false; true] [] [].
Definition RES_dG4a := Eval vm_compute in sym_exec SEGS 200 true [0x5379c; 0x537e4] scr_dG4a ss_dec [].
Lemma RES_dG4a_ok : sym_exec SEGS 200 true [0x5379c; 0x537e4] scr_dG4a (SS 0x53688 sr_dec [] kn_dec 43) [] = RES_dG4a.
Proof. vm_compute. reflexivity. Qed.

Definition scr_dG5a : scripts := SCR [false; false; false; false; false; true; false; false; false; true] [] [].
Definition RES_dG5a := Eval vm_compute in sym_exec SEGS 200 true [0x5379c; 0x537e4] scr_dG5a ss_dec [].
Lemma RES_dG5a_ok : sym_exec SEGS 200 true [0x5379c; 0x537e4] scr_dG5a (SS 0x53688 sr_dec [] kn_dec 43) [] = RES_dG5a.
Proof. vm_compute. reflexivity. Qed.

Definition scr_dE4a : scripts := SCR [false; false; false; false; false; true; false; false; false; false; true] [] [].
Definition RES_dE4a := Eval vm_compute in sym_exec SEGS 200 true [0x5379c; 0x537e4] scr_dE4a ss_dec [].
Lemma RES_dE4a_ok : sym_exec SEGS 200 true [0x5379c; 0x537e4] scr_dE4a (SS 0x53688 sr_dec [] kn_dec 43) [] = RES_dE4a.
Proof. vm_compute. reflexivity. Qed.

Definition scr_dG6a : scripts := SCR [false; false; false; false; false; true; false; false; false; false; false; false] [] [].
Definition RES_dG6a := Eval vm_compute in sym_exec SEGS 200 true [0x5379c; 0x537e4] scr_dG6a ss_dec [].
Lemma RES_dG6a_ok : sym_exec SEGS 200 true [0x5379c; 0x537e4] scr_dG6a (SS 0x53688 sr_dec [] kn_dec 43) [] = RES_dG6a.
Proof. vm_compute. reflexivity. Qed.
End AXF_dec.

Module AXF_decz.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AxBits MngZ.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.MngZ OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_dec.
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
  dp_Mbnc : rdn SEGS m (wa (622593 + SCW W)) 1 = Some (word_to_le_bytes 1 (wa bnc)) ;
  dp_Musg : rdn SEGS m (wa (622184 + 8 * SCW W)) 8 = Some (word_to_le_bytes 8 (wa usg)) ;
  dp_Mgot : rdn SEGS m (wa 416600) 8 = Some (word_to_le_bytes 8 (wa 0x97c00)) ;
  dp_Mcan : rdn SEGS m (wa 621568) 8 = Some (word_to_le_bytes 8 (wa canary)) ;
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
  getr R 13 = wa (bv_swrap 32 (Z.lor avail freed)) /\ getr R 9 = wa 0x97c00 /\ getr R 2 = wa (sp0 - 96) /\
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
  destruct (run_sound SEGS 200 [0x5379c; 0x537e4] _ 0x53688 sr_dec kn_dec 43 _ _ _ E m rom regs RESok HR HK) as (R & HR' & _ & Hms);
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
  exists R, msteps SEGS (mkst regs (wa 0x53688) m rom)
              (mkst R (wa (if dec_ok G idx W avail freed csz nxt bnc usg then 0x5379c else 0x537e4)) (dec_mem m regs sp0 canary) rom)
         /\ dec_post R regs G idx W avail freed sp0 /\ (dec_ok G idx W avail freed csz nxt bnc usg = true -> getr R 18 = wa 0x97c98).
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

Import OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AxBits OSSVerify.Proofs.fast_float.from_chars.lib.MAXU.AXF_eez.AXF_decz.

Module AXF_ee.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

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
Definition sr_ee := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 2 (EAlu ALU_ADD e_sp0 (ELit (-96)))) 9 (ELit 0x97c00)) 10 (e_G)) 11 (EAluw ALU_SLL (ELit 1) e_idx)) 12 (e_sc)) 13 (EAlu ALU_OR (EExt true 0 4 e_avail) (EExt true 0 4 e_freed))).
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
    KWord (SA ACT 621800) 8 e_H;
    KWord (SA e_sp0 (-8)) 8 e_ra;
    KWord (SA e_sp0 (-16)) 8 e_s0;
    KWord (SA e_sp0 (-24)) 8 e_s1;
    KWord (SA e_sp0 (-32)) 8 e_s2;
    KWord (SA e_sp0 (-40)) 8 e_s3;
    KWord (SA e_sp0 (-48)) 8 e_canary;
    KWord (SA (ELit 0) 0x97c00) 8 e_canary;
    KWr (SA e_G 28) (ELit 4);
    KDisj STK (ELit 1024) (SA e_G 0) (ELit 40);
    KDisj STK (ELit 1024) (SA ACT 621800) (ELit 8);
    KDisj STK (ELit 1024) (SA (ELit 0) 0x97c00) (ELit 8);
    KDisj (SA e_G 0) (ELit 40) (SA (ELit 0) 0x97c00) (ELit 8) ].
Definition scr_ee : scripts := SCR [] [] [].
Definition ss_ee := SS 0x537e4 sr_ee [] kn_ee 45.
Definition RUN_ee := sym_exec SEGS 200 true [] scr_ee ss_ee [].

Definition scr_ee1 : scripts := SCR [true; false; false] [] [].
Definition RES_ee1 := Eval vm_compute in sym_exec SEGS 200 true [] scr_ee1 ss_ee [].
Lemma RES_ee1_ok : sym_exec SEGS 200 true [] scr_ee1 (SS 0x537e4 sr_ee [] kn_ee 45) [] = RES_ee1.
Proof. vm_compute. reflexivity. Qed.

Definition scr_ee2 : scripts := SCR [false; true; false; false] [] [].
Definition RES_ee2 := Eval vm_compute in sym_exec SEGS 200 true [] scr_ee2 ss_ee [].
Lemma RES_ee2_ok : sym_exec SEGS 200 true [] scr_ee2 (SS 0x537e4 sr_ee [] kn_ee 45) [] = RES_ee2.
Proof. vm_compute. reflexivity. Qed.
End AXF_ee.


Module AXF_ee3.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

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
Definition sr_ee3 := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 2 (EAlu ALU_ADD e_sp0 (ELit (-96)))) 9 (ELit 0x97c00)) 10 (e_G)) 11 (EAluw ALU_SLL (ELit 1) e_idx)) 12 (e_sc)) 13 (EAlu ALU_OR (EExt true 0 4 e_avail) (EExt true 0 4 e_freed))).
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
    KWord (SA ACT 621800) 8 (ELit 0);
    KWord (SA e_G 0) 8 (ELit 0);
    KWord (SA e_G 8) 8 (ELit 0);
    KWord (SA e_sp0 (-8)) 8 e_ra;
    KWord (SA e_sp0 (-16)) 8 e_s0;
    KWord (SA e_sp0 (-24)) 8 e_s1;
    KWord (SA e_sp0 (-32)) 8 e_s2;
    KWord (SA e_sp0 (-40)) 8 e_s3;
    KWord (SA e_sp0 (-48)) 8 e_canary;
    KWord (SA (ELit 0) 0x97c00) 8 e_canary;
    KWr (SA e_G 0) (ELit 16);
    KWr (SA e_G 28) (ELit 4);
    KWr (SA ACT 621800) (ELit 8);
    KDisj STK (ELit 1024) (SA e_G 0) (ELit 40);
    KDisj STK (ELit 1024) (SA ACT 621800) (ELit 8);
    KDisj STK (ELit 1024) (SA (ELit 0) 0x97c00) (ELit 8);
    KDisj (SA e_G 0) (ELit 40) (SA (ELit 0) 0x97c00) (ELit 8);
    KDisj (SA e_G 0) (ELit 40) (SA ACT 621800) (ELit 8);
    KDisj (SA ACT 621800) (ELit 8) (SA (ELit 0) 0x97c00) (ELit 8) ].
Definition scr_ee3 : scripts := SCR [] [] [].
Definition ss_ee3 := SS 0x537e4 sr_ee3 [] kn_ee3 45.
Definition RUN_ee3 := sym_exec SEGS 200 true [] scr_ee3 ss_ee3 [].

Definition scr_pee3 : scripts := SCR [false; false; false; false] [] [].
Definition RES_pee3 := Eval vm_compute in sym_exec SEGS 200 true [] scr_pee3 ss_ee3 [].
Lemma RES_pee3_ok : sym_exec SEGS 200 true [] scr_pee3 (SS 0x537e4 sr_ee3 [] kn_ee3 45) [] = RES_pee3.
Proof. vm_compute. reflexivity. Qed.
End AXF_ee3.


Module AXF_ee4.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

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
Definition sr_ee4 := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 2 (EAlu ALU_ADD e_sp0 (ELit (-96)))) 9 (ELit 0x97c00)) 10 (e_G)) 11 (EAluw ALU_SLL (ELit 1) e_idx)) 12 (e_sc)) 13 (EAlu ALU_OR (EExt true 0 4 e_avail) (EExt true 0 4 e_freed))).
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
    KWord (SA ACT 621800) 8 e_H;
    KWord (SA e_G 0) 8 (ELit 0);
    KWord (SA e_G 8) 8 (ELit 0);
    KWord (SA e_H 0) 8 e_HP;
    KWord (SA e_sp0 (-8)) 8 e_ra;
    KWord (SA e_sp0 (-16)) 8 e_s0;
    KWord (SA e_sp0 (-24)) 8 e_s1;
    KWord (SA e_sp0 (-32)) 8 e_s2;
    KWord (SA e_sp0 (-40)) 8 e_s3;
    KWord (SA e_sp0 (-48)) 8 e_canary;
    KWord (SA (ELit 0) 0x97c00) 8 e_canary;
    KWr (SA e_G 0) (ELit 16);
    KWr (SA e_G 28) (ELit 4);
    KWr (SA e_H 0) (ELit 8);
    KWr (SA e_HP 8) (ELit 8);
    KDisj STK (ELit 1024) (SA e_G 0) (ELit 40);
    KDisj STK (ELit 1024) (SA ACT 621800) (ELit 8);
    KDisj STK (ELit 1024) (SA (ELit 0) 0x97c00) (ELit 8);
    KDisj STK (ELit 1024) (SA e_H 0) (ELit 40);
    KDisj STK (ELit 1024) (SA e_HP 0) (ELit 40);
    KDisj (SA e_G 0) (ELit 40) (SA (ELit 0) 0x97c00) (ELit 8);
    KDisj (SA e_G 0) (ELit 40) (SA ACT 621800) (ELit 8);
    KDisj (SA e_G 0) (ELit 40) (SA e_H 0) (ELit 40);
    KDisj (SA e_G 0) (ELit 40) (SA e_HP 0) (ELit 40);
    KDisj (SA e_H 0) (ELit 40) (SA (ELit 0) 0x97c00) (ELit 8);
    KDisj (SA e_HP 0) (ELit 40) (SA (ELit 0) 0x97c00) (ELit 8);
    KDisj (SA e_H 0) (ELit 40) (SA ACT 621800) (ELit 8);
    KDisj (SA e_HP 0) (ELit 40) (SA ACT 621800) (ELit 8) ].
Definition scr_ee4 : scripts := SCR [] [] [].
Definition ss_ee4 := SS 0x537e4 sr_ee4 [] kn_ee4 46.
Definition RUN_ee4 := sym_exec SEGS 200 true [] scr_ee4 ss_ee4 [].

Definition scr_pee4 : scripts := SCR [false; false; false; false; false] [] [].
Definition RES_pee4 := Eval vm_compute in sym_exec SEGS 200 true [] scr_pee4 ss_ee4 [].
Lemma RES_pee4_ok : sym_exec SEGS 200 true [] scr_pee4 (SS 0x537e4 sr_ee4 [] kn_ee4 46) [] = RES_pee4.
Proof. vm_compute. reflexivity. Qed.
End AXF_ee4.

Import ListNotations AX2 AX2S.

Module AXF_dec63.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_G := EVar 32.
Definition e_idx := EVar 33.
Definition e_W := EVar 34.
Definition e_avail := EVar 35.
Definition e_freed := EVar 36.
Definition e_sp0 := EVar 37.
Definition e_canary := EVar 38.
Definition STK := SA e_sp0 (-1024).
Definition sr_dec63 := (sr_upd (sr_upd (sr_upd sr_id 2 (e_sp0)) 10 (e_G)) 11 (e_idx)).
Definition kn_dec63 : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KWr STK (ELit 1024);
    KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange e_idx 0 31;
    KRange e_avail 0 (2^32-1);
    KRange e_freed 0 (2^32-1);
    KWord (SA e_G 24) 4 e_avail;
    KWord (SA e_G 28) 4 e_freed;
    KWord (SA e_G 32) 8 e_W;
    KWord (SA (ELit 0) 0x65b58) 8 (ELit 0x97c00);
    KWord (SA (ELit 0) 0x97c00) 8 e_canary;
    KDisj STK (ELit 1024) (SA e_G 0) (ELit 40) ].
Definition scr_dec63 : scripts := SCR [] [] [].
Definition ss_dec63 := SS 0x53688 sr_dec63 [] kn_dec63 39.
Definition RUN_dec63 := sym_exec SEGS 200 true [0x5379c; 0x537e4] scr_dec63 ss_dec63 [].

Definition scr_pd63 : scripts := SCR [false; false; true] [] [].
Definition RES_pd63 := Eval vm_compute in sym_exec SEGS 200 true [0x5379c; 0x537e4] scr_pd63 ss_dec63 [].
Lemma RES_pd63_ok : sym_exec SEGS 200 true [0x5379c; 0x537e4] scr_pd63 (SS 0x53688 sr_dec63 [] kn_dec63 39) [] = RES_pd63.
Proof. vm_compute. reflexivity. Qed.
End AXF_dec63.

Module AXF_dec63z.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section DEC63.
Context {fx : FPState}.

Definition VALS_dec63 (G idx W avail freed sp0 canary : Z) : list Z := [G; idx; W; avail; freed; sp0; canary].

Record dec63_pre (regs : bvmap 5 word) (m : word -> option byte) (G idx W avail freed sp0 canary : Z) : Prop := {
  dec63_R2 : getr regs 2 = wa sp0 ;
  dec63_R10 : getr regs 10 = wa G ;
  dec63_R11 : getr regs 11 = wa idx ;
  dec63_HSTK : stk_ok SEGS m (wa sp0) 1024 ;
  dec63_rng_G : 1 <= G <= 2^63-1 ;
  dec63_rng_idx : 0 <= idx <= 31 ;
  dec63_rng_W : 0 <= W <= 2^64-1 ;
  dec63_rng_avail : 0 <= avail <= 2^32-1 ;
  dec63_rng_freed : 0 <= freed <= 2^32-1 ;
  dec63_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  dec63_rng_canary : 0 <= canary <= 2^64-1 ;
  dec63_ka1 : sp0 mod 16 = 0 ;
  dec63_ka4 : G mod 8 = 0 ;
  dec63_kw8 : rdn SEGS m (wa (G + 24)) 4 = Some (word_to_le_bytes 4 (wa avail)) ;
  dec63_kw9 : rdn SEGS m (wa (G + 28)) 4 = Some (word_to_le_bytes 4 (wa freed)) ;
  dec63_kw10 : rdn SEGS m (wa (G + 32)) 8 = Some (word_to_le_bytes 8 (wa W)) ;
  dec63_kw11 : rdn SEGS m (wa (0 + 416600)) 8 = Some (word_to_le_bytes 8 (wa 621568)) ;
  dec63_kw12 : rdn SEGS m (wa (0 + 621568)) 8 = Some (word_to_le_bytes 8 (wa canary)) ;
  dec63_kd13 : sp0 + -1024 + 1024 <= G + 0 \/ G + 0 + 40 <= sp0 + -1024
}.


#[using="Type"] Lemma dec63_setup : forall regs m G idx W avail freed sp0 canary, dec63_pre regs m G idx W avail freed sp0 canary ->
  regs_ok (Ez regs (VALS_dec63 G idx W avail freed sp0 canary)) AXF_dec63.sr_dec63 regs /\ know_ok SEGS (Ez regs (VALS_dec63 G idx W avail freed sp0 canary)) m AXF_dec63.kn_dec63.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G idx W avail freed sp0 canary P. destruct P as [dec63_R2 dec63_R10 dec63_R11 dec63_HSTK dec63_rng_G dec63_rng_idx dec63_rng_W dec63_rng_avail dec63_rng_freed dec63_rng_sp0 dec63_rng_canary dec63_ka1 dec63_ka4 dec63_kw8 dec63_kw9 dec63_kw10 dec63_kw11 dec63_kw12 dec63_kd13].
  set (E := Ez regs (VALS_dec63 G idx W avail freed sp0 canary)).
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = idx) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = W) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = avail) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = freed) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = canary) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_dec63.sr_dec63.
    apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 2); [apply regs_ok_id|]|]|].
    - rewrite dec63_R2. reflexivity.
    - rewrite dec63_R10. reflexivity.
    - rewrite dec63_R11. reflexivity. }
  unfold know_ok, AXF_dec63.kn_dec63.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_dec63.e_sp0 (wa sp0) 1024); [reflexivity | assumption | rewrite u_wa_small by lia; lia])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_dec63.e_G AXF_dec63.e_idx AXF_dec63.e_W AXF_dec63.e_avail AXF_dec63.e_freed AXF_dec63.e_sp0 AXF_dec63.e_canary AXF_dec63.STK a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36, ?Z37, ?Z38.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range G _ _ dec63_rng_G eq_refl eq_refl), ?(mod64_of_range idx _ _ dec63_rng_idx eq_refl eq_refl), ?(mod64_of_range avail _ _ dec63_rng_avail eq_refl eq_refl), ?(mod64_of_range freed _ _ dec63_rng_freed eq_refl eq_refl), ?(mod64_of_range sp0 _ _ dec63_rng_sp0 eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - dec63_rng_G dec63_rng_idx dec63_rng_W dec63_rng_avail dec63_rng_freed dec63_rng_sp0 dec63_rng_canary dec63_ka1 dec63_ka4; lia).
  all: first [(clear - dec63_rng_G dec63_rng_idx dec63_rng_W dec63_rng_avail dec63_rng_freed dec63_rng_sp0 dec63_rng_canary dec63_ka1 dec63_ka4 dec63_kd13; lia) | lia].
Qed.


Definition dec63_mem_pd63 (m : word -> option byte) (regs : bvmap 5 word) (G idx W avail freed sp0 canary : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (sp0 + -8)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 1))))))) (wa (sp0 + -16)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 8))))))) (wa (sp0 + -24)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 9))))))) (wa (sp0 + -32)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 18))))))) (wa (sp0 + -40)) (word_to_le_bytes 8 (wa (bv_unsigned (getr regs (Z_to_bv 5 (Z.of_nat 19))))))) (wa (sp0 + -48)) (word_to_le_bytes 8 (wa canary)).

#[using="Type"] Theorem dec63_pd63 : forall regs m rom G idx W avail freed sp0 canary, dec63_pre regs m G idx W avail freed sp0 canary ->
  scs_denot SEGS m (Ez regs (VALS_dec63 G idx W avail freed sp0 canary)) (snd (fst AXF_dec63.RES_pd63)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53688) m rom) (mkst R (wa 0x5379c) (dec63_mem_pd63 m regs G idx W avail freed sp0 canary) rom) /\
    getr R 2 = wa (sp0 + -96) /\ getr R 9 = wa 621568 /\ getr R 10 = wa G /\ getr R 12 = wa (Z.shiftr (((4503599627370496 * W)) mod 2^64) 58) /\ getr R 14 = wa 47 /\ getr R 15 = wa W /\ getr R 16 = wa 620272 /\ getr R 18 = wa 621720 /\ (forall k, In k [1; 3; 4; 5; 6; 7; 8; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G idx W avail freed sp0 canary P Hsc. destruct (dec63_setup regs m G idx W avail freed sp0 canary P) as [HR HK].
  set (E := Ez regs (VALS_dec63 G idx W avail freed sp0 canary)) in *. destruct P as [dec63_R2 dec63_R10 dec63_R11 dec63_HSTK dec63_rng_G dec63_rng_idx dec63_rng_W dec63_rng_avail dec63_rng_freed dec63_rng_sp0 dec63_rng_canary dec63_ka1 dec63_ka4 dec63_kw8 dec63_kw9 dec63_kw10 dec63_kw11 dec63_kw12 dec63_kd13].
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = idx) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = W) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = avail) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = freed) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z37 : bv_unsigned (ev E 37) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = canary) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 200 [0x5379c; 0x537e4] AXF_dec63.scr_pd63 0x53688 AXF_dec63.sr_dec63 AXF_dec63.kn_dec63 39 _ _ _ E m rom regs AXF_dec63.RES_pd63_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_dec63.RES_pd63 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (dec63_mem_pd63 m regs G idx W avail freed sp0 canary) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold dec63_mem_pd63. repeat (apply (f_equal3 wbytes)); try reflexivity.
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

End DEC63.
End AXF_dec63z.

Module AXF_m1n.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_sc := EVar 32.
Definition e_G1 := EVar 33.
Definition e_freed1 := EVar 34.
Definition e_W1 := EVar 35.
Definition ACT := SA (EMd M_MUL (ELit 8) e_sc) 621800.
Definition sr_m1n := (sr_upd (sr_upd sr_id 10 (e_G1)) 21 (EAlu ALU_ADD (EMd M_MUL (ELit 8) e_sc) (ELit 621800))).
Definition kn_m1n : list kentry :=
  [ KRange e_sc 0 47;
    KRange e_G1 1 (2^63-1);
    KAlign e_G1 8;
    KRange e_freed1 0 (2^32-1);
    KRange e_W1 0 (2^63-1);
    KWord (SA e_G1 28) 4 e_freed1;
    KWord (SA e_G1 32) 8 e_W1 ].
Definition scr_m1n : scripts := SCR [false; true] [] [].
Definition ss_m1n := SS 0x54170 sr_m1n [] kn_m1n 36.
Definition RUN_m1n := sym_exec SEGS 100 true [0x5419c] scr_m1n ss_m1n [].

Definition scr_pm1n : scripts := SCR [false; true] [] [].
Definition RES_pm1n := Eval vm_compute in sym_exec SEGS 100 true [0x5419c] scr_pm1n ss_m1n [].
Lemma RES_pm1n_ok : sym_exec SEGS 100 true [0x5419c] scr_pm1n (SS 0x54170 sr_m1n [] kn_m1n 36) [] = RES_pm1n.
Proof. vm_compute. reflexivity. Qed.
End AXF_m1n.

Module AXF_m1nz.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section M1N.
Context {fx : FPState}.

Definition VALS_m1n (sc G1 freed1 W1 : Z) : list Z := [sc; G1; freed1; W1].

Record m1n_pre (regs : bvmap 5 word) (m : word -> option byte) (sc G1 freed1 W1 : Z) : Prop := {
  m1n_R10 : getr regs 10 = wa G1 ;
  m1n_R21 : getr regs 21 = wa ((8 * sc) + 621800) ;
  m1n_rng_sc : 0 <= sc <= 47 ;
  m1n_rng_G1 : 1 <= G1 <= 2^63-1 ;
  m1n_rng_freed1 : 0 <= freed1 <= 2^32-1 ;
  m1n_rng_W1 : 0 <= W1 <= 2^63-1 ;
  m1n_ka2 : G1 mod 8 = 0 ;
  m1n_kw5 : rdn SEGS m (wa (G1 + 28)) 4 = Some (word_to_le_bytes 4 (wa freed1)) ;
  m1n_kw6 : rdn SEGS m (wa (G1 + 32)) 8 = Some (word_to_le_bytes 8 (wa W1))
}.


#[using="Type"] Lemma m1n_setup : forall regs m sc G1 freed1 W1, m1n_pre regs m sc G1 freed1 W1 ->
  regs_ok (Ez regs (VALS_m1n sc G1 freed1 W1)) AXF_m1n.sr_m1n regs /\ know_ok SEGS (Ez regs (VALS_m1n sc G1 freed1 W1)) m AXF_m1n.kn_m1n.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sc G1 freed1 W1 P. destruct P as [m1n_R10 m1n_R21 m1n_rng_sc m1n_rng_G1 m1n_rng_freed1 m1n_rng_W1 m1n_ka2 m1n_kw5 m1n_kw6].
  set (E := Ez regs (VALS_m1n sc G1 freed1 W1)).
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = G1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = freed1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = W1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_m1n.sr_m1n.
    apply (regs_ok_pin E _ regs 21); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|].
    - rewrite m1n_R10. reflexivity.
    - rewrite m1n_R21, zeval_sound. cbn [zeval edenot AXF_m1n.e_sc AXF_m1n.e_G1 AXF_m1n.e_freed1 AXF_m1n.e_W1 AXF_m1n.ACT]. rewrite ?Z32, ?Z33, ?Z34, ?Z35. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)]. }
  unfold know_ok, AXF_m1n.kn_m1n.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_m1n.e_sc AXF_m1n.e_G1 AXF_m1n.e_freed1 AXF_m1n.e_W1 AXF_m1n.ACT a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sc _ _ m1n_rng_sc eq_refl eq_refl), ?(mod64_of_range G1 _ _ m1n_rng_G1 eq_refl eq_refl), ?(mod64_of_range freed1 _ _ m1n_rng_freed1 eq_refl eq_refl), ?(mod64_of_range W1 _ _ m1n_rng_W1 eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - m1n_rng_sc m1n_rng_G1 m1n_rng_freed1 m1n_rng_W1 m1n_ka2; lia).
  all: first [lia].
Qed.


Definition m1n_mem_pm1n (m : word -> option byte) (regs : bvmap 5 word) (sc G1 freed1 W1 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem m1n_pm1n : forall regs m rom sc G1 freed1 W1, m1n_pre regs m sc G1 freed1 W1 ->
  scs_denot SEGS m (Ez regs (VALS_m1n sc G1 freed1 W1)) (snd (fst AXF_m1n.RES_pm1n)) ->
  exists R, msteps SEGS (mkst regs (wa 0x54170) m rom) (mkst R (wa 0x5419c) (m1n_mem_pm1n m regs sc G1 freed1 W1) rom) /\
    getr R 10 = wa G1 /\ getr R 12 = wa (Z.land W1 32) /\ getr R 13 = wa (ext_Z true 0 4 freed1) /\ getr R 14 = wa 2 /\ getr R 21 = wa ((8 * sc) + 621800) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 15; 16; 17; 18; 19; 20; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc G1 freed1 W1 P Hsc. destruct (m1n_setup regs m sc G1 freed1 W1 P) as [HR HK].
  set (E := Ez regs (VALS_m1n sc G1 freed1 W1)) in *. destruct P as [m1n_R10 m1n_R21 m1n_rng_sc m1n_rng_G1 m1n_rng_freed1 m1n_rng_W1 m1n_ka2 m1n_kw5 m1n_kw6].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = G1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = freed1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = W1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x5419c] AXF_m1n.scr_pm1n 0x54170 AXF_m1n.sr_m1n AXF_m1n.kn_m1n 36 _ _ _ E m rom regs AXF_m1n.RES_pm1n_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_m1n.RES_pm1n fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (m1n_mem_pm1n m regs sc G1 freed1 W1) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold m1n_mem_pm1n. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End M1N.
End AXF_m1nz.

Module AXF_m2a.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_sc := EVar 32.
Definition e_G2 := EVar 33.
Definition e_freed2 := EVar 34.
Definition e_mem2 := EVar 35.
Definition e_hb := EVar 36.
Definition sr_m2a := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 10 (e_G2)) 13 (EExt true 0 4 e_freed2)) 14 (ELit 2)) 21 (EAlu ALU_ADD (EMd M_MUL (ELit 8) e_sc) (ELit 621800))).
Definition kn_m2a : list kentry :=
  [ KRange e_sc 0 47;
    KRange e_G2 1 (2^63-1);
    KAlign e_G2 8;
    KRange e_freed2 0 (2^32-1);
    KRange e_mem2 1 (2^63-1);
    KRange e_hb 0 255;
    KWord (SA e_G2 16) 8 e_mem2;
    KWord (SA e_mem2 8) 1 e_hb;
    KWord (SA e_G2 24) 4 (ELit 0) ].
Definition scr_m2a : scripts := SCR [true] [] [].
Definition ss_m2a := SS 0x5419c sr_m2a [] kn_m2a 37.
Definition RUN_m2a := sym_exec SEGS 100 true [0x541d0] scr_m2a ss_m2a [].

Definition scr_pm2a : scripts := SCR [true] [] [].
Definition RES_pm2a := Eval vm_compute in sym_exec SEGS 100 true [0x541d0] scr_pm2a ss_m2a [].
Lemma RES_pm2a_ok : sym_exec SEGS 100 true [0x541d0] scr_pm2a (SS 0x5419c sr_m2a [] kn_m2a 37) [] = RES_pm2a.
Proof. vm_compute. reflexivity. Qed.
End AXF_m2a.

Module AXF_m2az.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section M2A.
Context {fx : FPState}.

Definition VALS_m2a (sc G2 freed2 mem2 hb : Z) : list Z := [sc; G2; freed2; mem2; hb].

Record m2a_pre (regs : bvmap 5 word) (m : word -> option byte) (sc G2 freed2 mem2 hb : Z) : Prop := {
  m2a_R10 : getr regs 10 = wa G2 ;
  m2a_R13 : getr regs 13 = wa (ext_Z true 0 4 freed2) ;
  m2a_R14 : getr regs 14 = wa 2 ;
  m2a_R21 : getr regs 21 = wa ((8 * sc) + 621800) ;
  m2a_rng_sc : 0 <= sc <= 47 ;
  m2a_rng_G2 : 1 <= G2 <= 2^63-1 ;
  m2a_rng_freed2 : 0 <= freed2 <= 2^32-1 ;
  m2a_rng_mem2 : 1 <= mem2 <= 2^63-1 ;
  m2a_rng_hb : 0 <= hb <= 255 ;
  m2a_ka2 : G2 mod 8 = 0 ;
  m2a_kw6 : rdn SEGS m (wa (G2 + 16)) 8 = Some (word_to_le_bytes 8 (wa mem2)) ;
  m2a_kw7 : rdn SEGS m (wa (mem2 + 8)) 1 = Some (word_to_le_bytes 1 (wa hb)) ;
  m2a_kw8 : rdn SEGS m (wa (G2 + 24)) 4 = Some (word_to_le_bytes 4 (wa 0))
}.


#[using="Type"] Lemma m2a_setup : forall regs m sc G2 freed2 mem2 hb, m2a_pre regs m sc G2 freed2 mem2 hb ->
  regs_ok (Ez regs (VALS_m2a sc G2 freed2 mem2 hb)) AXF_m2a.sr_m2a regs /\ know_ok SEGS (Ez regs (VALS_m2a sc G2 freed2 mem2 hb)) m AXF_m2a.kn_m2a.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sc G2 freed2 mem2 hb P. destruct P as [m2a_R10 m2a_R13 m2a_R14 m2a_R21 m2a_rng_sc m2a_rng_G2 m2a_rng_freed2 m2a_rng_mem2 m2a_rng_hb m2a_ka2 m2a_kw6 m2a_kw7 m2a_kw8].
  set (E := Ez regs (VALS_m2a sc G2 freed2 mem2 hb)).
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = G2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = freed2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = mem2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = hb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_m2a.sr_m2a.
    apply (regs_ok_pin E _ regs 21); [apply (regs_ok_pin E _ regs 14); [apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|]|]|].
    - rewrite m2a_R10. reflexivity.
    - rewrite m2a_R13, zeval_sound. cbn [zeval edenot AXF_m2a.e_sc AXF_m2a.e_G2 AXF_m2a.e_freed2 AXF_m2a.e_mem2 AXF_m2a.e_hb]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite m2a_R14. reflexivity.
    - rewrite m2a_R21, zeval_sound. cbn [zeval edenot AXF_m2a.e_sc AXF_m2a.e_G2 AXF_m2a.e_freed2 AXF_m2a.e_mem2 AXF_m2a.e_hb]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)]. }
  unfold know_ok, AXF_m2a.kn_m2a.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_m2a.e_sc AXF_m2a.e_G2 AXF_m2a.e_freed2 AXF_m2a.e_mem2 AXF_m2a.e_hb a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sc _ _ m2a_rng_sc eq_refl eq_refl), ?(mod64_of_range G2 _ _ m2a_rng_G2 eq_refl eq_refl), ?(mod64_of_range freed2 _ _ m2a_rng_freed2 eq_refl eq_refl), ?(mod64_of_range mem2 _ _ m2a_rng_mem2 eq_refl eq_refl), ?(mod64_of_range hb _ _ m2a_rng_hb eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - m2a_rng_sc m2a_rng_G2 m2a_rng_freed2 m2a_rng_mem2 m2a_rng_hb m2a_ka2; lia).
  all: first [lia].
Qed.


Definition m2a_mem_pm2a (m : word -> option byte) (regs : bvmap 5 word) (sc G2 freed2 mem2 hb : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem m2a_pm2a : forall regs m rom sc G2 freed2 mem2 hb, m2a_pre regs m sc G2 freed2 mem2 hb ->
  scs_denot SEGS m (Ez regs (VALS_m2a sc G2 freed2 mem2 hb)) (snd (fst AXF_m2a.RES_pm2a)) ->
  exists R, msteps SEGS (mkst regs (wa 0x5419c) m rom) (mkst R (wa 0x541d0) (m2a_mem_pm2a m regs sc G2 freed2 mem2 hb) rom) /\
    getr R 10 = wa G2 /\ getr R 11 = wa 0 /\ getr R 12 = wa hb /\ getr R 21 = wa ((8 * sc) + 621800) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 15; 16; 17; 18; 19; 20; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc G2 freed2 mem2 hb P Hsc. destruct (m2a_setup regs m sc G2 freed2 mem2 hb P) as [HR HK].
  set (E := Ez regs (VALS_m2a sc G2 freed2 mem2 hb)) in *. destruct P as [m2a_R10 m2a_R13 m2a_R14 m2a_R21 m2a_rng_sc m2a_rng_G2 m2a_rng_freed2 m2a_rng_mem2 m2a_rng_hb m2a_ka2 m2a_kw6 m2a_kw7 m2a_kw8].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = G2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = freed2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = mem2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = hb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x541d0] AXF_m2a.scr_pm2a 0x5419c AXF_m2a.sr_m2a AXF_m2a.kn_m2a 37 _ _ _ E m rom regs AXF_m2a.RES_pm2a_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_m2a.RES_pm2a fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (m2a_mem_pm2a m regs sc G2 freed2 mem2 hb) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold m2a_mem_pm2a. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End M2A.
End AXF_m2az.

Module AXF_m2c.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_sc := EVar 32.
Definition e_G2 := EVar 33.
Definition e_freed2 := EVar 34.
Definition e_mem2 := EVar 35.
Definition e_hb := EVar 36.
Definition sr_m2c := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 10 (e_G2)) 13 (EExt true 0 4 e_freed2)) 14 (ELit 2)) 21 (EAlu ALU_ADD (EMd M_MUL (ELit 8) e_sc) (ELit 621800))).
Definition kn_m2c : list kentry :=
  [ KRange e_sc 0 47;
    KRange e_G2 1 (2^63-1);
    KAlign e_G2 8;
    KRange e_freed2 0 (2^32-1);
    KRange e_mem2 1 (2^63-1);
    KRange e_hb 0 255;
    KWord (SA e_G2 16) 8 e_mem2;
    KWord (SA e_mem2 8) 1 e_hb;
    KWord (SA e_G2 8) 8 e_G2 ].
Definition scr_m2c : scripts := SCR [false] [] [].
Definition ss_m2c := SS 0x5419c sr_m2c [] kn_m2c 37.
Definition RUN_m2c := sym_exec SEGS 100 true [0x5457c] scr_m2c ss_m2c [].

Definition scr_pm2c : scripts := SCR [false] [] [].
Definition RES_pm2c := Eval vm_compute in sym_exec SEGS 100 true [0x5457c] scr_pm2c ss_m2c [].
Lemma RES_pm2c_ok : sym_exec SEGS 100 true [0x5457c] scr_pm2c (SS 0x5419c sr_m2c [] kn_m2c 37) [] = RES_pm2c.
Proof. vm_compute. reflexivity. Qed.
End AXF_m2c.

Module AXF_m2cz.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section M2C.
Context {fx : FPState}.

Definition VALS_m2c (sc G2 freed2 mem2 hb : Z) : list Z := [sc; G2; freed2; mem2; hb].

Record m2c_pre (regs : bvmap 5 word) (m : word -> option byte) (sc G2 freed2 mem2 hb : Z) : Prop := {
  m2c_R10 : getr regs 10 = wa G2 ;
  m2c_R13 : getr regs 13 = wa (ext_Z true 0 4 freed2) ;
  m2c_R14 : getr regs 14 = wa 2 ;
  m2c_R21 : getr regs 21 = wa ((8 * sc) + 621800) ;
  m2c_rng_sc : 0 <= sc <= 47 ;
  m2c_rng_G2 : 1 <= G2 <= 2^63-1 ;
  m2c_rng_freed2 : 0 <= freed2 <= 2^32-1 ;
  m2c_rng_mem2 : 1 <= mem2 <= 2^63-1 ;
  m2c_rng_hb : 0 <= hb <= 255 ;
  m2c_ka2 : G2 mod 8 = 0 ;
  m2c_kw6 : rdn SEGS m (wa (G2 + 16)) 8 = Some (word_to_le_bytes 8 (wa mem2)) ;
  m2c_kw7 : rdn SEGS m (wa (mem2 + 8)) 1 = Some (word_to_le_bytes 1 (wa hb)) ;
  m2c_kw8 : rdn SEGS m (wa (G2 + 8)) 8 = Some (word_to_le_bytes 8 (wa G2))
}.


#[using="Type"] Lemma m2c_setup : forall regs m sc G2 freed2 mem2 hb, m2c_pre regs m sc G2 freed2 mem2 hb ->
  regs_ok (Ez regs (VALS_m2c sc G2 freed2 mem2 hb)) AXF_m2c.sr_m2c regs /\ know_ok SEGS (Ez regs (VALS_m2c sc G2 freed2 mem2 hb)) m AXF_m2c.kn_m2c.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sc G2 freed2 mem2 hb P. destruct P as [m2c_R10 m2c_R13 m2c_R14 m2c_R21 m2c_rng_sc m2c_rng_G2 m2c_rng_freed2 m2c_rng_mem2 m2c_rng_hb m2c_ka2 m2c_kw6 m2c_kw7 m2c_kw8].
  set (E := Ez regs (VALS_m2c sc G2 freed2 mem2 hb)).
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = G2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = freed2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = mem2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = hb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_m2c.sr_m2c.
    apply (regs_ok_pin E _ regs 21); [apply (regs_ok_pin E _ regs 14); [apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|]|]|].
    - rewrite m2c_R10. reflexivity.
    - rewrite m2c_R13, zeval_sound. cbn [zeval edenot AXF_m2c.e_sc AXF_m2c.e_G2 AXF_m2c.e_freed2 AXF_m2c.e_mem2 AXF_m2c.e_hb]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite m2c_R14. reflexivity.
    - rewrite m2c_R21, zeval_sound. cbn [zeval edenot AXF_m2c.e_sc AXF_m2c.e_G2 AXF_m2c.e_freed2 AXF_m2c.e_mem2 AXF_m2c.e_hb]. rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)]. }
  unfold know_ok, AXF_m2c.kn_m2c.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_m2c.e_sc AXF_m2c.e_G2 AXF_m2c.e_freed2 AXF_m2c.e_mem2 AXF_m2c.e_hb a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sc _ _ m2c_rng_sc eq_refl eq_refl), ?(mod64_of_range G2 _ _ m2c_rng_G2 eq_refl eq_refl), ?(mod64_of_range freed2 _ _ m2c_rng_freed2 eq_refl eq_refl), ?(mod64_of_range mem2 _ _ m2c_rng_mem2 eq_refl eq_refl), ?(mod64_of_range hb _ _ m2c_rng_hb eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - m2c_rng_sc m2c_rng_G2 m2c_rng_freed2 m2c_rng_mem2 m2c_rng_hb m2c_ka2; lia).
  all: first [lia].
Qed.


Definition m2c_mem_pm2c (m : word -> option byte) (regs : bvmap 5 word) (sc G2 freed2 mem2 hb : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem m2c_pm2c : forall regs m rom sc G2 freed2 mem2 hb, m2c_pre regs m sc G2 freed2 mem2 hb ->
  scs_denot SEGS m (Ez regs (VALS_m2c sc G2 freed2 mem2 hb)) (snd (fst AXF_m2c.RES_pm2c)) ->
  exists R, msteps SEGS (mkst regs (wa 0x5419c) m rom) (mkst R (wa 0x5457c) (m2c_mem_pm2c m regs sc G2 freed2 mem2 hb) rom) /\
    getr R 10 = wa G2 /\ getr R 11 = wa mem2 /\ getr R 12 = wa hb /\ getr R 13 = wa G2 /\ getr R 21 = wa ((8 * sc) + 621800) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 15; 16; 17; 18; 19; 20; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc G2 freed2 mem2 hb P Hsc. destruct (m2c_setup regs m sc G2 freed2 mem2 hb P) as [HR HK].
  set (E := Ez regs (VALS_m2c sc G2 freed2 mem2 hb)) in *. destruct P as [m2c_R10 m2c_R13 m2c_R14 m2c_R21 m2c_rng_sc m2c_rng_G2 m2c_rng_freed2 m2c_rng_mem2 m2c_rng_hb m2c_ka2 m2c_kw6 m2c_kw7 m2c_kw8].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = G2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = freed2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = mem2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = hb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x5457c] AXF_m2c.scr_pm2c 0x5419c AXF_m2c.sr_m2c AXF_m2c.kn_m2c 37 _ _ _ E m rom regs AXF_m2c.RES_pm2c_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_m2c.RES_pm2c fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (m2c_mem_pm2c m regs sc G2 freed2 mem2 hb) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold m2c_mem_pm2c. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End M2C.
End AXF_m2cz.

Module AXF_mas.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_n := EVar 32.
Definition e_sc := EVar 33.
Definition e_idx := EVar 34.
Definition e_G := EVar 35.
Definition ACT := EMd M_MUL (ELit 8) e_sc.
Definition sr_mas := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 8 (e_n)) 9 (ELit 621712)) 10 (e_idx)) 18 (e_sc)) 20 (e_sc)).
Definition kn_mas : list kentry :=
  [ KRange e_n 1 131051;
    KRange e_sc 0 47;
    KRange e_idx 0 31;
    KRange e_G 1 (2^63-1);
    KWord (SA ACT 621800) 8 e_G ].
Definition scr_mas : scripts := SCR [] [] [].
Definition ss_mas := SS 0x54048 sr_mas [] kn_mas 36.
Definition RUN_mas := sym_exec SEGS 100 true [0x5405c; 0x54098] scr_mas ss_mas [].

Definition scr_pmas : scripts := SCR [false] [] [].
Definition RES_pmas := Eval vm_compute in sym_exec SEGS 100 true [0x5405c; 0x54098] scr_pmas ss_mas [].
Lemma RES_pmas_ok : sym_exec SEGS 100 true [0x5405c; 0x54098] scr_pmas (SS 0x54048 sr_mas [] kn_mas 36) [] = RES_pmas.
Proof. vm_compute. reflexivity. Qed.
End AXF_mas.

Module AXF_masz.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section MAS.
Context {fx : FPState}.

Definition VALS_mas (n sc idx G : Z) : list Z := [n; sc; idx; G].

Record mas_pre (regs : bvmap 5 word) (m : word -> option byte) (n sc idx G : Z) : Prop := {
  mas_R8 : getr regs 8 = wa n ;
  mas_R9 : getr regs 9 = wa 621712 ;
  mas_R10 : getr regs 10 = wa idx ;
  mas_R18 : getr regs 18 = wa sc ;
  mas_R20 : getr regs 20 = wa sc ;
  mas_rng_n : 1 <= n <= 131051 ;
  mas_rng_sc : 0 <= sc <= 47 ;
  mas_rng_idx : 0 <= idx <= 31 ;
  mas_rng_G : 1 <= G <= 2^63-1 ;
  mas_kw4 : rdn SEGS m (wa (8 * sc + 621800)) 8 = Some (word_to_le_bytes 8 (wa G))
}.


#[using="Type"] Lemma mas_setup : forall regs m n sc idx G, mas_pre regs m n sc idx G ->
  regs_ok (Ez regs (VALS_mas n sc idx G)) AXF_mas.sr_mas regs /\ know_ok SEGS (Ez regs (VALS_mas n sc idx G)) m AXF_mas.kn_mas.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m n sc idx G P. destruct P as [mas_R8 mas_R9 mas_R10 mas_R18 mas_R20 mas_rng_n mas_rng_sc mas_rng_idx mas_rng_G mas_kw4].
  set (E := Ez regs (VALS_mas n sc idx G)).
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = idx) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mas.sr_mas.
    apply (regs_ok_pin E _ regs 20); [apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 8); [apply regs_ok_id|]|]|]|]|].
    - rewrite mas_R8. reflexivity.
    - rewrite mas_R9. reflexivity.
    - rewrite mas_R10. reflexivity.
    - rewrite mas_R18. reflexivity.
    - rewrite mas_R20. reflexivity. }
  unfold know_ok, AXF_mas.kn_mas.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mas.e_n AXF_mas.e_sc AXF_mas.e_idx AXF_mas.e_G AXF_mas.ACT a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range n _ _ mas_rng_n eq_refl eq_refl), ?(mod64_of_range sc _ _ mas_rng_sc eq_refl eq_refl), ?(mod64_of_range idx _ _ mas_rng_idx eq_refl eq_refl), ?(mod64_of_range G _ _ mas_rng_G eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - mas_rng_n mas_rng_sc mas_rng_idx mas_rng_G; lia).
  all: first [lia].
Qed.


Definition mas_mem_pmas (m : word -> option byte) (regs : bvmap 5 word) (n sc idx G : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mas_pmas : forall regs m rom n sc idx G, mas_pre regs m n sc idx G ->
  scs_denot SEGS m (Ez regs (VALS_mas n sc idx G)) (snd (fst AXF_mas.RES_pmas)) ->
  exists R, msteps SEGS (mkst regs (wa 0x54048) m rom) (mkst R (wa 0x5405c) (mas_mem_pmas m regs n sc idx G) rom) /\
    getr R 8 = wa n /\ getr R 9 = wa 621712 /\ getr R 10 = wa idx /\ getr R 18 = wa G /\ getr R 19 = wa idx /\ getr R 20 = wa sc /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom n sc idx G P Hsc. destruct (mas_setup regs m n sc idx G P) as [HR HK].
  set (E := Ez regs (VALS_mas n sc idx G)) in *. destruct P as [mas_R8 mas_R9 mas_R10 mas_R18 mas_R20 mas_rng_n mas_rng_sc mas_rng_idx mas_rng_G mas_kw4].
  assert (Z32 : bv_unsigned (ev E 32) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = idx) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x5405c; 0x54098] AXF_mas.scr_pmas 0x54048 AXF_mas.sr_mas AXF_mas.kn_mas 36 _ _ _ E m rom regs AXF_mas.RES_pmas_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mas.RES_pmas fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mas_mem_pmas m regs n sc idx G) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mas_mem_pmas. repeat (apply (f_equal3 wbytes)); try reflexivity.
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

End MAS.
End AXF_masz.

Module AXF_mi0.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_sp1 := EVar 32.
Definition e_auxv := EVar 33.
Definition sr_mi0 := (sr_upd (sr_upd sr_id 2 (e_sp1)) 19 (ELit 621712)).
Definition kn_mi0 : list kentry :=
  [ KRange e_sp1 (2^20) (2^47);
    KAlign e_sp1 16;
    KRange e_auxv 8 (2^47);
    KWord (SA (ELit 0) 621728) 4 (ELit 0);
    KWord (SA (ELit 0) 621608) 8 e_auxv;
    KWr (SA e_sp1 0) (ELit 8);
    KDisj (SA e_sp1 0) (ELit 8) (SA (ELit 0) 621608) (ELit 8) ].
Definition scr_mi0 : scripts := SCR [false] [] [].
Definition ss_mi0 := SS 0x53a94 sr_mi0 [] kn_mi0 34.
Definition RUN_mi0 := sym_exec SEGS 100 true [0x53ae4] scr_mi0 ss_mi0 [].

Definition scr_pmi0 : scripts := SCR [false] [] [].
Definition RES_pmi0 := Eval vm_compute in sym_exec SEGS 100 true [0x53ae4] scr_pmi0 ss_mi0 [].
Lemma RES_pmi0_ok : sym_exec SEGS 100 true [0x53ae4] scr_pmi0 (SS 0x53a94 sr_mi0 [] kn_mi0 34) [] = RES_pmi0.
Proof. vm_compute. reflexivity. Qed.
End AXF_mi0.

Module AXF_mi0z.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section MI0.
Context {fx : FPState}.

Definition VALS_mi0 (sp1 auxv : Z) : list Z := [sp1; auxv].

Record mi0_pre (regs : bvmap 5 word) (m : word -> option byte) (sp1 auxv : Z) : Prop := {
  mi0_R2 : getr regs 2 = wa sp1 ;
  mi0_R19 : getr regs 19 = wa 621712 ;
  mi0_rng_sp1 : 2^20 <= sp1 <= 2^47 ;
  mi0_rng_auxv : 8 <= auxv <= 2^47 ;
  mi0_ka1 : sp1 mod 16 = 0 ;
  mi0_kw3 : rdn SEGS m (wa (0 + 621728)) 4 = Some (word_to_le_bytes 4 (wa 0)) ;
  mi0_kw4 : rdn SEGS m (wa (0 + 621608)) 8 = Some (word_to_le_bytes 8 (wa auxv)) ;
  mi0_kwr5 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (sp1 + 0 + d)) k = true ;
  mi0_kd6 : sp1 + 0 + 8 <= 0 + 621608 \/ 0 + 621608 + 8 <= sp1 + 0
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
  exists R, msteps SEGS (mkst regs (wa 0x53a94) m rom) (mkst R (wa 0x53ae4) (mi0_mem_pmi0 m regs sp1 auxv) rom) /\
    getr R 2 = wa sp1 /\ getr R 8 = wa 621600 /\ getr R 9 = wa 0 /\ getr R 10 = wa auxv /\ getr R 11 = wa (1103515245 * sp1) /\ getr R 12 = wa sp1 /\ getr R 19 = wa 621712 /\ getr R 20 = wa 25 /\ (forall k, In k [1; 3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 18; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sp1 auxv P Hsc. destruct (mi0_setup regs m sp1 auxv P) as [HR HK].
  set (E := Ez regs (VALS_mi0 sp1 auxv)) in *. destruct P as [mi0_R2 mi0_R19 mi0_rng_sp1 mi0_rng_auxv mi0_ka1 mi0_kw3 mi0_kw4 mi0_kwr5 mi0_kd6].
  assert (Z32 : bv_unsigned (ev E 32) = sp1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = auxv) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53ae4] AXF_mi0.scr_pmi0 0x53a94 AXF_mi0.sr_mi0 AXF_mi0.kn_mi0 34 _ _ _ E m rom regs AXF_mi0.RES_pmi0_ok HR HK Hsc) as (R & HR' & _ & Hms).
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

Module AXF_mir.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

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
Definition ss_mir := SS 0x53ac8 sr_mir [] kn_mir 35.
Definition RUN_mir := sym_exec SEGS 100 true [0x600a8] scr_mir ss_mir [].

Definition scr_pmir : scripts := SCR [] [] [].
Definition RES_pmir := Eval vm_compute in sym_exec SEGS 100 true [0x600a8] scr_pmir ss_mir [].
Lemma RES_pmir_ok : sym_exec SEGS 100 true [0x600a8] scr_pmir (SS 0x53ac8 sr_mir [] kn_mir 35) [] = RES_pmir.
Proof. vm_compute. reflexivity. Qed.
End AXF_mir.

Module AXF_mirz.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

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
  exists R, msteps SEGS (mkst regs (wa 0x53ac8) m rom) (mkst R (wa 0x600a8) (mir_mem_pmir m regs ent rnd sp1) rom) /\
    getr R 1 = wa 342748 /\ getr R 2 = wa sp1 /\ getr R 10 = wa sp1 /\ getr R 11 = wa (rnd + 8) /\ getr R 12 = wa 8 /\ (forall k, In k [3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom ent rnd sp1 P Hsc. destruct (mir_setup regs m ent rnd sp1 P) as [HR HK].
  set (E := Ez regs (VALS_mir ent rnd sp1)) in *. destruct P as [mir_R2 mir_R12 mir_rng_ent mir_rng_rnd mir_rng_sp1 mir_ka1 mir_ka4 mir_kw5].
  assert (Z32 : bv_unsigned (ev E 32) = ent) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = rnd) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sp1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x600a8] AXF_mir.scr_pmir 0x53ac8 AXF_mir.sr_mir AXF_mir.kn_mir 35 _ _ _ E m rom regs AXF_mir.RES_pmir_ok HR HK Hsc) as (R & HR' & _ & Hms).
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
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_sp1 := EVar 32.
Definition e_sec := EVar 33.
Definition sr_mix := (sr_upd (sr_upd (sr_upd sr_id 2 (e_sp1)) 8 (ELit 621600)) 19 (ELit 621712)).
Definition kn_mix : list kentry :=
  [ KRange e_sp1 (2^20) (2^47);
    KAlign e_sp1 16;
    KRange e_sec 0 (2^64-1);
    KWord (SA e_sp1 0) 8 e_sec;
    KWord (SA (ELit 0) 621648) 8 (ELit 4096);
    KWord (SA (ELit 0) 621736) 8 (ELit 0);
    KWr (SA (ELit 0) 621720) (ELit 12);
    KDisj (SA (ELit 0) 621720) (ELit 12) (SA e_sp1 0) (ELit 8) ].
Definition scr_mix : scripts := SCR [] [] [].
Definition ss_mix := SS 0x53af4 sr_mix [] kn_mix 34.
Definition RUN_mix := sym_exec SEGS 100 true [0x53b4c] scr_mix ss_mix [].

Definition scr_pmix : scripts := SCR [] [] [].
Definition RES_pmix := Eval vm_compute in sym_exec SEGS 100 true [0x53b4c] scr_pmix ss_mix [].
Lemma RES_pmix_ok : sym_exec SEGS 100 true [0x53b4c] scr_pmix (SS 0x53af4 sr_mix [] kn_mix 34) [] = RES_pmix.
Proof. vm_compute. reflexivity. Qed.
End AXF_mix.

Module AXF_mixz.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section MIX.
Context {fx : FPState}.

Definition VALS_mix (sp1 sec : Z) : list Z := [sp1; sec].

Record mix_pre (regs : bvmap 5 word) (m : word -> option byte) (sp1 sec : Z) : Prop := {
  mix_R2 : getr regs 2 = wa sp1 ;
  mix_R8 : getr regs 8 = wa 621600 ;
  mix_R19 : getr regs 19 = wa 621712 ;
  mix_rng_sp1 : 2^20 <= sp1 <= 2^47 ;
  mix_rng_sec : 0 <= sec <= 2^64-1 ;
  mix_ka1 : sp1 mod 16 = 0 ;
  mix_kw3 : rdn SEGS m (wa (sp1 + 0)) 8 = Some (word_to_le_bytes 8 (wa sec)) ;
  mix_kw4 : rdn SEGS m (wa (0 + 621648)) 8 = Some (word_to_le_bytes 8 (wa 4096)) ;
  mix_kw5 : rdn SEGS m (wa (0 + 621736)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  mix_kwr6 : forall d k, 0 <= d -> d + Z.of_nat k <= 12 -> store_ok SEGS m (wa (0 + 621720 + d)) k = true ;
  mix_kd7 : 0 + 621720 + 12 <= sp1 + 0 \/ sp1 + 0 + 8 <= 0 + 621720
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
  wbytes (wbytes (m) (wa (0 + 621720)) (word_to_le_bytes 8 (wa sec))) (wa (0 + 621728)) (word_to_le_bytes 4 (wa 1)).

#[using="Type"] Theorem mix_pmix : forall regs m rom sp1 sec, mix_pre regs m sp1 sec ->
  scs_denot SEGS m (Ez regs (VALS_mix sp1 sec)) (snd (fst AXF_mix.RES_pmix)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53af4) m rom) (mkst R (wa 0x53b4c) (mix_mem_pmix m regs sp1 sec) rom) /\
    getr R 2 = wa sp1 /\ getr R 8 = wa 4096 /\ getr R 10 = wa 0 /\ getr R 11 = wa 1 /\ getr R 19 = wa 621712 /\ (forall k, In k [1; 3; 4; 5; 6; 7; 9; 12; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sp1 sec P Hsc. destruct (mix_setup regs m sp1 sec P) as [HR HK].
  set (E := Ez regs (VALS_mix sp1 sec)) in *. destruct P as [mix_R2 mix_R8 mix_R19 mix_rng_sp1 mix_rng_sec mix_ka1 mix_kw3 mix_kw4 mix_kw5 mix_kwr6 mix_kd7].
  assert (Z32 : bv_unsigned (ev E 32) = sp1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sec) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53b4c] AXF_mix.scr_pmix 0x53af4 AXF_mix.sr_mix AXF_mix.kn_mix 34 _ _ _ E m rom regs AXF_mix.RES_pmix_ok HR HK Hsc) as (R & HR' & _ & Hms).
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
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

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
    KWord (SA e_sp0 (-8)) 8 (ELit 343020);
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
Definition ss_mmrg := SS 0x551a8 sr_mmrg [] kn_mmrg 41.
Definition RUN_mmrg := sym_exec SEGS 100 true [0x53bec] scr_mmrg ss_mmrg [].

Definition scr_pmmrg : scripts := SCR [] [] [].
Definition RES_pmmrg := Eval vm_compute in sym_exec SEGS 100 true [0x53bec] scr_pmmrg ss_mmrg [].
Lemma RES_pmmrg_ok : sym_exec SEGS 100 true [0x53bec] scr_pmmrg (SS 0x551a8 sr_mmrg [] kn_mmrg 41) [] = RES_pmmrg.
Proof. vm_compute. reflexivity. Qed.
End AXF_mmrg.

Module AXF_mmrgz.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

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
  mmrg_kw4 : rdn SEGS m (wa (sp0 + -8)) 8 = Some (word_to_le_bytes 8 (wa 343020)) ;
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
  exists R, msteps SEGS (mkst regs (wa 0x551a8) m rom) (mkst R (wa 0x53bec) (mmrg_mem_pmmrg m regs sp0 res ad s00 s10 s20 s30 s40 s50) rom) /\
    getr R 1 = wa 343020 /\ getr R 2 = wa sp0 /\ getr R 8 = wa s00 /\ getr R 9 = wa s10 /\ getr R 10 = wa res /\ getr R 11 = wa 18446744073709547521 /\ getr R 16 = wa ad /\ getr R 18 = wa s20 /\ getr R 19 = wa s30 /\ getr R 20 = wa s40 /\ getr R 21 = wa s50 /\ (forall k, In k [3; 4; 5; 6; 7; 12; 13; 14; 15; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
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
  destruct (run_sound SEGS 100 [0x53bec] AXF_mmrg.scr_pmmrg 0x551a8 AXF_mmrg.sr_mmrg AXF_mmrg.kn_mmrg 41 _ _ _ E m rom regs AXF_mmrg.RES_pmmrg_ok HR HK Hsc) as (R & HR' & _ & Hms).
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
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

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
    KWord (SA e_sp0 (-8)) 8 (ELit 343108);
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
Definition ss_mmrr := SS 0x551a8 sr_mmrr [] kn_mmrr 41.
Definition RUN_mmrr := sym_exec SEGS 100 true [0x53c44] scr_mmrr ss_mmrr [].

Definition scr_pmmrr : scripts := SCR [] [] [].
Definition RES_pmmrr := Eval vm_compute in sym_exec SEGS 100 true [0x53c44] scr_pmmrr ss_mmrr [].
Lemma RES_pmmrr_ok : sym_exec SEGS 100 true [0x53c44] scr_pmmrr (SS 0x551a8 sr_mmrr [] kn_mmrr 41) [] = RES_pmmrr.
Proof. vm_compute. reflexivity. Qed.
End AXF_mmrr.

Module AXF_mmrrz.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

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
  mmrr_kw4 : rdn SEGS m (wa (sp0 + -8)) 8 = Some (word_to_le_bytes 8 (wa 343108)) ;
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
  exists R, msteps SEGS (mkst regs (wa 0x551a8) m rom) (mkst R (wa 0x53c44) (mmrr_mem_pmmrr m regs sp0 res ad s00 s10 s20 s30 s40 s50) rom) /\
    getr R 1 = wa 343108 /\ getr R 2 = wa sp0 /\ getr R 8 = wa s00 /\ getr R 9 = wa s10 /\ getr R 10 = wa res /\ getr R 11 = wa 18446744073709547521 /\ getr R 16 = wa ad /\ getr R 18 = wa s20 /\ getr R 19 = wa s30 /\ getr R 20 = wa s40 /\ getr R 21 = wa s50 /\ (forall k, In k [3; 4; 5; 6; 7; 12; 13; 14; 15; 17; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
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
  destruct (run_sound SEGS 100 [0x53c44] AXF_mmrr.scr_pmmrr 0x551a8 AXF_mmrr.sr_mmrr AXF_mmrr.kn_mmrr 41 _ _ _ E m rom regs AXF_mmrr.RES_pmmrr_ok HR HK Hsc) as (R & HR' & _ & Hms).
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
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

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
Definition ss_mmwr := SS 0x550e0 sr_mmwr [] kn_mmwr 37.
Definition RUN_mmwr := sym_exec SEGS 100 true [0x551a4] scr_mmwr ss_mmwr [].

Definition scr_pnfr : scripts := SCR [false] [] [].
Definition RES_pnfr := Eval vm_compute in sym_exec SEGS 100 true [0x551a4] scr_pnfr ss_mmwr [].
Lemma RES_pnfr_ok : sym_exec SEGS 100 true [0x551a4] scr_pnfr (SS 0x550e0 sr_mmwr [] kn_mmwr 37) [] = RES_pnfr.
Proof. vm_compute. reflexivity. Qed.
End AXF_mmwr.

Module AXF_mmwrz.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

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
  exists R, msteps SEGS (mkst regs (wa 0x550e0) m rom) (mkst R (wa 0x551a4) (mmwr_mem_pnfr m regs sp0 ad len prot flags) rom) /\
    getr R 2 = wa (sp0 + -64) /\ getr R 5 = wa 18446744073709551604 /\ getr R 10 = wa ad /\ getr R 11 = wa len /\ getr R 12 = wa prot /\ getr R 13 = wa flags /\ getr R 14 = wa 18446744073709551615 /\ getr R 15 = wa 0 /\ getr R 16 = wa ad /\ getr R 17 = wa 222 /\ (forall k, In k [1; 3; 4; 6; 7; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sp0 ad len prot flags P Hsc. destruct (mmwr_setup regs m sp0 ad len prot flags P) as [HR HK].
  set (E := Ez regs (VALS_mmwr sp0 ad len prot flags)) in *. destruct P as [mmwr_R2 mmwr_R10 mmwr_R11 mmwr_R12 mmwr_R13 mmwr_R14 mmwr_R15 mmwr_HSTK mmwr_rng_sp0 mmwr_rng_ad mmwr_rng_len mmwr_rng_prot mmwr_rng_flags mmwr_ka1].
  assert (Z32 : bv_unsigned (ev E 32) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ad) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = len) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = prot) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = flags) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x551a4] AXF_mmwr.scr_pnfr 0x550e0 AXF_mmwr.sr_mmwr AXF_mmwr.kn_mmwr 37 _ _ _ E m rom regs AXF_mmwr.RES_pnfr_ok HR HK Hsc) as (R & HR' & _ & Hms).
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
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_sp0 := EVar 32.
Definition sr_mpr := (sr_upd (sr_upd sr_id 2 (EAlu ALU_ADD e_sp0 (ELit (-16)))) 10 (ELit 0)).
Definition kn_mpr : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KWord (SA e_sp0 (-8)) 8 (ELit 343320) ].
Definition scr_mpr : scripts := SCR [] [] [].
Definition ss_mpr := SS 0x55200 sr_mpr [] kn_mpr 33.
Definition RUN_mpr := sym_exec SEGS 100 true [0x53d18] scr_mpr ss_mpr [].

Definition scr_pmpr : scripts := SCR [] [] [].
Definition RES_pmpr := Eval vm_compute in sym_exec SEGS 100 true [0x53d18] scr_pmpr ss_mpr [].
Lemma RES_pmpr_ok : sym_exec SEGS 100 true [0x53d18] scr_pmpr (SS 0x55200 sr_mpr [] kn_mpr 33) [] = RES_pmpr.
Proof. vm_compute. reflexivity. Qed.
End AXF_mpr.

Module AXF_mprz.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section MPR.
Context {fx : FPState}.

Definition VALS_mpr (sp0 : Z) : list Z := [sp0].

Record mpr_pre (regs : bvmap 5 word) (m : word -> option byte) (sp0 : Z) : Prop := {
  mpr_R2 : getr regs 2 = wa (sp0 + -16) ;
  mpr_R10 : getr regs 10 = wa 0 ;
  mpr_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  mpr_ka1 : sp0 mod 16 = 0 ;
  mpr_kw2 : rdn SEGS m (wa (sp0 + -8)) 8 = Some (word_to_le_bytes 8 (wa 343320))
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
  exists R, msteps SEGS (mkst regs (wa 0x55200) m rom) (mkst R (wa 0x53d18) (mpr_mem_pmpr m regs sp0) rom) /\
    getr R 1 = wa 343320 /\ getr R 2 = wa sp0 /\ getr R 10 = wa 0 /\ getr R 11 = wa 18446744073709547521 /\ (forall k, In k [3; 4; 5; 6; 7; 8; 9; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sp0 P Hsc. destruct (mpr_setup regs m sp0 P) as [HR HK].
  set (E := Ez regs (VALS_mpr sp0)) in *. destruct P as [mpr_R2 mpr_R10 mpr_rng_sp0 mpr_ka1 mpr_kw2].
  assert (Z32 : bv_unsigned (ev E 32) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53d18] AXF_mpr.scr_pmpr 0x55200 AXF_mpr.sr_mpr AXF_mpr.kn_mpr 33 _ _ _ E m rom regs AXF_mpr.RES_pmpr_ok HR HK Hsc) as (R & HR' & _ & Hms).
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
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

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
    KWord (SA (ELit 0) 621648) 8 (ELit 4096);
    KDisj STK (ELit 1024) (SA (ELit 0) 621648) (ELit 8) ].
Definition scr_mpw : scripts := SCR [] [] [].
Definition ss_mpw := SS 0x551cc sr_mpw [] kn_mpw 34.
Definition RUN_mpw := sym_exec SEGS 100 true [0x551fc] scr_mpw ss_mpw [].

Definition scr_pmpw : scripts := SCR [] [] [].
Definition RES_pmpw := Eval vm_compute in sym_exec SEGS 100 true [0x551fc] scr_pmpw ss_mpw [].
Lemma RES_pmpw_ok : sym_exec SEGS 100 true [0x551fc] scr_pmpw (SS 0x551cc sr_mpw [] kn_mpw 34) [] = RES_pmpw.
Proof. vm_compute. reflexivity. Qed.
End AXF_mpw.

Module AXF_mpwz.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

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
  mpw_kw5 : rdn SEGS m (wa (0 + 621648)) 8 = Some (word_to_le_bytes 8 (wa 4096)) ;
  mpw_kd6 : sp0 + -1024 + 1024 <= 0 + 621648 \/ 0 + 621648 + 8 <= sp0 + -1024
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
  exists R, msteps SEGS (mkst regs (wa 0x551cc) m rom) (mkst R (wa 0x551fc) (mpw_mem_pmpw m regs sp0 p) rom) /\
    getr R 2 = wa (sp0 + -16) /\ getr R 10 = wa p /\ getr R 11 = wa 4096 /\ getr R 12 = wa 3 /\ getr R 13 = wa 4096 /\ getr R 14 = wa 18446744073709547520 /\ getr R 17 = wa 226 /\ (forall k, In k [1; 3; 4; 5; 6; 7; 8; 9; 15; 16; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sp0 p P Hsc. destruct (mpw_setup regs m sp0 p P) as [HR HK].
  set (E := Ez regs (VALS_mpw sp0 p)) in *. destruct P as [mpw_R2 mpw_R10 mpw_R11 mpw_R12 mpw_HSTK mpw_rng_sp0 mpw_rng_p mpw_ka1 mpw_ka4 mpw_kw5 mpw_kd6].
  assert (Z32 : bv_unsigned (ev E 32) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = p) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x551fc] AXF_mpw.scr_pmpw 0x551cc AXF_mpw.sr_mpw AXF_mpw.kn_mpw 34 _ _ _ E m rom regs AXF_mpw.RES_pmpw_ok HR HK Hsc) as (R & HR' & _ & Hms).
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
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_can := EVar 32.
Definition e_sp0 := EVar 33.
Definition STK := SA e_sp0 (-1024).
Definition sr_mt0 := (sr_upd sr_id 2 (e_sp0)).
Definition kn_mt0 : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KWr STK (ELit 1024);
    KWord (SA (ELit 0) 416600) 8 (ELit 621568);
    KWord (SA (ELit 0) 621568) 8 e_can;
    KDisj STK (ELit 1024) (SA (ELit 0) 416600) (ELit 8);
    KDisj STK (ELit 1024) (SA (ELit 0) 621568) (ELit 8) ].
Definition scr_mt0 : scripts := SCR [] [] [].
Definition ss_mt0 := SS 0x53a60 sr_mt0 [] kn_mt0 34.
Definition RUN_mt0 := sym_exec SEGS 100 true [0x53a94] scr_mt0 ss_mt0 [].

Definition scr_pmt0 : scripts := SCR [] [] [].
Definition RES_pmt0 := Eval vm_compute in sym_exec SEGS 100 true [0x53a94] scr_pmt0 ss_mt0 [].
Lemma RES_pmt0_ok : sym_exec SEGS 100 true [0x53a94] scr_pmt0 (SS 0x53a60 sr_mt0 [] kn_mt0 34) [] = RES_pmt0.
Proof. vm_compute. reflexivity. Qed.
End AXF_mt0.

Module AXF_mt0z.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section MT0.
Context {fx : FPState}.

Definition VALS_mt0 (can sp0 : Z) : list Z := [can; sp0].

Record mt0_pre (regs : bvmap 5 word) (m : word -> option byte) (can sp0 : Z) : Prop := {
  mt0_R2 : getr regs 2 = wa sp0 ;
  mt0_HSTK : stk_ok SEGS m (wa sp0) 1024 ;
  mt0_rng_can : 0 <= can <= 2^64-1 ;
  mt0_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  mt0_ka1 : sp0 mod 16 = 0 ;
  mt0_kw3 : rdn SEGS m (wa (0 + 416600)) 8 = Some (word_to_le_bytes 8 (wa 621568)) ;
  mt0_kw4 : rdn SEGS m (wa (0 + 621568)) 8 = Some (word_to_le_bytes 8 (wa can)) ;
  mt0_kd5 : sp0 + -1024 + 1024 <= 0 + 416600 \/ 0 + 416600 + 8 <= sp0 + -1024 ;
  mt0_kd6 : sp0 + -1024 + 1024 <= 0 + 621568 \/ 0 + 621568 + 8 <= sp0 + -1024
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
  exists R, msteps SEGS (mkst regs (wa 0x53a60) m rom) (mkst R (wa 0x53a94) (mt0_mem_pmt0 m regs can sp0) rom) /\
    getr R 2 = wa (sp0 + -64) /\ getr R 10 = wa can /\ getr R 11 = wa 621192 /\ getr R 18 = wa 621568 /\ getr R 19 = wa 621712 /\ (forall k, In k [1; 3; 4; 5; 6; 7; 8; 9; 12; 13; 14; 15; 16; 17; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom can sp0 P Hsc. destruct (mt0_setup regs m can sp0 P) as [HR HK].
  set (E := Ez regs (VALS_mt0 can sp0)) in *. destruct P as [mt0_R2 mt0_HSTK mt0_rng_can mt0_rng_sp0 mt0_ka1 mt0_kw3 mt0_kw4 mt0_kd5 mt0_kd6].
  assert (Z32 : bv_unsigned (ev E 32) = can) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53a94] AXF_mt0.scr_pmt0 0x53a60 AXF_mt0.sr_mt0 AXF_mt0.kn_mt0 34 _ _ _ E m rom regs AXF_mt0.RES_pmt0_ok HR HK Hsc) as (R & HR' & _ & Hms).
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

Module AXF_mt10.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_p := EVar 32.
Definition e_ac := EVar 33.
Definition e_tl := EVar 34.
Definition e_sec := EVar 35.
Definition sr_mt10 := (sr_upd (sr_upd sr_id 9 (e_p)) 19 (ELit 621712)).
Definition kn_mt10 : list kentry :=
  [ KRange e_p 4096 (2^47);
    KAlign e_p 4096;
    KRange e_ac 1 (2^60);
    KRange e_tl 0 (2^63-1);
    KRange e_sec 0 (2^64-1);
    KWord (SA (ELit 0) 621760) 8 e_ac;
    KWord (SA (ELit 0) 621784) 8 e_tl;
    KWord (SA (ELit 0) 621720) 8 e_sec;
    KWr (SA (ELit 0) 621736) (ELit 64);
    KWr (SA e_p 0) (ELit 24);
    KWr (SA e_tl 8) (ELit 8);
    KDisj (SA (ELit 0) 621736) (ELit 64) (SA e_p 0) (ELit 24);
    KDisj (SA (ELit 0) 621736) (ELit 64) (SA e_tl 8) (ELit 8);
    KDisj (SA e_p 0) (ELit 24) (SA e_tl 8) (ELit 8);
    KDisj (SA (ELit 0) 621720) (ELit 8) (SA e_tl 8) (ELit 8) ].
Definition scr_mt10 : scripts := SCR [false] [] [].
Definition ss_mt10 := SS 0x53c78 sr_mt10 [] kn_mt10 36.
Definition RUN_mt10 := sym_exec SEGS 100 true [0x53cd4] scr_mt10 ss_mt10 [].

Definition scr_ptl : scripts := SCR [false] [] [].
Definition RES_ptl := Eval vm_compute in sym_exec SEGS 100 true [0x53cd4] scr_ptl ss_mt10 [].
Lemma RES_ptl_ok : sym_exec SEGS 100 true [0x53cd4] scr_ptl (SS 0x53c78 sr_mt10 [] kn_mt10 36) [] = RES_ptl.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pt0 : scripts := SCR [true] [] [].
Definition RES_pt0 := Eval vm_compute in sym_exec SEGS 100 true [0x53cd4] scr_pt0 ss_mt10 [].
Lemma RES_pt0_ok : sym_exec SEGS 100 true [0x53cd4] scr_pt0 (SS 0x53c78 sr_mt10 [] kn_mt10 36) [] = RES_pt0.
Proof. vm_compute. reflexivity. Qed.
End AXF_mt10.

Module AXF_mt100.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_p := EVar 32.
Definition e_ac := EVar 33.
Definition e_sec := EVar 34.
Definition sr_mt100 := (sr_upd (sr_upd sr_id 9 (e_p)) 19 (ELit 621712)).
Definition kn_mt100 : list kentry :=
  [ KRange e_p 4096 (2^47);
    KAlign e_p 4096;
    KRange e_ac 1 (2^60);
    KRange e_sec 0 (2^64-1);
    KWord (SA (ELit 0) 621760) 8 e_ac;
    KWord (SA (ELit 0) 621784) 8 (ELit 0);
    KWord (SA (ELit 0) 621720) 8 e_sec;
    KWr (SA (ELit 0) 621736) (ELit 64);
    KWr (SA e_p 0) (ELit 24);
    KDisj (SA (ELit 0) 621736) (ELit 64) (SA e_p 0) (ELit 24) ].
Definition scr_mt100 : scripts := SCR [] [] [].
Definition ss_mt100 := SS 0x53c78 sr_mt100 [] kn_mt100 35.
Definition RUN_mt100 := sym_exec SEGS 100 true [0x53cd4] scr_mt100 ss_mt100 [].

Definition scr_pt00 : scripts := SCR [true] [] [].
Definition RES_pt00 := Eval vm_compute in sym_exec SEGS 100 true [0x53cd4] scr_pt00 ss_mt100 [].
Lemma RES_pt00_ok : sym_exec SEGS 100 true [0x53cd4] scr_pt00 (SS 0x53c78 sr_mt100 [] kn_mt100 35) [] = RES_pt00.
Proof. vm_compute. reflexivity. Qed.
End AXF_mt100.

Module AXF_mt100z.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section MT100.
Context {fx : FPState}.

Definition VALS_mt100 (p ac sec : Z) : list Z := [p; ac; sec].

Record mt100_pre (regs : bvmap 5 word) (m : word -> option byte) (p ac sec : Z) : Prop := {
  mt100_R9 : getr regs 9 = wa p ;
  mt100_R19 : getr regs 19 = wa 621712 ;
  mt100_rng_p : 4096 <= p <= 2^47 ;
  mt100_rng_ac : 1 <= ac <= 2^60 ;
  mt100_rng_sec : 0 <= sec <= 2^64-1 ;
  mt100_ka1 : p mod 4096 = 0 ;
  mt100_kw4 : rdn SEGS m (wa (0 + 621760)) 8 = Some (word_to_le_bytes 8 (wa ac)) ;
  mt100_kw5 : rdn SEGS m (wa (0 + 621784)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  mt100_kw6 : rdn SEGS m (wa (0 + 621720)) 8 = Some (word_to_le_bytes 8 (wa sec)) ;
  mt100_kwr7 : forall d k, 0 <= d -> d + Z.of_nat k <= 64 -> store_ok SEGS m (wa (0 + 621736 + d)) k = true ;
  mt100_kwr8 : forall d k, 0 <= d -> d + Z.of_nat k <= 24 -> store_ok SEGS m (wa (p + 0 + d)) k = true ;
  mt100_kd9 : 0 + 621736 + 64 <= p + 0 \/ p + 0 + 24 <= 0 + 621736
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
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (0 + 621760)) (word_to_le_bytes 8 (wa (ac + -1)))) (wa (0 + 621792)) (word_to_le_bytes 8 (wa (p + 4096)))) (wa (0 + 621776)) (word_to_le_bytes 8 (wa p))) (wa (0 + 621784)) (word_to_le_bytes 8 (wa p))) (wa (p + 0)) (word_to_le_bytes 8 (wa sec))) (wa (p + 16)) (word_to_le_bytes 4 (wa 101))) (wa (0 + 621744)) (word_to_le_bytes 8 (wa (p + 64)))) (wa (0 + 621752)) (word_to_le_bytes 8 (wa 100)).

#[using="Type"] Theorem mt100_pt00 : forall regs m rom p ac sec, mt100_pre regs m p ac sec ->
  scs_denot SEGS m (Ez regs (VALS_mt100 p ac sec)) (snd (fst AXF_mt100.RES_pt00)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53c78) m rom) (mkst R (wa 0x53cd4) (mt100_mem_pt00 m regs p ac sec) rom) /\
    getr R 9 = wa p /\ getr R 10 = wa (p + 24) /\ getr R 11 = wa 100 /\ getr R 12 = wa (p + 64) /\ getr R 19 = wa 621712 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom p ac sec P Hsc. destruct (mt100_setup regs m p ac sec P) as [HR HK].
  set (E := Ez regs (VALS_mt100 p ac sec)) in *. destruct P as [mt100_R9 mt100_R19 mt100_rng_p mt100_rng_ac mt100_rng_sec mt100_ka1 mt100_kw4 mt100_kw5 mt100_kw6 mt100_kwr7 mt100_kwr8 mt100_kd9].
  assert (Z32 : bv_unsigned (ev E 32) = p) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ac) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sec) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53cd4] AXF_mt100.scr_pt00 0x53c78 AXF_mt100.sr_mt100 AXF_mt100.kn_mt100 35 _ _ _ E m rom regs AXF_mt100.RES_pt00_ok HR HK Hsc) as (R & HR' & _ & Hms).
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
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section MT10.
Context {fx : FPState}.

Definition VALS_mt10 (p ac tl sec : Z) : list Z := [p; ac; tl; sec].

Record mt10_pre (regs : bvmap 5 word) (m : word -> option byte) (p ac tl sec : Z) : Prop := {
  mt10_R9 : getr regs 9 = wa p ;
  mt10_R19 : getr regs 19 = wa 621712 ;
  mt10_rng_p : 4096 <= p <= 2^47 ;
  mt10_rng_ac : 1 <= ac <= 2^60 ;
  mt10_rng_tl : 0 <= tl <= 2^63-1 ;
  mt10_rng_sec : 0 <= sec <= 2^64-1 ;
  mt10_ka1 : p mod 4096 = 0 ;
  mt10_kw5 : rdn SEGS m (wa (0 + 621760)) 8 = Some (word_to_le_bytes 8 (wa ac)) ;
  mt10_kw6 : rdn SEGS m (wa (0 + 621784)) 8 = Some (word_to_le_bytes 8 (wa tl)) ;
  mt10_kw7 : rdn SEGS m (wa (0 + 621720)) 8 = Some (word_to_le_bytes 8 (wa sec)) ;
  mt10_kwr8 : forall d k, 0 <= d -> d + Z.of_nat k <= 64 -> store_ok SEGS m (wa (0 + 621736 + d)) k = true ;
  mt10_kwr9 : forall d k, 0 <= d -> d + Z.of_nat k <= 24 -> store_ok SEGS m (wa (p + 0 + d)) k = true ;
  mt10_kwr10 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (tl + 8 + d)) k = true ;
  mt10_kd11 : 0 + 621736 + 64 <= p + 0 \/ p + 0 + 24 <= 0 + 621736 ;
  mt10_kd12 : 0 + 621736 + 64 <= tl + 8 \/ tl + 8 + 8 <= 0 + 621736 ;
  mt10_kd13 : p + 0 + 24 <= tl + 8 \/ tl + 8 + 8 <= p + 0 ;
  mt10_kd14 : 0 + 621720 + 8 <= tl + 8 \/ tl + 8 + 8 <= 0 + 621720
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
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (0 + 621760)) (word_to_le_bytes 8 (wa (ac + -1)))) (wa (0 + 621792)) (word_to_le_bytes 8 (wa (p + 4096)))) (wa (tl + 8)) (word_to_le_bytes 8 (wa p))) (wa (0 + 621784)) (word_to_le_bytes 8 (wa p))) (wa (p + 0)) (word_to_le_bytes 8 (wa sec))) (wa (p + 16)) (word_to_le_bytes 4 (wa 101))) (wa (0 + 621744)) (word_to_le_bytes 8 (wa (p + 64)))) (wa (0 + 621752)) (word_to_le_bytes 8 (wa 100)).

#[using="Type"] Theorem mt10_ptl : forall regs m rom p ac tl sec, mt10_pre regs m p ac tl sec ->
  scs_denot SEGS m (Ez regs (VALS_mt10 p ac tl sec)) (snd (fst AXF_mt10.RES_ptl)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53c78) m rom) (mkst R (wa 0x53cd4) (mt10_mem_ptl m regs p ac tl sec) rom) /\
    getr R 9 = wa p /\ getr R 10 = wa (p + 24) /\ getr R 11 = wa 100 /\ getr R 12 = wa (p + 64) /\ getr R 19 = wa 621712 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom p ac tl sec P Hsc. destruct (mt10_setup regs m p ac tl sec P) as [HR HK].
  set (E := Ez regs (VALS_mt10 p ac tl sec)) in *. destruct P as [mt10_R9 mt10_R19 mt10_rng_p mt10_rng_ac mt10_rng_tl mt10_rng_sec mt10_ka1 mt10_kw5 mt10_kw6 mt10_kw7 mt10_kwr8 mt10_kwr9 mt10_kwr10 mt10_kd11 mt10_kd12 mt10_kd13 mt10_kd14].
  assert (Z32 : bv_unsigned (ev E 32) = p) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ac) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = tl) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = sec) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53cd4] AXF_mt10.scr_ptl 0x53c78 AXF_mt10.sr_mt10 AXF_mt10.kn_mt10 36 _ _ _ E m rom regs AXF_mt10.RES_ptl_ok HR HK Hsc) as (R & HR' & _ & Hms).
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
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (m) (wa (0 + 621760)) (word_to_le_bytes 8 (wa (ac + -1)))) (wa (0 + 621792)) (word_to_le_bytes 8 (wa (p + 4096)))) (wa (0 + 621776)) (word_to_le_bytes 8 (wa p))) (wa (0 + 621784)) (word_to_le_bytes 8 (wa p))) (wa (p + 0)) (word_to_le_bytes 8 (wa sec))) (wa (p + 16)) (word_to_le_bytes 4 (wa 101))) (wa (0 + 621744)) (word_to_le_bytes 8 (wa (p + 64)))) (wa (0 + 621752)) (word_to_le_bytes 8 (wa 100)).

#[using="Type"] Theorem mt10_pt0 : forall regs m rom p ac tl sec, mt10_pre regs m p ac tl sec ->
  scs_denot SEGS m (Ez regs (VALS_mt10 p ac tl sec)) (snd (fst AXF_mt10.RES_pt0)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53c78) m rom) (mkst R (wa 0x53cd4) (mt10_mem_pt0 m regs p ac tl sec) rom) /\
    getr R 9 = wa p /\ getr R 10 = wa (p + 24) /\ getr R 11 = wa 100 /\ getr R 12 = wa (p + 64) /\ getr R 19 = wa 621712 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom p ac tl sec P Hsc. destruct (mt10_setup regs m p ac tl sec P) as [HR HK].
  set (E := Ez regs (VALS_mt10 p ac tl sec)) in *. destruct P as [mt10_R9 mt10_R19 mt10_rng_p mt10_rng_ac mt10_rng_tl mt10_rng_sec mt10_ka1 mt10_kw5 mt10_kw6 mt10_kw7 mt10_kwr8 mt10_kwr9 mt10_kwr10 mt10_kd11 mt10_kd12 mt10_kd13 mt10_kd14].
  assert (Z32 : bv_unsigned (ev E 32) = p) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ac) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = tl) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = sec) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53cd4] AXF_mt10.scr_pt0 0x53c78 AXF_mt10.sr_mt10 AXF_mt10.kn_mt10 36 _ _ _ E m rom regs AXF_mt10.RES_pt0_ok HR HK Hsc) as (R & HR' & _ & Hms).
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

Module AXF_mt1f1.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_fm := EVar 32.
Definition sr_mt1f1 := (sr_upd sr_id 19 (ELit 621712)).
Definition kn_mt1f1 : list kentry :=
  [ KRange e_fm 1 (2^63-1);
    KAlign e_fm 8;
    KWord (SA (ELit 0) 621728) 4 (ELit 1);
    KWord (SA (ELit 0) 621648) 8 (ELit 4096);
    KWord (SA (ELit 0) 621736) 8 e_fm;
    KWord (SA e_fm 8) 8 e_fm;
    KWr (SA (ELit 0) 621736) (ELit 8) ].
Definition scr_mt1f1 : scripts := SCR [true] [] [].
Definition ss_mt1f1 := SS 0x53a94 sr_mt1f1 [] kn_mt1f1 33.
Definition RUN_mt1f1 := sym_exec SEGS 100 true [0x53b4c; 0x53cd4] scr_mt1f1 ss_mt1f1 [].

Definition scr_pmf1a : scripts := SCR [true] [] [].
Definition RES_pmf1a := Eval vm_compute in sym_exec SEGS 100 true [0x53b4c; 0x53cd4] scr_pmf1a ss_mt1f1 [].
Lemma RES_pmf1a_ok : sym_exec SEGS 100 true [0x53b4c; 0x53cd4] scr_pmf1a (SS 0x53a94 sr_mt1f1 [] kn_mt1f1 33) [] = RES_pmf1a.
Proof. vm_compute. reflexivity. Qed.
End AXF_mt1f1.

Module AXF_mt1f1z.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section MT1F1.
Context {fx : FPState}.

Definition VALS_mt1f1 (fm : Z) : list Z := [fm].

Record mt1f1_pre (regs : bvmap 5 word) (m : word -> option byte) (fm : Z) : Prop := {
  mt1f1_R19 : getr regs 19 = wa 621712 ;
  mt1f1_rng_fm : 1 <= fm <= 2^63-1 ;
  mt1f1_ka1 : fm mod 8 = 0 ;
  mt1f1_kw2 : rdn SEGS m (wa (0 + 621728)) 4 = Some (word_to_le_bytes 4 (wa 1)) ;
  mt1f1_kw3 : rdn SEGS m (wa (0 + 621648)) 8 = Some (word_to_le_bytes 8 (wa 4096)) ;
  mt1f1_kw4 : rdn SEGS m (wa (0 + 621736)) 8 = Some (word_to_le_bytes 8 (wa fm)) ;
  mt1f1_kw5 : rdn SEGS m (wa (fm + 8)) 8 = Some (word_to_le_bytes 8 (wa fm)) ;
  mt1f1_kwr6 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (0 + 621736 + d)) k = true
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
  wbytes (m) (wa (0 + 621736)) (word_to_le_bytes 8 (wa 0)).

#[using="Type"] Theorem mt1f1_pmf1a : forall regs m rom fm, mt1f1_pre regs m fm ->
  scs_denot SEGS m (Ez regs (VALS_mt1f1 fm)) (snd (fst AXF_mt1f1.RES_pmf1a)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53a94) m rom) (mkst R (wa 0x53cd4) (mt1f1_mem_pmf1a m regs fm) rom) /\
    getr R 8 = wa 4096 /\ getr R 10 = wa fm /\ getr R 11 = wa fm /\ getr R 19 = wa 621712 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 9; 12; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom fm P Hsc. destruct (mt1f1_setup regs m fm P) as [HR HK].
  set (E := Ez regs (VALS_mt1f1 fm)) in *. destruct P as [mt1f1_R19 mt1f1_rng_fm mt1f1_ka1 mt1f1_kw2 mt1f1_kw3 mt1f1_kw4 mt1f1_kw5 mt1f1_kwr6].
  assert (Z32 : bv_unsigned (ev E 32) = fm) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53b4c; 0x53cd4] AXF_mt1f1.scr_pmf1a 0x53a94 AXF_mt1f1.sr_mt1f1 AXF_mt1f1.kn_mt1f1 33 _ _ _ E m rom regs AXF_mt1f1.RES_pmf1a_ok HR HK Hsc) as (R & HR' & _ & Hms).
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

Module AXF_mt2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_cnt := EVar 32.
Definition e_am := EVar 33.
Definition sr_mt2 := (sr_upd sr_id 19 (ELit 621712)).
Definition kn_mt2 : list kentry :=
  [ KRange e_cnt 0 101;
    KRange e_am 0 (2^63-1);
    KWord (SA (ELit 0) 621752) 8 e_cnt;
    KWord (SA (ELit 0) 621744) 8 e_am;
    KWr (SA (ELit 0) 621744) (ELit 16) ].
Definition scr_mt2 : scripts := SCR [false] [] [].
Definition ss_mt2 := SS 0x53b4c sr_mt2 [] kn_mt2 34.
Definition RUN_mt2 := sym_exec SEGS 100 true [0x53cd4; 0x53b68] scr_mt2 ss_mt2 [].

Definition scr_pmt2t : scripts := SCR [false] [] [].
Definition RES_pmt2t := Eval vm_compute in sym_exec SEGS 100 true [0x53cd4; 0x53b68] scr_pmt2t ss_mt2 [].
Lemma RES_pmt2t_ok : sym_exec SEGS 100 true [0x53cd4; 0x53b68] scr_pmt2t (SS 0x53b4c sr_mt2 [] kn_mt2 34) [] = RES_pmt2t.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pmt2z : scripts := SCR [true] [] [].
Definition RES_pmt2z := Eval vm_compute in sym_exec SEGS 100 true [0x53cd4; 0x53b68] scr_pmt2z ss_mt2 [].
Lemma RES_pmt2z_ok : sym_exec SEGS 100 true [0x53cd4; 0x53b68] scr_pmt2z (SS 0x53b4c sr_mt2 [] kn_mt2 34) [] = RES_pmt2z.
Proof. vm_compute. reflexivity. Qed.
End AXF_mt2.

Module AXF_mt2z.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section MT2.
Context {fx : FPState}.

Definition VALS_mt2 (cnt am : Z) : list Z := [cnt; am].

Record mt2_pre (regs : bvmap 5 word) (m : word -> option byte) (cnt am : Z) : Prop := {
  mt2_R19 : getr regs 19 = wa 621712 ;
  mt2_rng_cnt : 0 <= cnt <= 101 ;
  mt2_rng_am : 0 <= am <= 2^63-1 ;
  mt2_kw2 : rdn SEGS m (wa (0 + 621752)) 8 = Some (word_to_le_bytes 8 (wa cnt)) ;
  mt2_kw3 : rdn SEGS m (wa (0 + 621744)) 8 = Some (word_to_le_bytes 8 (wa am)) ;
  mt2_kwr4 : forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS m (wa (0 + 621744 + d)) k = true
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
  wbytes (wbytes (m) (wa (0 + 621744)) (word_to_le_bytes 8 (wa (am + 40)))) (wa (0 + 621752)) (word_to_le_bytes 8 (wa (cnt + -1))).

#[using="Type"] Theorem mt2_pmt2t : forall regs m rom cnt am, mt2_pre regs m cnt am ->
  scs_denot SEGS m (Ez regs (VALS_mt2 cnt am)) (snd (fst AXF_mt2.RES_pmt2t)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53b4c) m rom) (mkst R (wa 0x53cd4) (mt2_mem_pmt2t m regs cnt am) rom) /\
    getr R 10 = wa am /\ getr R 11 = wa (cnt + -1) /\ getr R 12 = wa (am + 40) /\ getr R 19 = wa 621712 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom cnt am P Hsc. destruct (mt2_setup regs m cnt am P) as [HR HK].
  set (E := Ez regs (VALS_mt2 cnt am)) in *. destruct P as [mt2_R19 mt2_rng_cnt mt2_rng_am mt2_kw2 mt2_kw3 mt2_kwr4].
  assert (Z32 : bv_unsigned (ev E 32) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = am) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53cd4; 0x53b68] AXF_mt2.scr_pmt2t 0x53b4c AXF_mt2.sr_mt2 AXF_mt2.kn_mt2 34 _ _ _ E m rom regs AXF_mt2.RES_pmt2t_ok HR HK Hsc) as (R & HR' & _ & Hms).
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
  exists R, msteps SEGS (mkst regs (wa 0x53b4c) m rom) (mkst R (wa 0x53b68) (mt2_mem_pmt2z m regs cnt am) rom) /\
    getr R 11 = wa cnt /\ getr R 19 = wa 621712 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 12; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom cnt am P Hsc. destruct (mt2_setup regs m cnt am P) as [HR HK].
  set (E := Ez regs (VALS_mt2 cnt am)) in *. destruct P as [mt2_R19 mt2_rng_cnt mt2_rng_am mt2_kw2 mt2_kw3 mt2_kwr4].
  assert (Z32 : bv_unsigned (ev E 32) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = am) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53cd4; 0x53b68] AXF_mt2.scr_pmt2z 0x53b4c AXF_mt2.sr_mt2 AXF_mt2.kn_mt2 34 _ _ _ E m rom regs AXF_mt2.RES_pmt2z_ok HR HK Hsc) as (R & HR' & _ & Hms).
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
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_ac := EVar 32.
Definition e_ar := EVar 33.
Definition sr_mt3o := (sr_upd (sr_upd sr_id 8 (ELit 4096)) 19 (ELit 621712)).
Definition kn_mt3o : list kentry :=
  [ KRange e_ac 1 (2^60);
    KRange e_ar 0 (2^63-1);
    KWord (SA (ELit 0) 621760) 8 e_ac;
    KWord (SA (ELit 0) 621792) 8 e_ar ].
Definition scr_mt3o : scripts := SCR [] [] [].
Definition ss_mt3o := SS 0x53b68 sr_mt3o [] kn_mt3o 34.
Definition RUN_mt3o := sym_exec SEGS 100 true [0x53c6c; 0x53b8c; 0x53ba4; 0x550e0] scr_mt3o ss_mt3o [].

Definition scr_pmt3oo : scripts := SCR [] [] [].
Definition RES_pmt3oo := Eval vm_compute in sym_exec SEGS 100 true [0x53c6c; 0x53b8c; 0x53ba4; 0x550e0] scr_pmt3oo ss_mt3o [].
Lemma RES_pmt3oo_ok : sym_exec SEGS 100 true [0x53c6c; 0x53b8c; 0x53ba4; 0x550e0] scr_pmt3oo (SS 0x53b68 sr_mt3o [] kn_mt3o 34) [] = RES_pmt3oo.
Proof. vm_compute. reflexivity. Qed.
End AXF_mt3o.

Module AXF_mt3oz.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section MT3O.
Context {fx : FPState}.

Definition VALS_mt3o (ac ar : Z) : list Z := [ac; ar].

Record mt3o_pre (regs : bvmap 5 word) (m : word -> option byte) (ac ar : Z) : Prop := {
  mt3o_R8 : getr regs 8 = wa 4096 ;
  mt3o_R19 : getr regs 19 = wa 621712 ;
  mt3o_rng_ac : 1 <= ac <= 2^60 ;
  mt3o_rng_ar : 0 <= ar <= 2^63-1 ;
  mt3o_kw2 : rdn SEGS m (wa (0 + 621760)) 8 = Some (word_to_le_bytes 8 (wa ac)) ;
  mt3o_kw3 : rdn SEGS m (wa (0 + 621792)) 8 = Some (word_to_le_bytes 8 (wa ar))
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
  exists R, msteps SEGS (mkst regs (wa 0x53b68) m rom) (mkst R (wa 0x53c6c) (mt3o_mem_pmt3oo m regs ac ar) rom) /\
    getr R 8 = wa 4096 /\ getr R 9 = wa ar /\ getr R 10 = wa ac /\ getr R 19 = wa 621712 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom ac ar P Hsc. destruct (mt3o_setup regs m ac ar P) as [HR HK].
  set (E := Ez regs (VALS_mt3o ac ar)) in *. destruct P as [mt3o_R8 mt3o_R19 mt3o_rng_ac mt3o_rng_ar mt3o_kw2 mt3o_kw3].
  assert (Z32 : bv_unsigned (ev E 32) = ac) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = ar) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53c6c; 0x53b8c; 0x53ba4; 0x550e0] AXF_mt3o.scr_pmt3oo 0x53b68 AXF_mt3o.sr_mt3o AXF_mt3o.kn_mt3o 34 _ _ _ E m rom regs AXF_mt3o.RES_pmt3oo_ok HR HK Hsc) as (R & HR' & _ & Hms).
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
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_ac := EVar 32.
Definition e_bk := EVar 33.
Definition e_ar := EVar 34.
Definition e_sh := EVar 35.
Definition sr_mt3w := (sr_upd (sr_upd sr_id 8 (ELit 4096)) 19 (ELit 621712)).
Definition kn_mt3w : list kentry :=
  [ KRange e_ac 0 (2^60);
    KRange e_bk 0 (2^64-1);
    KRange e_ar 0 (2^64-1);
    KRange e_sh 0 40;
    KWord (SA (ELit 0) 621760) 8 e_ac;
    KWord (SA (ELit 0) 622640) 8 e_bk;
    KWord (SA (ELit 0) 621792) 8 e_ar;
    KWord (SA (ELit 0) 621768) 8 e_sh ].
Definition scr_mt3w : scripts := SCR [true; false] [] [].
Definition ss_mt3w := SS 0x53b68 sr_mt3w [] kn_mt3w 36.
Definition RUN_mt3w := sym_exec SEGS 100 true [0x53c6c; 0x53b8c; 0x53ba4; 0x550e0] scr_mt3w ss_mt3w [].

Definition scr_pmt3dw : scripts := SCR [false; true; true] [] [].
Definition RES_pmt3dw := Eval vm_compute in sym_exec SEGS 100 true [0x53c6c; 0x53b8c; 0x53ba4; 0x550e0] scr_pmt3dw ss_mt3w [].
Lemma RES_pmt3dw_ok : sym_exec SEGS 100 true [0x53c6c; 0x53b8c; 0x53ba4; 0x550e0] scr_pmt3dw (SS 0x53b68 sr_mt3w [] kn_mt3w 36) [] = RES_pmt3dw.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pmt3nw : scripts := SCR [false; false; true] [] [].
Definition RES_pmt3nw := Eval vm_compute in sym_exec SEGS 100 true [0x53c6c; 0x53b8c; 0x53ba4; 0x550e0] scr_pmt3nw ss_mt3w [].
Lemma RES_pmt3nw_ok : sym_exec SEGS 100 true [0x53c6c; 0x53b8c; 0x53ba4; 0x550e0] scr_pmt3nw (SS 0x53b68 sr_mt3w [] kn_mt3w 36) [] = RES_pmt3nw.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pmt3cw : scripts := SCR [false; false; false] [] [].
Definition RES_pmt3cw := Eval vm_compute in sym_exec SEGS 100 true [0x53c6c; 0x53b8c; 0x53ba4; 0x550e0] scr_pmt3cw ss_mt3w [].
Lemma RES_pmt3cw_ok : sym_exec SEGS 100 true [0x53c6c; 0x53b8c; 0x53ba4; 0x550e0] scr_pmt3cw (SS 0x53b68 sr_mt3w [] kn_mt3w 36) [] = RES_pmt3cw.
Proof. vm_compute. reflexivity. Qed.
End AXF_mt3w.

Module AXF_mt3wz.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section MT3W.
Context {fx : FPState}.

Definition VALS_mt3w (ac bk ar sh : Z) : list Z := [ac; bk; ar; sh].

Record mt3w_pre (regs : bvmap 5 word) (m : word -> option byte) (ac bk ar sh : Z) : Prop := {
  mt3w_R8 : getr regs 8 = wa 4096 ;
  mt3w_R19 : getr regs 19 = wa 621712 ;
  mt3w_rng_ac : 0 <= ac <= 2^60 ;
  mt3w_rng_bk : 0 <= bk <= 2^64-1 ;
  mt3w_rng_ar : 0 <= ar <= 2^64-1 ;
  mt3w_rng_sh : 0 <= sh <= 40 ;
  mt3w_kw4 : rdn SEGS m (wa (0 + 621760)) 8 = Some (word_to_le_bytes 8 (wa ac)) ;
  mt3w_kw5 : rdn SEGS m (wa (0 + 622640)) 8 = Some (word_to_le_bytes 8 (wa bk)) ;
  mt3w_kw6 : rdn SEGS m (wa (0 + 621792)) 8 = Some (word_to_le_bytes 8 (wa ar)) ;
  mt3w_kw7 : rdn SEGS m (wa (0 + 621768)) 8 = Some (word_to_le_bytes 8 (wa sh))
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
  exists R, msteps SEGS (mkst regs (wa 0x53b68) m rom) (mkst R (wa 0x550e0) (mt3w_mem_pmt3dw m regs ac bk ar sh) rom) /\
    getr R 1 = wa 343108 /\ getr R 8 = wa 4096 /\ getr R 9 = wa (Z.shiftl 2 sh) /\ getr R 10 = wa 0 /\ getr R 11 = wa (4096 * Z.shiftl 2 sh) /\ getr R 12 = wa 0 /\ getr R 13 = wa 34 /\ getr R 14 = wa 18446744073709551615 /\ getr R 15 = wa 0 /\ getr R 19 = wa 621712 /\ getr R 20 = wa 18446744073709551615 /\ (forall k, In k [2; 3; 4; 5; 6; 7; 16; 17; 18; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom ac bk ar sh P Hsc. destruct (mt3w_setup regs m ac bk ar sh P) as [HR HK].
  set (E := Ez regs (VALS_mt3w ac bk ar sh)) in *. destruct P as [mt3w_R8 mt3w_R19 mt3w_rng_ac mt3w_rng_bk mt3w_rng_ar mt3w_rng_sh mt3w_kw4 mt3w_kw5 mt3w_kw6 mt3w_kw7].
  assert (Z32 : bv_unsigned (ev E 32) = ac) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = bk) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = ar) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = sh) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53c6c; 0x53b8c; 0x53ba4; 0x550e0] AXF_mt3w.scr_pmt3dw 0x53b68 AXF_mt3w.sr_mt3w AXF_mt3w.kn_mt3w 36 _ _ _ E m rom regs AXF_mt3w.RES_pmt3dw_ok HR HK Hsc) as (R & HR' & _ & Hms).
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
  exists R, msteps SEGS (mkst regs (wa 0x53b68) m rom) (mkst R (wa 0x53ba4) (mt3w_mem_pmt3nw m regs ac bk ar sh) rom) /\
    getr R 8 = wa 4096 /\ getr R 9 = wa bk /\ getr R 10 = wa 0 /\ getr R 11 = wa 4095 /\ getr R 17 = wa 214 /\ getr R 19 = wa 621712 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 12; 13; 14; 15; 16; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom ac bk ar sh P Hsc. destruct (mt3w_setup regs m ac bk ar sh P) as [HR HK].
  set (E := Ez regs (VALS_mt3w ac bk ar sh)) in *. destruct P as [mt3w_R8 mt3w_R19 mt3w_rng_ac mt3w_rng_bk mt3w_rng_ar mt3w_rng_sh mt3w_kw4 mt3w_kw5 mt3w_kw6 mt3w_kw7].
  assert (Z32 : bv_unsigned (ev E 32) = ac) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = bk) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = ar) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = sh) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53c6c; 0x53b8c; 0x53ba4; 0x550e0] AXF_mt3w.scr_pmt3nw 0x53b68 AXF_mt3w.sr_mt3w AXF_mt3w.kn_mt3w 36 _ _ _ E m rom regs AXF_mt3w.RES_pmt3nw_ok HR HK Hsc) as (R & HR' & _ & Hms).
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
  exists R, msteps SEGS (mkst regs (wa 0x53b68) m rom) (mkst R (wa 0x53b8c) (mt3w_mem_pmt3cw m regs ac bk ar sh) rom) /\
    getr R 8 = wa 4096 /\ getr R 9 = wa (bk + 4096) /\ getr R 10 = wa (bk + 4096) /\ getr R 11 = wa 18446744073709551615 /\ getr R 17 = wa 214 /\ getr R 19 = wa 621712 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 12; 13; 14; 15; 16; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom ac bk ar sh P Hsc. destruct (mt3w_setup regs m ac bk ar sh P) as [HR HK].
  set (E := Ez regs (VALS_mt3w ac bk ar sh)) in *. destruct P as [mt3w_R8 mt3w_R19 mt3w_rng_ac mt3w_rng_bk mt3w_rng_ar mt3w_rng_sh mt3w_kw4 mt3w_kw5 mt3w_kw6 mt3w_kw7].
  assert (Z32 : bv_unsigned (ev E 32) = ac) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = bk) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = ar) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = sh) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53c6c; 0x53b8c; 0x53ba4; 0x550e0] AXF_mt3w.scr_pmt3cw 0x53b68 AXF_mt3w.sr_mt3w AXF_mt3w.kn_mt3w 36 _ _ _ E m rom regs AXF_mt3w.RES_pmt3cw_ok HR HK Hsc) as (R & HR' & _ & Hms).
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
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_b0 := EVar 32.
Definition sr_mt4 := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 8 (ELit 4096)) 10 (e_b0)) 11 (ELit 4095)) 19 (ELit 621712)).
Definition kn_mt4 : list kentry :=
  [ KRange e_b0 0 (2^47);
    KWr (SA (ELit 0) 622640) (ELit 8) ].
Definition scr_mt4 : scripts := SCR [] [] [].
Definition ss_mt4 := SS 0x53ba8 sr_mt4 [] kn_mt4 33.
Definition RUN_mt4 := sym_exec SEGS 100 true [0x53bc8] scr_mt4 ss_mt4 [].

Definition scr_pmt4 : scripts := SCR [] [] [].
Definition RES_pmt4 := Eval vm_compute in sym_exec SEGS 100 true [0x53bc8] scr_pmt4 ss_mt4 [].
Lemma RES_pmt4_ok : sym_exec SEGS 100 true [0x53bc8] scr_pmt4 (SS 0x53ba8 sr_mt4 [] kn_mt4 33) [] = RES_pmt4.
Proof. vm_compute. reflexivity. Qed.
End AXF_mt4.

Module AXF_mt4z.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section MT4.
Context {fx : FPState}.

Definition VALS_mt4 (b0 : Z) : list Z := [b0].

Record mt4_pre (regs : bvmap 5 word) (m : word -> option byte) (b0 : Z) : Prop := {
  mt4_R8 : getr regs 8 = wa 4096 ;
  mt4_R10 : getr regs 10 = wa b0 ;
  mt4_R11 : getr regs 11 = wa 4095 ;
  mt4_R19 : getr regs 19 = wa 621712 ;
  mt4_rng_b0 : 0 <= b0 <= 2^47 ;
  mt4_kwr1 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (0 + 622640 + d)) k = true
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
  wbytes (m) (wa (0 + 622640)) (word_to_le_bytes 8 (wa (b0 + Z.land (((-1 * b0)) mod 2^64) 4095))).

#[using="Type"] Theorem mt4_pmt4 : forall regs m rom b0, mt4_pre regs m b0 ->
  scs_denot SEGS m (Ez regs (VALS_mt4 b0)) (snd (fst AXF_mt4.RES_pmt4)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53ba8) m rom) (mkst R (wa 0x53bc8) (mt4_mem_pmt4 m regs b0) rom) /\
    getr R 8 = wa 4096 /\ getr R 9 = wa ((b0 + Z.land (((-1 * b0)) mod 2^64) 4095) + 8192) /\ getr R 10 = wa ((b0 + Z.land (((-1 * b0)) mod 2^64) 4095) + 8192) /\ getr R 11 = wa (Z.land (((-1 * b0)) mod 2^64) 4095) /\ getr R 12 = wa (-1 * b0) /\ getr R 17 = wa 214 /\ getr R 19 = wa 621712 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 13; 14; 15; 16; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom b0 P Hsc. destruct (mt4_setup regs m b0 P) as [HR HK].
  set (E := Ez regs (VALS_mt4 b0)) in *. destruct P as [mt4_R8 mt4_R10 mt4_R11 mt4_R19 mt4_rng_b0 mt4_kwr1].
  assert (Z32 : bv_unsigned (ev E 32) = b0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53bc8] AXF_mt4.scr_pmt4 0x53ba8 AXF_mt4.sr_mt4 AXF_mt4.kn_mt4 33 _ _ _ E m rom regs AXF_mt4.RES_pmt4_ok HR HK Hsc) as (R & HR' & _ & Hms).
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
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_res := EVar 32.
Definition e_b := EVar 33.
Definition e_sh := EVar 34.
Definition sr_mt5 := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 8 (ELit 4096)) 9 (EAlu ALU_ADD e_b (ELit 8192))) 10 (e_res)) 19 (ELit 621712)).
Definition kn_mt5 : list kentry :=
  [ KRange e_res 0 (2^64-1);
    KRange e_b 4096 (2^47);
    KRange e_sh 0 40;
    KWord (SA (ELit 0) 622640) 8 e_b;
    KWord (SA (ELit 0) 621760) 8 (ELit 0);
    KWord (SA (ELit 0) 621768) 8 e_sh;
    KWr (SA (ELit 0) 622640) (ELit 8) ].
Definition scr_mt5 : scripts := SCR [false] [] [].
Definition ss_mt5 := SS 0x53bcc sr_mt5 [] kn_mt5 35.
Definition RUN_mt5 := sym_exec SEGS 100 true [0x550e0] scr_mt5 ss_mt5 [].

Definition scr_pmt5g : scripts := SCR [false] [] [].
Definition RES_pmt5g := Eval vm_compute in sym_exec SEGS 100 true [0x550e0] scr_pmt5g ss_mt5 [].
Lemma RES_pmt5g_ok : sym_exec SEGS 100 true [0x550e0] scr_pmt5g (SS 0x53bcc sr_mt5 [] kn_mt5 35) [] = RES_pmt5g.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pmt5r : scripts := SCR [true] [] [].
Definition RES_pmt5r := Eval vm_compute in sym_exec SEGS 100 true [0x550e0] scr_pmt5r ss_mt5 [].
Lemma RES_pmt5r_ok : sym_exec SEGS 100 true [0x550e0] scr_pmt5r (SS 0x53bcc sr_mt5 [] kn_mt5 35) [] = RES_pmt5r.
Proof. vm_compute. reflexivity. Qed.
End AXF_mt5.

Module AXF_mt5z.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section MT5.
Context {fx : FPState}.

Definition VALS_mt5 (res b sh : Z) : list Z := [res; b; sh].

Record mt5_pre (regs : bvmap 5 word) (m : word -> option byte) (res b sh : Z) : Prop := {
  mt5_R8 : getr regs 8 = wa 4096 ;
  mt5_R9 : getr regs 9 = wa (b + 8192) ;
  mt5_R10 : getr regs 10 = wa res ;
  mt5_R19 : getr regs 19 = wa 621712 ;
  mt5_rng_res : 0 <= res <= 2^64-1 ;
  mt5_rng_b : 4096 <= b <= 2^47 ;
  mt5_rng_sh : 0 <= sh <= 40 ;
  mt5_kw3 : rdn SEGS m (wa (0 + 622640)) 8 = Some (word_to_le_bytes 8 (wa b)) ;
  mt5_kw4 : rdn SEGS m (wa (0 + 621760)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  mt5_kw5 : rdn SEGS m (wa (0 + 621768)) 8 = Some (word_to_le_bytes 8 (wa sh)) ;
  mt5_kwr6 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (0 + 622640 + d)) k = true
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
  exists R, msteps SEGS (mkst regs (wa 0x53bcc) m rom) (mkst R (wa 0x550e0) (mt5_mem_pmt5g m regs res b sh) rom) /\
    getr R 1 = wa 343020 /\ getr R 8 = wa 4096 /\ getr R 9 = wa (b + 8192) /\ getr R 10 = wa b /\ getr R 11 = wa 4096 /\ getr R 12 = wa 0 /\ getr R 13 = wa 50 /\ getr R 14 = wa 18446744073709551615 /\ getr R 15 = wa 0 /\ getr R 19 = wa 621712 /\ (forall k, In k [2; 3; 4; 5; 6; 7; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom res b sh P Hsc. destruct (mt5_setup regs m res b sh P) as [HR HK].
  set (E := Ez regs (VALS_mt5 res b sh)) in *. destruct P as [mt5_R8 mt5_R9 mt5_R10 mt5_R19 mt5_rng_res mt5_rng_b mt5_rng_sh mt5_kw3 mt5_kw4 mt5_kw5 mt5_kwr6].
  assert (Z32 : bv_unsigned (ev E 32) = res) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = b) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sh) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x550e0] AXF_mt5.scr_pmt5g 0x53bcc AXF_mt5.sr_mt5 AXF_mt5.kn_mt5 35 _ _ _ E m rom regs AXF_mt5.RES_pmt5g_ok HR HK Hsc) as (R & HR' & _ & Hms).
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
  wbytes (m) (wa (0 + 622640)) (word_to_le_bytes 8 (wa 18446744073709551615)).

#[using="Type"] Theorem mt5_pmt5r : forall regs m rom res b sh, mt5_pre regs m res b sh ->
  scs_denot SEGS m (Ez regs (VALS_mt5 res b sh)) (snd (fst AXF_mt5.RES_pmt5r)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53bcc) m rom) (mkst R (wa 0x550e0) (mt5_mem_pmt5r m regs res b sh) rom) /\
    getr R 1 = wa 343108 /\ getr R 8 = wa 4096 /\ getr R 9 = wa (Z.shiftl 2 sh) /\ getr R 10 = wa 0 /\ getr R 11 = wa (4096 * Z.shiftl 2 sh) /\ getr R 12 = wa 0 /\ getr R 13 = wa 34 /\ getr R 14 = wa 18446744073709551615 /\ getr R 15 = wa 0 /\ getr R 19 = wa 621712 /\ getr R 20 = wa 18446744073709551615 /\ (forall k, In k [2; 3; 4; 5; 6; 7; 16; 17; 18; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom res b sh P Hsc. destruct (mt5_setup regs m res b sh P) as [HR HK].
  set (E := Ez regs (VALS_mt5 res b sh)) in *. destruct P as [mt5_R8 mt5_R9 mt5_R10 mt5_R19 mt5_rng_res mt5_rng_b mt5_rng_sh mt5_kw3 mt5_kw4 mt5_kw5 mt5_kwr6].
  assert (Z32 : bv_unsigned (ev E 32) = res) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = b) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sh) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x550e0] AXF_mt5.scr_pmt5r 0x53bcc AXF_mt5.sr_mt5 AXF_mt5.kn_mt5 35 _ _ _ E m rom regs AXF_mt5.RES_pmt5r_ok HR HK Hsc) as (R & HR' & _ & Hms).
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
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_res := EVar 32.
Definition e_nb := EVar 33.
Definition e_sh := EVar 34.
Definition sr_mt6 := (sr_upd (sr_upd (sr_upd (sr_upd sr_id 8 (ELit 4096)) 9 (e_nb)) 10 (e_res)) 19 (ELit 621712)).
Definition kn_mt6 : list kentry :=
  [ KRange e_res 0 (2^64-1);
    KRange e_nb 8192 (2^47);
    KRange e_sh 0 40;
    KWord (SA (ELit 0) 621760) 8 (ELit 0);
    KWord (SA (ELit 0) 621768) 8 e_sh;
    KWr (SA (ELit 0) 622640) (ELit 8);
    KWr (SA (ELit 0) 621760) (ELit 8) ].
Definition scr_mt6 : scripts := SCR [true] [] [].
Definition ss_mt6 := SS 0x53b90 sr_mt6 [] kn_mt6 35.
Definition RUN_mt6 := sym_exec SEGS 100 true [0x53c78; 0x550e0] scr_mt6 ss_mt6 [].

Definition scr_pmt6g : scripts := SCR [true] [] [].
Definition RES_pmt6g := Eval vm_compute in sym_exec SEGS 100 true [0x53c78; 0x550e0] scr_pmt6g ss_mt6 [].
Lemma RES_pmt6g_ok : sym_exec SEGS 100 true [0x53c78; 0x550e0] scr_pmt6g (SS 0x53b90 sr_mt6 [] kn_mt6 35) [] = RES_pmt6g.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pmt6r : scripts := SCR [false] [] [].
Definition RES_pmt6r := Eval vm_compute in sym_exec SEGS 100 true [0x53c78; 0x550e0] scr_pmt6r ss_mt6 [].
Lemma RES_pmt6r_ok : sym_exec SEGS 100 true [0x53c78; 0x550e0] scr_pmt6r (SS 0x53b90 sr_mt6 [] kn_mt6 35) [] = RES_pmt6r.
Proof. vm_compute. reflexivity. Qed.
End AXF_mt6.

Module AXF_mt6z.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section MT6.
Context {fx : FPState}.

Definition VALS_mt6 (res nb sh : Z) : list Z := [res; nb; sh].

Record mt6_pre (regs : bvmap 5 word) (m : word -> option byte) (res nb sh : Z) : Prop := {
  mt6_R8 : getr regs 8 = wa 4096 ;
  mt6_R9 : getr regs 9 = wa nb ;
  mt6_R10 : getr regs 10 = wa res ;
  mt6_R19 : getr regs 19 = wa 621712 ;
  mt6_rng_res : 0 <= res <= 2^64-1 ;
  mt6_rng_nb : 8192 <= nb <= 2^47 ;
  mt6_rng_sh : 0 <= sh <= 40 ;
  mt6_kw3 : rdn SEGS m (wa (0 + 621760)) 8 = Some (word_to_le_bytes 8 (wa 0)) ;
  mt6_kw4 : rdn SEGS m (wa (0 + 621768)) 8 = Some (word_to_le_bytes 8 (wa sh)) ;
  mt6_kwr5 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (0 + 622640 + d)) k = true ;
  mt6_kwr6 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (0 + 621760 + d)) k = true
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
  wbytes (wbytes (m) (wa (0 + 622640)) (word_to_le_bytes 8 (wa nb))) (wa (0 + 621760)) (word_to_le_bytes 8 (wa 1)).

#[using="Type"] Theorem mt6_pmt6g : forall regs m rom res nb sh, mt6_pre regs m res nb sh ->
  scs_denot SEGS m (Ez regs (VALS_mt6 res nb sh)) (snd (fst AXF_mt6.RES_pmt6g)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53b90) m rom) (mkst R (wa 0x53c78) (mt6_mem_pmt6g m regs res nb sh) rom) /\
    getr R 8 = wa 1 /\ getr R 9 = wa (nb + -4096) /\ getr R 10 = wa res /\ getr R 19 = wa 621712 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom res nb sh P Hsc. destruct (mt6_setup regs m res nb sh P) as [HR HK].
  set (E := Ez regs (VALS_mt6 res nb sh)) in *. destruct P as [mt6_R8 mt6_R9 mt6_R10 mt6_R19 mt6_rng_res mt6_rng_nb mt6_rng_sh mt6_kw3 mt6_kw4 mt6_kwr5 mt6_kwr6].
  assert (Z32 : bv_unsigned (ev E 32) = res) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = nb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sh) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53c78; 0x550e0] AXF_mt6.scr_pmt6g 0x53b90 AXF_mt6.sr_mt6 AXF_mt6.kn_mt6 35 _ _ _ E m rom regs AXF_mt6.RES_pmt6g_ok HR HK Hsc) as (R & HR' & _ & Hms).
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
  wbytes (m) (wa (0 + 622640)) (word_to_le_bytes 8 (wa 18446744073709551615)).

#[using="Type"] Theorem mt6_pmt6r : forall regs m rom res nb sh, mt6_pre regs m res nb sh ->
  scs_denot SEGS m (Ez regs (VALS_mt6 res nb sh)) (snd (fst AXF_mt6.RES_pmt6r)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53b90) m rom) (mkst R (wa 0x550e0) (mt6_mem_pmt6r m regs res nb sh) rom) /\
    getr R 1 = wa 343108 /\ getr R 8 = wa 4096 /\ getr R 9 = wa (Z.shiftl 2 sh) /\ getr R 10 = wa 0 /\ getr R 11 = wa (4096 * Z.shiftl 2 sh) /\ getr R 12 = wa 0 /\ getr R 13 = wa 34 /\ getr R 14 = wa 18446744073709551615 /\ getr R 15 = wa 0 /\ getr R 19 = wa 621712 /\ getr R 20 = wa 18446744073709551615 /\ (forall k, In k [2; 3; 4; 5; 6; 7; 16; 17; 18; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom res nb sh P Hsc. destruct (mt6_setup regs m res nb sh P) as [HR HK].
  set (E := Ez regs (VALS_mt6 res nb sh)) in *. destruct P as [mt6_R8 mt6_R9 mt6_R10 mt6_R19 mt6_rng_res mt6_rng_nb mt6_rng_sh mt6_kw3 mt6_kw4 mt6_kwr5 mt6_kwr6].
  assert (Z32 : bv_unsigned (ev E 32) = res) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = nb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = sh) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53c78; 0x550e0] AXF_mt6.scr_pmt6r 0x53b90 AXF_mt6.sr_mt6 AXF_mt6.kn_mt6 35 _ _ _ E m rom regs AXF_mt6.RES_pmt6r_ok HR HK Hsc) as (R & HR' & _ & Hms).
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
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_nb := EVar 32.
Definition sr_mt7 := (sr_upd (sr_upd (sr_upd sr_id 8 (ELit 4096)) 9 (e_nb)) 19 (ELit 621712)).
Definition kn_mt7 : list kentry :=
  [ KRange e_nb 8192 (2^47);
    KWr (SA (ELit 0) 622640) (ELit 8);
    KWr (SA (ELit 0) 621760) (ELit 8) ].
Definition scr_mt7 : scripts := SCR [] [] [].
Definition ss_mt7 := SS 0x53bec sr_mt7 [] kn_mt7 33.
Definition RUN_mt7 := sym_exec SEGS 100 true [0x53c78] scr_mt7 ss_mt7 [].

Definition scr_pmt7 : scripts := SCR [] [] [].
Definition RES_pmt7 := Eval vm_compute in sym_exec SEGS 100 true [0x53c78] scr_pmt7 ss_mt7 [].
Lemma RES_pmt7_ok : sym_exec SEGS 100 true [0x53c78] scr_pmt7 (SS 0x53bec sr_mt7 [] kn_mt7 33) [] = RES_pmt7.
Proof. vm_compute. reflexivity. Qed.
End AXF_mt7.

Module AXF_mt7z.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section MT7.
Context {fx : FPState}.

Definition VALS_mt7 (nb : Z) : list Z := [nb].

Record mt7_pre (regs : bvmap 5 word) (m : word -> option byte) (nb : Z) : Prop := {
  mt7_R8 : getr regs 8 = wa 4096 ;
  mt7_R9 : getr regs 9 = wa nb ;
  mt7_R19 : getr regs 19 = wa 621712 ;
  mt7_rng_nb : 8192 <= nb <= 2^47 ;
  mt7_kwr1 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (0 + 622640 + d)) k = true ;
  mt7_kwr2 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (0 + 621760 + d)) k = true
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
  wbytes (wbytes (m) (wa (0 + 622640)) (word_to_le_bytes 8 (wa nb))) (wa (0 + 621760)) (word_to_le_bytes 8 (wa 1)).

#[using="Type"] Theorem mt7_pmt7 : forall regs m rom nb, mt7_pre regs m nb ->
  scs_denot SEGS m (Ez regs (VALS_mt7 nb)) (snd (fst AXF_mt7.RES_pmt7)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53bec) m rom) (mkst R (wa 0x53c78) (mt7_mem_pmt7 m regs nb) rom) /\
    getr R 8 = wa 1 /\ getr R 9 = wa (nb + -4096) /\ getr R 19 = wa 621712 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom nb P Hsc. destruct (mt7_setup regs m nb P) as [HR HK].
  set (E := Ez regs (VALS_mt7 nb)) in *. destruct P as [mt7_R8 mt7_R9 mt7_R19 mt7_rng_nb mt7_kwr1 mt7_kwr2].
  assert (Z32 : bv_unsigned (ev E 32) = nb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53c78] AXF_mt7.scr_pmt7 0x53bec AXF_mt7.sr_mt7 AXF_mt7.kn_mt7 33 _ _ _ E m rom regs AXF_mt7.RES_pmt7_ok HR HK Hsc) as (R & HR' & _ & Hms).
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
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_p := EVar 32.
Definition sr_mt8b := (sr_upd (sr_upd sr_id 8 (ELit 4096)) 9 (e_p)).
Definition kn_mt8b : list kentry :=
  [ KRange e_p 4096 (2^47);
    KAlign e_p 4096 ].
Definition scr_mt8b : scripts := SCR [true] [] [].
Definition ss_mt8b := SS 0x53c6c sr_mt8b [] kn_mt8b 33.
Definition RUN_mt8b := sym_exec SEGS 100 true [0x551cc] scr_mt8b ss_mt8b [].

Definition scr_pmt8b : scripts := SCR [true] [] [].
Definition RES_pmt8b := Eval vm_compute in sym_exec SEGS 100 true [0x551cc] scr_pmt8b ss_mt8b [].
Lemma RES_pmt8b_ok : sym_exec SEGS 100 true [0x551cc] scr_pmt8b (SS 0x53c6c sr_mt8b [] kn_mt8b 33) [] = RES_pmt8b.
Proof. vm_compute. reflexivity. Qed.
End AXF_mt8b.

Module AXF_mt8bz.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

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
  exists R, msteps SEGS (mkst regs (wa 0x53c6c) m rom) (mkst R (wa 0x551cc) (mt8b_mem_pmt8b m regs p) rom) /\
    getr R 1 = wa 343320 /\ getr R 8 = wa 4096 /\ getr R 9 = wa p /\ getr R 10 = wa p /\ getr R 11 = wa 4096 /\ getr R 12 = wa 3 /\ (forall k, In k [2; 3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom p P Hsc. destruct (mt8b_setup regs m p P) as [HR HK].
  set (E := Ez regs (VALS_mt8b p)) in *. destruct P as [mt8b_R8 mt8b_R9 mt8b_rng_p mt8b_ka1].
  assert (Z32 : bv_unsigned (ev E 32) = p) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x551cc] AXF_mt8b.scr_pmt8b 0x53c6c AXF_mt8b.sr_mt8b AXF_mt8b.kn_mt8b 33 _ _ _ E m rom regs AXF_mt8b.RES_pmt8b_ok HR HK Hsc) as (R & HR' & _ & Hms).
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
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_p := EVar 32.
Definition e_sh := EVar 33.
Definition e_n := EVar 34.
Definition sr_mt8x := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 8 (ELit 4096)) 9 (e_n)) 10 (e_p)) 19 (ELit 621712)) 20 (ELit 18446744073709551615)).
Definition kn_mt8x : list kentry :=
  [ KRange e_p 4096 (2^47);
    KAlign e_p 4096;
    KRange e_sh 0 40;
    KRange e_n 2 (2^41);
    KWord (SA (ELit 0) 621768) 8 e_sh;
    KWr (SA (ELit 0) 621760) (ELit 16);
    KWr (SA (ELit 0) 621792) (ELit 8) ].
Definition scr_mt8x : scripts := SCR [false] [] [].
Definition ss_mt8x := SS 0x53c44 sr_mt8x [] kn_mt8x 35.
Definition RUN_mt8x := sym_exec SEGS 100 true [0x551cc] scr_mt8x ss_mt8x [].

Definition scr_pmt8x : scripts := SCR [false] [] [].
Definition RES_pmt8x := Eval vm_compute in sym_exec SEGS 100 true [0x551cc] scr_pmt8x ss_mt8x [].
Lemma RES_pmt8x_ok : sym_exec SEGS 100 true [0x551cc] scr_pmt8x (SS 0x53c44 sr_mt8x [] kn_mt8x 35) [] = RES_pmt8x.
Proof. vm_compute. reflexivity. Qed.
End AXF_mt8x.

Module AXF_mt8xz.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section MT8X.
Context {fx : FPState}.

Definition VALS_mt8x (p sh n : Z) : list Z := [p; sh; n].

Record mt8x_pre (regs : bvmap 5 word) (m : word -> option byte) (p sh n : Z) : Prop := {
  mt8x_R8 : getr regs 8 = wa 4096 ;
  mt8x_R9 : getr regs 9 = wa n ;
  mt8x_R10 : getr regs 10 = wa p ;
  mt8x_R19 : getr regs 19 = wa 621712 ;
  mt8x_R20 : getr regs 20 = wa 18446744073709551615 ;
  mt8x_rng_p : 4096 <= p <= 2^47 ;
  mt8x_rng_sh : 0 <= sh <= 40 ;
  mt8x_rng_n : 2 <= n <= 2^41 ;
  mt8x_ka1 : p mod 4096 = 0 ;
  mt8x_kw4 : rdn SEGS m (wa (0 + 621768)) 8 = Some (word_to_le_bytes 8 (wa sh)) ;
  mt8x_kwr5 : forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS m (wa (0 + 621760 + d)) k = true ;
  mt8x_kwr6 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (0 + 621792 + d)) k = true
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
  wbytes (wbytes (wbytes (m) (wa (0 + 621760)) (word_to_le_bytes 8 (wa (n + -1)))) (wa (0 + 621768)) (word_to_le_bytes 8 (wa (sh + 1)))) (wa (0 + 621792)) (word_to_le_bytes 8 (wa (p + 4096))).

#[using="Type"] Theorem mt8x_pmt8x : forall regs m rom p sh n, mt8x_pre regs m p sh n ->
  scs_denot SEGS m (Ez regs (VALS_mt8x p sh n)) (snd (fst AXF_mt8x.RES_pmt8x)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53c44) m rom) (mkst R (wa 0x551cc) (mt8x_mem_pmt8x m regs p sh n) rom) /\
    getr R 1 = wa 343320 /\ getr R 8 = wa 4096 /\ getr R 9 = wa (p + 4096) /\ getr R 10 = wa (p + 4096) /\ getr R 11 = wa 4096 /\ getr R 12 = wa 3 /\ getr R 19 = wa 621712 /\ getr R 20 = wa 18446744073709551615 /\ (forall k, In k [2; 3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 18; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom p sh n P Hsc. destruct (mt8x_setup regs m p sh n P) as [HR HK].
  set (E := Ez regs (VALS_mt8x p sh n)) in *. destruct P as [mt8x_R8 mt8x_R9 mt8x_R10 mt8x_R19 mt8x_R20 mt8x_rng_p mt8x_rng_sh mt8x_rng_n mt8x_ka1 mt8x_kw4 mt8x_kwr5 mt8x_kwr6].
  assert (Z32 : bv_unsigned (ev E 32) = p) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sh) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = n) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x551cc] AXF_mt8x.scr_pmt8x 0x53c44 AXF_mt8x.sr_mt8x AXF_mt8x.kn_mt8x 35 _ _ _ E m rom regs AXF_mt8x.RES_pmt8x_ok HR HK Hsc) as (R & HR' & _ & Hms).
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
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_d := EVar 32.
Definition sr_mt9 := (sr_upd sr_id 10 (ELit 0)).
Definition kn_mt9 : list kentry :=
  [  ].
Definition scr_mt9 : scripts := SCR [true] [] [].
Definition ss_mt9 := SS 0x53d18 sr_mt9 [] kn_mt9 33.
Definition RUN_mt9 := sym_exec SEGS 100 true [0x53c78] scr_mt9 ss_mt9 [].

Definition scr_pmt9 : scripts := SCR [true] [] [].
Definition RES_pmt9 := Eval vm_compute in sym_exec SEGS 100 true [0x53c78] scr_pmt9 ss_mt9 [].
Lemma RES_pmt9_ok : sym_exec SEGS 100 true [0x53c78] scr_pmt9 (SS 0x53d18 sr_mt9 [] kn_mt9 33) [] = RES_pmt9.
Proof. vm_compute. reflexivity. Qed.
End AXF_mt9.

Module AXF_mt9z.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

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
  exists R, msteps SEGS (mkst regs (wa 0x53d18) m rom) (mkst R (wa 0x53c78) (mt9_mem_pmt9 m regs d) rom) /\
    getr R 10 = wa 0 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom d P Hsc. destruct (mt9_setup regs m d P) as [HR HK].
  set (E := Ez regs (VALS_mt9 d)) in *. destruct P as [mt9_R10 mt9_rng_d].
  assert (Z32 : bv_unsigned (ev E 32) = d) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x53c78] AXF_mt9.scr_pmt9 0x53d18 AXF_mt9.sr_mt9 AXF_mt9.kn_mt9 33 _ _ _ E m rom regs AXF_mt9.RES_pmt9_ok HR HK Hsc) as (R & HR' & _ & Hms).
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
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_mt := EVar 32.
Definition e_can := EVar 33.
Definition e_sp0 := EVar 34.
Definition e_s00 := EVar 35.
Definition e_s10 := EVar 36.
Definition e_s20 := EVar 37.
Definition e_s30 := EVar 38.
Definition e_s40 := EVar 39.
Definition sr_mte := (sr_upd (sr_upd (sr_upd sr_id 2 (EAlu ALU_ADD e_sp0 (ELit (-64)))) 10 (e_mt)) 18 (ELit 621568)).
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
    KWord (SA (ELit 0) 621568) 8 e_can;
    KWord (SA e_sp0 (-56)) 8 e_can;
    KWord (SA e_sp0 (-8)) 8 (ELit 344736);
    KWord (SA e_sp0 (-16)) 8 e_s00;
    KWord (SA e_sp0 (-24)) 8 e_s10;
    KWord (SA e_sp0 (-32)) 8 e_s20;
    KWord (SA e_sp0 (-40)) 8 e_s30;
    KWord (SA e_sp0 (-48)) 8 e_s40;
    KWr (SA e_mt 0) (ELit 16);
    KDisj (SA e_mt 0) (ELit 16) (SA e_sp0 (-56)) (ELit 56);
    KDisj (SA e_mt 0) (ELit 16) (SA (ELit 0) 621568) (ELit 8) ].
Definition scr_mte : scripts := SCR [false] [] [].
Definition ss_mte := SS 0x53cd4 sr_mte [] kn_mte 40.
Definition RUN_mte := sym_exec SEGS 100 true [0x542a0] scr_mte ss_mte [].

Definition scr_pmte : scripts := SCR [false] [] [].
Definition RES_pmte := Eval vm_compute in sym_exec SEGS 100 true [0x542a0] scr_pmte ss_mte [].
Lemma RES_pmte_ok : sym_exec SEGS 100 true [0x542a0] scr_pmte (SS 0x53cd4 sr_mte [] kn_mte 40) [] = RES_pmte.
Proof. vm_compute. reflexivity. Qed.
End AXF_mte.

Module AXF_mted.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_mt := EVar 32.
Definition e_can := EVar 33.
Definition e_sp0 := EVar 34.
Definition e_s00 := EVar 35.
Definition e_s10 := EVar 36.
Definition e_s20 := EVar 37.
Definition e_s30 := EVar 38.
Definition e_s40 := EVar 39.
Definition sr_mted := (sr_upd (sr_upd (sr_upd sr_id 2 (EAlu ALU_ADD e_sp0 (ELit (-64)))) 10 (e_mt)) 18 (ELit 621568)).
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
    KWord (SA (ELit 0) 621568) 8 e_can;
    KWord (SA e_sp0 (-56)) 8 e_can;
    KWord (SA e_sp0 (-8)) 8 (ELit 343748);
    KWord (SA e_sp0 (-16)) 8 e_s00;
    KWord (SA e_sp0 (-24)) 8 e_s10;
    KWord (SA e_sp0 (-32)) 8 e_s20;
    KWord (SA e_sp0 (-40)) 8 e_s30;
    KWord (SA e_sp0 (-48)) 8 e_s40;
    KWr (SA e_mt 0) (ELit 16);
    KDisj (SA e_mt 0) (ELit 16) (SA e_sp0 (-56)) (ELit 56);
    KDisj (SA e_mt 0) (ELit 16) (SA (ELit 0) 621568) (ELit 8) ].
Definition scr_mted : scripts := SCR [false] [] [].
Definition ss_mted := SS 0x53cd4 sr_mted [] kn_mted 40.
Definition RUN_mted := sym_exec SEGS 100 true [0x53ec4] scr_mted ss_mted [].

Definition scr_pmted : scripts := SCR [false] [] [].
Definition RES_pmted := Eval vm_compute in sym_exec SEGS 100 true [0x53ec4] scr_pmted ss_mted [].
Lemma RES_pmted_ok : sym_exec SEGS 100 true [0x53ec4] scr_pmted (SS 0x53cd4 sr_mted [] kn_mted 40) [] = RES_pmted.
Proof. vm_compute. reflexivity. Qed.
End AXF_mted.

Module AXF_mtedz.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section MTED.
Context {fx : FPState}.

Definition VALS_mted (mt can sp0 s00 s10 s20 s30 s40 : Z) : list Z := [mt; can; sp0; s00; s10; s20; s30; s40].

Record mted_pre (regs : bvmap 5 word) (m : word -> option byte) (mt can sp0 s00 s10 s20 s30 s40 : Z) : Prop := {
  mted_R2 : getr regs 2 = wa (sp0 + -64) ;
  mted_R10 : getr regs 10 = wa mt ;
  mted_R18 : getr regs 18 = wa 621568 ;
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
  mted_kw10 : rdn SEGS m (wa (0 + 621568)) 8 = Some (word_to_le_bytes 8 (wa can)) ;
  mted_kw11 : rdn SEGS m (wa (sp0 + -56)) 8 = Some (word_to_le_bytes 8 (wa can)) ;
  mted_kw12 : rdn SEGS m (wa (sp0 + -8)) 8 = Some (word_to_le_bytes 8 (wa 343748)) ;
  mted_kw13 : rdn SEGS m (wa (sp0 + -16)) 8 = Some (word_to_le_bytes 8 (wa s00)) ;
  mted_kw14 : rdn SEGS m (wa (sp0 + -24)) 8 = Some (word_to_le_bytes 8 (wa s10)) ;
  mted_kw15 : rdn SEGS m (wa (sp0 + -32)) 8 = Some (word_to_le_bytes 8 (wa s20)) ;
  mted_kw16 : rdn SEGS m (wa (sp0 + -40)) 8 = Some (word_to_le_bytes 8 (wa s30)) ;
  mted_kw17 : rdn SEGS m (wa (sp0 + -48)) 8 = Some (word_to_le_bytes 8 (wa s40)) ;
  mted_kwr18 : forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS m (wa (mt + 0 + d)) k = true ;
  mted_kd19 : mt + 0 + 16 <= sp0 + -56 \/ sp0 + -56 + 56 <= mt + 0 ;
  mted_kd20 : mt + 0 + 16 <= 0 + 621568 \/ 0 + 621568 + 8 <= mt + 0
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
  exists R, msteps SEGS (mkst regs (wa 0x53cd4) m rom) (mkst R (wa 0x53ec4) (mted_mem_pmted m regs mt can sp0 s00 s10 s20 s30 s40) rom) /\
    getr R 1 = wa 343748 /\ getr R 2 = wa sp0 /\ getr R 8 = wa s00 /\ getr R 9 = wa s10 /\ getr R 10 = wa mt /\ getr R 11 = wa can /\ getr R 12 = wa can /\ getr R 18 = wa s20 /\ getr R 19 = wa s30 /\ getr R 20 = wa s40 /\ (forall k, In k [3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
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
  destruct (run_sound SEGS 100 [0x53ec4] AXF_mted.scr_pmted 0x53cd4 AXF_mted.sr_mted AXF_mted.kn_mted 40 _ _ _ E m rom regs AXF_mted.RES_pmted_ok HR HK Hsc) as (R & HR' & _ & Hms).
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
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section MTE.
Context {fx : FPState}.

Definition VALS_mte (mt can sp0 s00 s10 s20 s30 s40 : Z) : list Z := [mt; can; sp0; s00; s10; s20; s30; s40].

Record mte_pre (regs : bvmap 5 word) (m : word -> option byte) (mt can sp0 s00 s10 s20 s30 s40 : Z) : Prop := {
  mte_R2 : getr regs 2 = wa (sp0 + -64) ;
  mte_R10 : getr regs 10 = wa mt ;
  mte_R18 : getr regs 18 = wa 621568 ;
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
  mte_kw10 : rdn SEGS m (wa (0 + 621568)) 8 = Some (word_to_le_bytes 8 (wa can)) ;
  mte_kw11 : rdn SEGS m (wa (sp0 + -56)) 8 = Some (word_to_le_bytes 8 (wa can)) ;
  mte_kw12 : rdn SEGS m (wa (sp0 + -8)) 8 = Some (word_to_le_bytes 8 (wa 344736)) ;
  mte_kw13 : rdn SEGS m (wa (sp0 + -16)) 8 = Some (word_to_le_bytes 8 (wa s00)) ;
  mte_kw14 : rdn SEGS m (wa (sp0 + -24)) 8 = Some (word_to_le_bytes 8 (wa s10)) ;
  mte_kw15 : rdn SEGS m (wa (sp0 + -32)) 8 = Some (word_to_le_bytes 8 (wa s20)) ;
  mte_kw16 : rdn SEGS m (wa (sp0 + -40)) 8 = Some (word_to_le_bytes 8 (wa s30)) ;
  mte_kw17 : rdn SEGS m (wa (sp0 + -48)) 8 = Some (word_to_le_bytes 8 (wa s40)) ;
  mte_kwr18 : forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS m (wa (mt + 0 + d)) k = true ;
  mte_kd19 : mt + 0 + 16 <= sp0 + -56 \/ sp0 + -56 + 56 <= mt + 0 ;
  mte_kd20 : mt + 0 + 16 <= 0 + 621568 \/ 0 + 621568 + 8 <= mt + 0
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
  exists R, msteps SEGS (mkst regs (wa 0x53cd4) m rom) (mkst R (wa 0x542a0) (mte_mem_pmte m regs mt can sp0 s00 s10 s20 s30 s40) rom) /\
    getr R 1 = wa 344736 /\ getr R 2 = wa sp0 /\ getr R 8 = wa s00 /\ getr R 9 = wa s10 /\ getr R 10 = wa mt /\ getr R 11 = wa can /\ getr R 12 = wa can /\ getr R 18 = wa s20 /\ getr R 19 = wa s30 /\ getr R 20 = wa s40 /\ (forall k, In k [3; 4; 5; 6; 7; 13; 14; 15; 16; 17; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
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
  destruct (run_sound SEGS 100 [0x542a0] AXF_mte.scr_pmte 0x53cd4 AXF_mte.sr_mte AXF_mte.kn_mte 40 _ _ _ E m rom regs AXF_mte.RES_pmte_ok HR HK Hsc) as (R & HR' & _ & Hms).
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

Module AXF_mwj.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_d := EVar 32.
Definition sr_mwj := sr_id.
Definition kn_mwj : list kentry :=
  [  ].
Definition scr_mwj : scripts := SCR [] [] [].
Definition ss_mwj := SS 0x54044 sr_mwj [] kn_mwj 33.
Definition RUN_mwj := sym_exec SEGS 10 true [0x540a8] scr_mwj ss_mwj [].

Definition scr_pmwj : scripts := SCR [] [] [].
Definition RES_pmwj := Eval vm_compute in sym_exec SEGS 10 true [0x540a8] scr_pmwj ss_mwj [].
Lemma RES_pmwj_ok : sym_exec SEGS 10 true [0x540a8] scr_pmwj (SS 0x54044 sr_mwj [] kn_mwj 33) [] = RES_pmwj.
Proof. vm_compute. reflexivity. Qed.
End AXF_mwj.

Module AXF_mwjz.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section MWJ.
Context {fx : FPState}.

Definition VALS_mwj (d : Z) : list Z := [d].

Record mwj_pre (regs : bvmap 5 word) (m : word -> option byte) (d : Z) : Prop := {
  mwj_rng_d : 0 <= d <= 1
}.


#[using="Type"] Lemma mwj_setup : forall regs m d, mwj_pre regs m d ->
  regs_ok (Ez regs (VALS_mwj d)) AXF_mwj.sr_mwj regs /\ know_ok SEGS (Ez regs (VALS_mwj d)) m AXF_mwj.kn_mwj.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m d P. destruct P as [mwj_rng_d].
  set (E := Ez regs (VALS_mwj d)).
  assert (Z32 : bv_unsigned (ev E 32) = d) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mwj.sr_mwj.
    apply regs_ok_id. }
  unfold know_ok, AXF_mwj.kn_mwj.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mwj.e_d a_base a_off].
  all: rewrite ?Z32.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range d _ _ mwj_rng_d eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - mwj_rng_d; lia).
  all: first [lia].
Qed.


Definition mwj_mem_pmwj (m : word -> option byte) (regs : bvmap 5 word) (d : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mwj_pmwj : forall regs m rom d, mwj_pre regs m d ->
  scs_denot SEGS m (Ez regs (VALS_mwj d)) (snd (fst AXF_mwj.RES_pmwj)) ->
  exists R, msteps SEGS (mkst regs (wa 0x54044) m rom) (mkst R (wa 0x540a8) (mwj_mem_pmwj m regs d) rom) /\
    getr R 1 = wa 344136 /\ (forall k, In k [2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom d P Hsc. destruct (mwj_setup regs m d P) as [HR HK].
  set (E := Ez regs (VALS_mwj d)) in *. destruct P as [mwj_rng_d].
  assert (Z32 : bv_unsigned (ev E 32) = d) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 10 [0x540a8] AXF_mwj.scr_pmwj 0x54044 AXF_mwj.sr_mwj AXF_mwj.kn_mwj 33 _ _ _ E m rom regs AXF_mwj.RES_pmwj_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mwj.RES_pmwj fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mwj_mem_pmwj m regs d) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mwj_mem_pmwj. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MWJ.
End AXF_mwjz.

Module AXF_mwr.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_d := EVar 32.
Definition sr_mwr := (sr_upd sr_id 1 (ELit 344136)).
Definition kn_mwr : list kentry :=
  [  ].
Definition scr_mwr : scripts := SCR [] [] [].
Definition ss_mwr := SS 0x54944 sr_mwr [] kn_mwr 33.
Definition RUN_mwr := sym_exec SEGS 10 true [0x54048] scr_mwr ss_mwr [].

Definition scr_pmwr : scripts := SCR [] [] [].
Definition RES_pmwr := Eval vm_compute in sym_exec SEGS 10 true [0x54048] scr_pmwr ss_mwr [].
Lemma RES_pmwr_ok : sym_exec SEGS 10 true [0x54048] scr_pmwr (SS 0x54944 sr_mwr [] kn_mwr 33) [] = RES_pmwr.
Proof. vm_compute. reflexivity. Qed.
End AXF_mwr.

Module AXF_mwrz.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section MWR.
Context {fx : FPState}.

Definition VALS_mwr (d : Z) : list Z := [d].

Record mwr_pre (regs : bvmap 5 word) (m : word -> option byte) (d : Z) : Prop := {
  mwr_R1 : getr regs 1 = wa 344136 ;
  mwr_rng_d : 0 <= d <= 1
}.


#[using="Type"] Lemma mwr_setup : forall regs m d, mwr_pre regs m d ->
  regs_ok (Ez regs (VALS_mwr d)) AXF_mwr.sr_mwr regs /\ know_ok SEGS (Ez regs (VALS_mwr d)) m AXF_mwr.kn_mwr.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m d P. destruct P as [mwr_R1 mwr_rng_d].
  set (E := Ez regs (VALS_mwr d)).
  assert (Z32 : bv_unsigned (ev E 32) = d) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_mwr.sr_mwr.
    apply (regs_ok_pin E _ regs 1); [apply regs_ok_id|].
    - rewrite mwr_R1. reflexivity. }
  unfold know_ok, AXF_mwr.kn_mwr.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ fail
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end)
             | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_mwr.e_d a_base a_off].
  all: rewrite ?Z32.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range d _ _ mwr_rng_d eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - mwr_rng_d; lia).
  all: first [lia].
Qed.


Definition mwr_mem_pmwr (m : word -> option byte) (regs : bvmap 5 word) (d : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem mwr_pmwr : forall regs m rom d, mwr_pre regs m d ->
  scs_denot SEGS m (Ez regs (VALS_mwr d)) (snd (fst AXF_mwr.RES_pmwr)) ->
  exists R, msteps SEGS (mkst regs (wa 0x54944) m rom) (mkst R (wa 0x54048) (mwr_mem_pmwr m regs d) rom) /\
    getr R 1 = wa 344136 /\ (forall k, In k [2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom d P Hsc. destruct (mwr_setup regs m d P) as [HR HK].
  set (E := Ez regs (VALS_mwr d)) in *. destruct P as [mwr_R1 mwr_rng_d].
  assert (Z32 : bv_unsigned (ev E 32) = d) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 10 [0x54048] AXF_mwr.scr_pmwr 0x54944 AXF_mwr.sr_mwr AXF_mwr.kn_mwr 33 _ _ _ E m rom regs AXF_mwr.RES_pmwr_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_mwr.RES_pmwr fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (mwr_mem_pmwr m regs d) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold mwr_mem_pmwr. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End MWR.
End AXF_mwrz.

Module AXF_ncall.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_j := EVar 32.
Definition sr_ncall := (sr_upd sr_id 14 (e_j)).
Definition kn_ncall : list kentry :=
  [ KRange e_j 0 47 ].
Definition scr_ncall : scripts := SCR [] [] [].
Definition ss_ncall := SS 0x5447c sr_ncall [] kn_ncall 33.
Definition RUN_ncall := sym_exec SEGS 100 true [0x540a8] scr_ncall ss_ncall [].

Definition scr_pncall : scripts := SCR [] [] [].
Definition RES_pncall := Eval vm_compute in sym_exec SEGS 100 true [0x540a8] scr_pncall ss_ncall [].
Lemma RES_pncall_ok : sym_exec SEGS 100 true [0x540a8] scr_pncall (SS 0x5447c sr_ncall [] kn_ncall 33) [] = RES_pncall.
Proof. vm_compute. reflexivity. Qed.
End AXF_ncall.

Module AXF_ncallz.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section NCALL.
Context {fx : FPState}.

Definition VALS_ncall (j : Z) : list Z := [j].

Record ncall_pre (regs : bvmap 5 word) (m : word -> option byte) (j : Z) : Prop := {
  ncall_R14 : getr regs 14 = wa j ;
  ncall_rng_j : 0 <= j <= 47
}.


#[using="Type"] Lemma ncall_setup : forall regs m j, ncall_pre regs m j ->
  regs_ok (Ez regs (VALS_ncall j)) AXF_ncall.sr_ncall regs /\ know_ok SEGS (Ez regs (VALS_ncall j)) m AXF_ncall.kn_ncall.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m j P. destruct P as [ncall_R14 ncall_rng_j].
  set (E := Ez regs (VALS_ncall j)).
  assert (Z32 : bv_unsigned (ev E 32) = j) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_ncall.sr_ncall.
    apply (regs_ok_pin E _ regs 14); [apply regs_ok_id|].
    - rewrite ncall_R14. reflexivity. }
  unfold know_ok, AXF_ncall.kn_ncall.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_ncall.e_j a_base a_off].
  all: rewrite ?Z32.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range j _ _ ncall_rng_j eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - ncall_rng_j; lia).
  all: first [lia].
Qed.


Definition ncall_mem_pncall (m : word -> option byte) (regs : bvmap 5 word) (j : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem ncall_pncall : forall regs m rom j, ncall_pre regs m j ->
  scs_denot SEGS m (Ez regs (VALS_ncall j)) (snd (fst AXF_ncall.RES_pncall)) ->
  exists R, msteps SEGS (mkst regs (wa 0x5447c) m rom) (mkst R (wa 0x540a8) (ncall_mem_pncall m regs j) rom) /\
    getr R 1 = wa 345224 /\ getr R 10 = wa j /\ getr R 14 = wa j /\ getr R 18 = wa j /\ (forall k, In k [2; 3; 4; 5; 6; 7; 8; 9; 11; 12; 13; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom j P Hsc. destruct (ncall_setup regs m j P) as [HR HK].
  set (E := Ez regs (VALS_ncall j)) in *. destruct P as [ncall_R14 ncall_rng_j].
  assert (Z32 : bv_unsigned (ev E 32) = j) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x540a8] AXF_ncall.scr_pncall 0x5447c AXF_ncall.sr_ncall AXF_ncall.kn_ncall 33 _ _ _ E m rom regs AXF_ncall.RES_pncall_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_ncall.RES_pncall fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (ncall_mem_pncall m regs j) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold ncall_mem_pncall. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End NCALL.
End AXF_ncallz.

Module AXF_nfin.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_cnt := EVar 32.
Definition sr_nfin := (sr_upd sr_id 19 (e_cnt)).
Definition kn_nfin : list kentry :=
  [ KRange e_cnt 1 32 ].
Definition scr_nfin : scripts := SCR [] [] [].
Definition ss_nfin := SS 0x544f0 sr_nfin [] kn_nfin 33.
Definition RUN_nfin := sym_exec SEGS 100 true [0x547b0] scr_nfin ss_nfin [].

Definition scr_pnfin : scripts := SCR [] [] [].
Definition RES_pnfin := Eval vm_compute in sym_exec SEGS 100 true [0x547b0] scr_pnfin ss_nfin [].
Lemma RES_pnfin_ok : sym_exec SEGS 100 true [0x547b0] scr_pnfin (SS 0x544f0 sr_nfin [] kn_nfin 33) [] = RES_pnfin.
Proof. vm_compute. reflexivity. Qed.
End AXF_nfin.

Module AXF_nfinz.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section NFIN.
Context {fx : FPState}.

Definition VALS_nfin (cnt : Z) : list Z := [cnt].

Record nfin_pre (regs : bvmap 5 word) (m : word -> option byte) (cnt : Z) : Prop := {
  nfin_R19 : getr regs 19 = wa cnt ;
  nfin_rng_cnt : 1 <= cnt <= 32
}.


#[using="Type"] Lemma nfin_setup : forall regs m cnt, nfin_pre regs m cnt ->
  regs_ok (Ez regs (VALS_nfin cnt)) AXF_nfin.sr_nfin regs /\ know_ok SEGS (Ez regs (VALS_nfin cnt)) m AXF_nfin.kn_nfin.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m cnt P. destruct P as [nfin_R19 nfin_rng_cnt].
  set (E := Ez regs (VALS_nfin cnt)).
  assert (Z32 : bv_unsigned (ev E 32) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_nfin.sr_nfin.
    apply (regs_ok_pin E _ regs 19); [apply regs_ok_id|].
    - rewrite nfin_R19. reflexivity. }
  unfold know_ok, AXF_nfin.kn_nfin.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_nfin.e_cnt a_base a_off].
  all: rewrite ?Z32.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range cnt _ _ nfin_rng_cnt eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - nfin_rng_cnt; lia).
  all: first [lia].
Qed.


Definition nfin_mem_pnfin (m : word -> option byte) (regs : bvmap 5 word) (cnt : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem nfin_pnfin : forall regs m rom cnt, nfin_pre regs m cnt ->
  scs_denot SEGS m (Ez regs (VALS_nfin cnt)) (snd (fst AXF_nfin.RES_pnfin)) ->
  exists R, msteps SEGS (mkst regs (wa 0x544f0) m rom) (mkst R (wa 0x547b0) (nfin_mem_pnfin m regs cnt) rom) /\
    getr R 11 = wa (cnt + -1) /\ getr R 12 = wa (cnt + -1) /\ getr R 19 = wa cnt /\ getr R 25 = wa cnt /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom cnt P Hsc. destruct (nfin_setup regs m cnt P) as [HR HK].
  set (E := Ez regs (VALS_nfin cnt)) in *. destruct P as [nfin_R19 nfin_rng_cnt].
  assert (Z32 : bv_unsigned (ev E 32) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x547b0] AXF_nfin.scr_pnfin 0x544f0 AXF_nfin.sr_nfin AXF_nfin.kn_nfin 33 _ _ _ E m rom regs AXF_nfin.RES_pnfin_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_nfin.RES_pnfin fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (nfin_mem_pnfin m regs cnt) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold nfin_mem_pnfin. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End NFIN.
End AXF_nfinz.

Module AXF_nhdr.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_p := EVar 32.
Definition e_mt := EVar 33.
Definition e_W := EVar 34.
Definition e_b3 := EVar 35.
Definition e_cnt := EVar 36.
Definition sr_nhdr := (sr_upd (sr_upd (sr_upd sr_id 9 (e_mt)) 10 (e_p)) 19 (e_cnt)).
Definition kn_nhdr : list kentry :=
  [ KRange e_p 4096 (2^47);
    KRange e_mt 1 (2^63-1);
    KAlign e_mt 8;
    KRange e_W 0 (2^63-1);
    KRange e_b3 0 255;
    KRange e_cnt 1 32;
    KWord (SA e_mt 32) 8 e_W;
    KWord (SA e_p (-3)) 1 e_b3;
    KWr (SA e_mt 32) (ELit 8);
    KWr (SA e_p (-3)) (ELit 1);
    KDisj (SA e_mt 32) (ELit 8) (SA e_p (-3)) (ELit 1) ].
Definition scr_nhdr : scripts := SCR [] [] [].
Definition ss_nhdr := SS 0x544b8 sr_nhdr [] kn_nhdr 37.
Definition RUN_nhdr := sym_exec SEGS 100 true [0x544e0] scr_nhdr ss_nhdr [].

Definition scr_pnhdr : scripts := SCR [] [] [].
Definition RES_pnhdr := Eval vm_compute in sym_exec SEGS 100 true [0x544e0] scr_pnhdr ss_nhdr [].
Lemma RES_pnhdr_ok : sym_exec SEGS 100 true [0x544e0] scr_pnhdr (SS 0x544b8 sr_nhdr [] kn_nhdr 37) [] = RES_pnhdr.
Proof. vm_compute. reflexivity. Qed.
End AXF_nhdr.

Module AXF_nhdrz.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section NHDR.
Context {fx : FPState}.

Definition VALS_nhdr (p mt W b3 cnt : Z) : list Z := [p; mt; W; b3; cnt].

Record nhdr_pre (regs : bvmap 5 word) (m : word -> option byte) (p mt W b3 cnt : Z) : Prop := {
  nhdr_R9 : getr regs 9 = wa mt ;
  nhdr_R10 : getr regs 10 = wa p ;
  nhdr_R19 : getr regs 19 = wa cnt ;
  nhdr_rng_p : 4096 <= p <= 2^47 ;
  nhdr_rng_mt : 1 <= mt <= 2^63-1 ;
  nhdr_rng_W : 0 <= W <= 2^63-1 ;
  nhdr_rng_b3 : 0 <= b3 <= 255 ;
  nhdr_rng_cnt : 1 <= cnt <= 32 ;
  nhdr_ka2 : mt mod 8 = 0 ;
  nhdr_kw6 : rdn SEGS m (wa (mt + 32)) 8 = Some (word_to_le_bytes 8 (wa W)) ;
  nhdr_kw7 : rdn SEGS m (wa (p + -3)) 1 = Some (word_to_le_bytes 1 (wa b3)) ;
  nhdr_kwr8 : forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (mt + 32 + d)) k = true ;
  nhdr_kwr9 : forall d k, 0 <= d -> d + Z.of_nat k <= 1 -> store_ok SEGS m (wa (p + -3 + d)) k = true ;
  nhdr_kd10 : mt + 32 + 8 <= p + -3 \/ p + -3 + 1 <= mt + 32
}.


#[using="Type"] Lemma nhdr_setup : forall regs m p mt W b3 cnt, nhdr_pre regs m p mt W b3 cnt ->
  regs_ok (Ez regs (VALS_nhdr p mt W b3 cnt)) AXF_nhdr.sr_nhdr regs /\ know_ok SEGS (Ez regs (VALS_nhdr p mt W b3 cnt)) m AXF_nhdr.kn_nhdr.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m p mt W b3 cnt P. destruct P as [nhdr_R9 nhdr_R10 nhdr_R19 nhdr_rng_p nhdr_rng_mt nhdr_rng_W nhdr_rng_b3 nhdr_rng_cnt nhdr_ka2 nhdr_kw6 nhdr_kw7 nhdr_kwr8 nhdr_kwr9 nhdr_kd10].
  set (E := Ez regs (VALS_nhdr p mt W b3 cnt)).
  assert (Z32 : bv_unsigned (ev E 32) = p) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = mt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = W) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = b3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_nhdr.sr_nhdr.
    apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply regs_ok_id|]|]|].
    - rewrite nhdr_R9. reflexivity.
    - rewrite nhdr_R10. reflexivity.
    - rewrite nhdr_R19. reflexivity. }
  unfold know_ok, AXF_nhdr.kn_nhdr.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_nhdr.e_p AXF_nhdr.e_mt AXF_nhdr.e_W AXF_nhdr.e_b3 AXF_nhdr.e_cnt a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range p _ _ nhdr_rng_p eq_refl eq_refl), ?(mod64_of_range mt _ _ nhdr_rng_mt eq_refl eq_refl), ?(mod64_of_range W _ _ nhdr_rng_W eq_refl eq_refl), ?(mod64_of_range b3 _ _ nhdr_rng_b3 eq_refl eq_refl), ?(mod64_of_range cnt _ _ nhdr_rng_cnt eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply nhdr_kwr8 | apply nhdr_kwr9]; assumption).
  all: try (clear - nhdr_rng_p nhdr_rng_mt nhdr_rng_W nhdr_rng_b3 nhdr_rng_cnt nhdr_ka2; lia).
  all: first [(clear - nhdr_rng_p nhdr_rng_mt nhdr_rng_W nhdr_rng_b3 nhdr_rng_cnt nhdr_ka2 nhdr_kd10; lia) | lia].
Qed.


Definition nhdr_mem_pnhdr (m : word -> option byte) (regs : bvmap 5 word) (p mt W b3 cnt : Z) : word -> option byte :=
  wbytes (wbytes (m) (wa (mt + 32)) (word_to_le_bytes 8 (wa (Z.shiftr (((4503599627370496 * W)) mod 2^64) 52)))) (wa (p + -3)) (word_to_le_bytes 1 (wa (Z.land b3 31 + 192))).

#[using="Type"] Theorem nhdr_pnhdr : forall regs m rom p mt W b3 cnt, nhdr_pre regs m p mt W b3 cnt ->
  scs_denot SEGS m (Ez regs (VALS_nhdr p mt W b3 cnt)) (snd (fst AXF_nhdr.RES_pnhdr)) ->
  exists R, msteps SEGS (mkst regs (wa 0x544b8) m rom) (mkst R (wa 0x544e0) (nhdr_mem_pnhdr m regs p mt W b3 cnt) rom) /\
    getr R 9 = wa mt /\ getr R 10 = wa p /\ getr R 11 = wa (cnt + 1) /\ getr R 12 = wa (p + 12) /\ getr R 19 = wa cnt /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 13; 14; 15; 16; 17; 18; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom p mt W b3 cnt P Hsc. destruct (nhdr_setup regs m p mt W b3 cnt P) as [HR HK].
  set (E := Ez regs (VALS_nhdr p mt W b3 cnt)) in *. destruct P as [nhdr_R9 nhdr_R10 nhdr_R19 nhdr_rng_p nhdr_rng_mt nhdr_rng_W nhdr_rng_b3 nhdr_rng_cnt nhdr_ka2 nhdr_kw6 nhdr_kw7 nhdr_kwr8 nhdr_kwr9 nhdr_kd10].
  assert (Z32 : bv_unsigned (ev E 32) = p) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = mt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = W) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = b3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x544e0] AXF_nhdr.scr_pnhdr 0x544b8 AXF_nhdr.sr_nhdr AXF_nhdr.kn_nhdr 37 _ _ _ E m rom regs AXF_nhdr.RES_pnhdr_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_nhdr.RES_pnhdr fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (nhdr_mem_pnhdr m regs p mt W b3 cnt) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold nhdr_mem_pnhdr. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End NHDR.
End AXF_nhdrz.

Module AXF_nj0.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_sz := EVar 32.
Definition sr_nj0 := (sr_upd sr_id 14 (e_sz)).
Definition kn_nj0 : list kentry :=
  [ KRange e_sz 16 2032;
    KAlign e_sz 16 ].
Definition scr_nj0 : scripts := SCR [true] [] [].
Definition ss_nj0 := SS 0x543b8 sr_nj0 [] kn_nj0 33.
Definition RUN_nj0 := sym_exec SEGS 100 true [0x5447c; 0x543c8] scr_nj0 ss_nj0 [].

Definition scr_pnjs : scripts := SCR [true] [] [].
Definition RES_pnjs := Eval vm_compute in sym_exec SEGS 100 true [0x5447c; 0x543c8] scr_pnjs ss_nj0 [].
Lemma RES_pnjs_ok : sym_exec SEGS 100 true [0x5447c; 0x543c8] scr_pnjs (SS 0x543b8 sr_nj0 [] kn_nj0 33) [] = RES_pnjs.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pnjm : scripts := SCR [false] [] [].
Definition RES_pnjm := Eval vm_compute in sym_exec SEGS 100 true [0x5447c; 0x543c8] scr_pnjm ss_nj0 [].
Lemma RES_pnjm_ok : sym_exec SEGS 100 true [0x5447c; 0x543c8] scr_pnjm (SS 0x543b8 sr_nj0 [] kn_nj0 33) [] = RES_pnjm.
Proof. vm_compute. reflexivity. Qed.
End AXF_nj0.

Module AXF_nj0z.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section NJ0.
Context {fx : FPState}.

Definition VALS_nj0 (sz : Z) : list Z := [sz].

Record nj0_pre (regs : bvmap 5 word) (m : word -> option byte) (sz : Z) : Prop := {
  nj0_R14 : getr regs 14 = wa sz ;
  nj0_rng_sz : 16 <= sz <= 2032 ;
  nj0_ka1 : sz mod 16 = 0
}.


#[using="Type"] Lemma nj0_setup : forall regs m sz, nj0_pre regs m sz ->
  regs_ok (Ez regs (VALS_nj0 sz)) AXF_nj0.sr_nj0 regs /\ know_ok SEGS (Ez regs (VALS_nj0 sz)) m AXF_nj0.kn_nj0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sz P. destruct P as [nj0_R14 nj0_rng_sz nj0_ka1].
  set (E := Ez regs (VALS_nj0 sz)).
  assert (Z32 : bv_unsigned (ev E 32) = sz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_nj0.sr_nj0.
    apply (regs_ok_pin E _ regs 14); [apply regs_ok_id|].
    - rewrite nj0_R14. reflexivity. }
  unfold know_ok, AXF_nj0.kn_nj0.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_nj0.e_sz a_base a_off].
  all: rewrite ?Z32.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sz _ _ nj0_rng_sz eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - nj0_rng_sz nj0_ka1; lia).
  all: first [lia].
Qed.


Definition nj0_mem_pnjs (m : word -> option byte) (regs : bvmap 5 word) (sz : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem nj0_pnjs : forall regs m rom sz, nj0_pre regs m sz ->
  scs_denot SEGS m (Ez regs (VALS_nj0 sz)) (snd (fst AXF_nj0.RES_pnjs)) ->
  exists R, msteps SEGS (mkst regs (wa 0x543b8) m rom) (mkst R (wa 0x5447c) (nj0_mem_pnjs m regs sz) rom) /\
    getr R 10 = wa 157 /\ getr R 11 = wa (sz + 12) /\ getr R 14 = wa (Z.shiftr sz 4) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 12; 13; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sz P Hsc. destruct (nj0_setup regs m sz P) as [HR HK].
  set (E := Ez regs (VALS_nj0 sz)) in *. destruct P as [nj0_R14 nj0_rng_sz nj0_ka1].
  assert (Z32 : bv_unsigned (ev E 32) = sz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x5447c; 0x543c8] AXF_nj0.scr_pnjs 0x543b8 AXF_nj0.sr_nj0 AXF_nj0.kn_nj0 33 _ _ _ E m rom regs AXF_nj0.RES_pnjs_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_nj0.RES_pnjs fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (nj0_mem_pnjs m regs sz) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold nj0_mem_pnjs. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition nj0_mem_pnjm (m : word -> option byte) (regs : bvmap 5 word) (sz : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem nj0_pnjm : forall regs m rom sz, nj0_pre regs m sz ->
  scs_denot SEGS m (Ez regs (VALS_nj0 sz)) (snd (fst AXF_nj0.RES_pnjm)) ->
  exists R, msteps SEGS (mkst regs (wa 0x543b8) m rom) (mkst R (wa 0x543c8) (nj0_mem_pnjm m regs sz) rom) /\
    getr R 10 = wa 157 /\ getr R 11 = wa (sz + 12) /\ getr R 14 = wa (Z.shiftr sz 4) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 12; 13; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sz P Hsc. destruct (nj0_setup regs m sz P) as [HR HK].
  set (E := Ez regs (VALS_nj0 sz)) in *. destruct P as [nj0_R14 nj0_rng_sz nj0_ka1].
  assert (Z32 : bv_unsigned (ev E 32) = sz) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x5447c; 0x543c8] AXF_nj0.scr_pnjm 0x543b8 AXF_nj0.sr_nj0 AXF_nj0.kn_nj0 33 _ _ _ E m rom regs AXF_nj0.RES_pnjm_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_nj0.RES_pnjm fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (nj0_mem_pnjm m regs sz) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold nj0_mem_pnjm. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End NJ0.
End AXF_nj0z.

Module AXF_nr.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_G := EVar 32.
Definition e_sp0 := EVar 33.
Definition e_BASE := EVar 34.
Definition e_LEN := EVar 35.
Definition sr_nr := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 1 (ELit 0x53910)) 2 (EAlu ALU_ADD e_sp0 (ELit (-96)))) 9 (ELit 0x97c00)) 10 (e_BASE)) 11 (e_LEN)) 18 (ELit 0x97c98)) 19 (e_G)).
Definition kn_nr : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KRange e_G 1 (2^63-1) ].
Definition scr_nr : scripts := SCR [] [] [].
Definition ss_nr := SS 0x53a58 sr_nr [] kn_nr 36.
Definition RUN_nr := sym_exec SEGS 20 true [0x5396c] scr_nr ss_nr [].

Definition scr_pnr : scripts := SCR [] [] [].
Definition RES_pnr := Eval vm_compute in sym_exec SEGS 20 true [0x5396c] scr_pnr ss_nr [].
Lemma RES_pnr_ok : sym_exec SEGS 20 true [0x5396c] scr_pnr (SS 0x53a58 sr_nr [] kn_nr 36) [] = RES_pnr.
Proof. vm_compute. reflexivity. Qed.
End AXF_nr.

Module AXF_nrz.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section NR.
Context {fx : FPState}.

Definition VALS_nr (G sp0 BASE LEN : Z) : list Z := [G; sp0; BASE; LEN].

Record nr_pre (regs : bvmap 5 word) (m : word -> option byte) (G sp0 BASE LEN : Z) : Prop := {
  nr_R1 : getr regs 1 = wa 342288 ;
  nr_R2 : getr regs 2 = wa (sp0 + -96) ;
  nr_R9 : getr regs 9 = wa 621568 ;
  nr_R10 : getr regs 10 = wa BASE ;
  nr_R11 : getr regs 11 = wa LEN ;
  nr_R18 : getr regs 18 = wa 621720 ;
  nr_R19 : getr regs 19 = wa G ;
  nr_rng_G : 1 <= G <= 2^63-1 ;
  nr_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  nr_rng_BASE : 0 <= BASE <= 2^64-1 ;
  nr_rng_LEN : 0 <= LEN <= 2^64-1 ;
  nr_ka1 : sp0 mod 16 = 0
}.


#[using="Type"] Lemma nr_setup : forall regs m G sp0 BASE LEN, nr_pre regs m G sp0 BASE LEN ->
  regs_ok (Ez regs (VALS_nr G sp0 BASE LEN)) AXF_nr.sr_nr regs /\ know_ok SEGS (Ez regs (VALS_nr G sp0 BASE LEN)) m AXF_nr.kn_nr.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G sp0 BASE LEN P. destruct P as [nr_R1 nr_R2 nr_R9 nr_R10 nr_R11 nr_R18 nr_R19 nr_rng_G nr_rng_sp0 nr_rng_BASE nr_rng_LEN nr_ka1].
  set (E := Ez regs (VALS_nr G sp0 BASE LEN)).
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = BASE) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = LEN) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_nr.sr_nr.
    apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 2); [apply (regs_ok_pin E _ regs 1); [apply regs_ok_id|]|]|]|]|]|]|].
    - rewrite nr_R1. reflexivity.
    - rewrite nr_R2, zeval_sound. cbn [zeval edenot AXF_nr.e_G AXF_nr.e_sp0 AXF_nr.e_BASE AXF_nr.e_LEN]. rewrite ?Z32, ?Z33, ?Z34, ?Z35. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite nr_R9. reflexivity.
    - rewrite nr_R10. reflexivity.
    - rewrite nr_R11. reflexivity.
    - rewrite nr_R18. reflexivity.
    - rewrite nr_R19. reflexivity. }
  unfold know_ok, AXF_nr.kn_nr.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_nr.e_sp0 (wa sp0) 1024); [reflexivity | assumption | rewrite u_wa_small by lia; lia])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_nr.e_G AXF_nr.e_sp0 AXF_nr.e_BASE AXF_nr.e_LEN a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range G _ _ nr_rng_G eq_refl eq_refl), ?(mod64_of_range sp0 _ _ nr_rng_sp0 eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - nr_rng_G nr_rng_sp0 nr_rng_BASE nr_rng_LEN nr_ka1; lia).
  all: first [lia].
Qed.


Definition nr_mem_pnr (m : word -> option byte) (regs : bvmap 5 word) (G sp0 BASE LEN : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem nr_pnr : forall regs m rom G sp0 BASE LEN, nr_pre regs m G sp0 BASE LEN ->
  scs_denot SEGS m (Ez regs (VALS_nr G sp0 BASE LEN)) (snd (fst AXF_nr.RES_pnr)) ->
  exists R, msteps SEGS (mkst regs (wa 0x53a58) m rom) (mkst R (wa 0x5396c) (nr_mem_pnr m regs G sp0 BASE LEN) rom) /\
    getr R 1 = wa 342288 /\ getr R 2 = wa (sp0 + -96) /\ getr R 9 = wa 621568 /\ getr R 10 = wa G /\ getr R 11 = wa LEN /\ getr R 12 = wa BASE /\ getr R 18 = wa 621720 /\ getr R 19 = wa G /\ (forall k, In k [3; 4; 5; 6; 7; 8; 13; 14; 15; 16; 17; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G sp0 BASE LEN P Hsc. destruct (nr_setup regs m G sp0 BASE LEN P) as [HR HK].
  set (E := Ez regs (VALS_nr G sp0 BASE LEN)) in *. destruct P as [nr_R1 nr_R2 nr_R9 nr_R10 nr_R11 nr_R18 nr_R19 nr_rng_G nr_rng_sp0 nr_rng_BASE nr_rng_LEN nr_ka1].
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = BASE) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = LEN) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 20 [0x5396c] AXF_nr.scr_pnr 0x53a58 AXF_nr.sr_nr AXF_nr.kn_nr 36 _ _ _ E m rom regs AXF_nr.RES_pnr_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_nr.RES_pnr fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (nr_mem_pnr m regs G sp0 BASE LEN) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold nr_mem_pnr. repeat (apply (f_equal3 wbytes)); try reflexivity.
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

End NR.
End AXF_nrz.

Module AXF_nzl.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_c := EVar 32.
Definition e_a := EVar 33.
Definition e_size := EVar 34.
Definition sr_nzl := (sr_upd (sr_upd (sr_upd sr_id 11 (e_c)) 12 (e_a)) 24 (e_size)).
Definition kn_nzl : list kentry :=
  [ KRange e_c 1 33;
    KRange e_a 4096 (2^47);
    KRange e_size 16 2032;
    KWr (SA e_a 0) (ELit 1) ].
Definition scr_nzl : scripts := SCR [true] [] [].
Definition ss_nzl := SS 0x544e0 sr_nzl [] kn_nzl 35.
Definition RUN_nzl := sym_exec SEGS 100 true [0x544e0; 0x544f0] scr_nzl ss_nzl [].

Definition scr_pnzc : scripts := SCR [true] [] [].
Definition RES_pnzc := Eval vm_compute in sym_exec SEGS 100 true [0x544e0; 0x544f0] scr_pnzc ss_nzl [].
Lemma RES_pnzc_ok : sym_exec SEGS 100 true [0x544e0; 0x544f0] scr_pnzc (SS 0x544e0 sr_nzl [] kn_nzl 35) [] = RES_pnzc.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pnzx : scripts := SCR [false] [] [].
Definition RES_pnzx := Eval vm_compute in sym_exec SEGS 100 true [0x544e0; 0x544f0] scr_pnzx ss_nzl [].
Lemma RES_pnzx_ok : sym_exec SEGS 100 true [0x544e0; 0x544f0] scr_pnzx (SS 0x544e0 sr_nzl [] kn_nzl 35) [] = RES_pnzx.
Proof. vm_compute. reflexivity. Qed.
End AXF_nzl.

Module AXF_nzlz.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section NZL.
Context {fx : FPState}.

Definition VALS_nzl (c a size : Z) : list Z := [c; a; size].

Record nzl_pre (regs : bvmap 5 word) (m : word -> option byte) (c a size : Z) : Prop := {
  nzl_R11 : getr regs 11 = wa c ;
  nzl_R12 : getr regs 12 = wa a ;
  nzl_R24 : getr regs 24 = wa size ;
  nzl_rng_c : 1 <= c <= 33 ;
  nzl_rng_a : 4096 <= a <= 2^47 ;
  nzl_rng_size : 16 <= size <= 2032 ;
  nzl_kwr3 : forall d k, 0 <= d -> d + Z.of_nat k <= 1 -> store_ok SEGS m (wa (a + 0 + d)) k = true
}.


#[using="Type"] Lemma nzl_setup : forall regs m c a size, nzl_pre regs m c a size ->
  regs_ok (Ez regs (VALS_nzl c a size)) AXF_nzl.sr_nzl regs /\ know_ok SEGS (Ez regs (VALS_nzl c a size)) m AXF_nzl.kn_nzl.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m c a size P. destruct P as [nzl_R11 nzl_R12 nzl_R24 nzl_rng_c nzl_rng_a nzl_rng_size nzl_kwr3].
  set (E := Ez regs (VALS_nzl c a size)).
  assert (Z32 : bv_unsigned (ev E 32) = c) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = a) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = size) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_nzl.sr_nzl.
    apply (regs_ok_pin E _ regs 24); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply regs_ok_id|]|]|].
    - rewrite nzl_R11. reflexivity.
    - rewrite nzl_R12. reflexivity.
    - rewrite nzl_R24. reflexivity. }
  unfold know_ok, AXF_nzl.kn_nzl.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_nzl.e_c AXF_nzl.e_a AXF_nzl.e_size a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range c _ _ nzl_rng_c eq_refl eq_refl), ?(mod64_of_range a _ _ nzl_rng_a eq_refl eq_refl), ?(mod64_of_range size _ _ nzl_rng_size eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply nzl_kwr3]; assumption).
  all: try (clear - nzl_rng_c nzl_rng_a nzl_rng_size; lia).
  all: first [lia].
Qed.


Definition nzl_mem_pnzc (m : word -> option byte) (regs : bvmap 5 word) (c a size : Z) : word -> option byte :=
  wbytes (m) (wa (a + 0)) (word_to_le_bytes 1 (wa 0)).

#[using="Type"] Theorem nzl_pnzc : forall regs m rom c a size, nzl_pre regs m c a size ->
  scs_denot SEGS m (Ez regs (VALS_nzl c a size)) (snd (fst AXF_nzl.RES_pnzc)) ->
  exists R, msteps SEGS (mkst regs (wa 0x544e0) m rom) (mkst R (wa 0x544e0) (nzl_mem_pnzc m regs c a size) rom) /\
    getr R 11 = wa (c + -1) /\ getr R 12 = wa (a + size) /\ getr R 24 = wa size /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom c a size P Hsc. destruct (nzl_setup regs m c a size P) as [HR HK].
  set (E := Ez regs (VALS_nzl c a size)) in *. destruct P as [nzl_R11 nzl_R12 nzl_R24 nzl_rng_c nzl_rng_a nzl_rng_size nzl_kwr3].
  assert (Z32 : bv_unsigned (ev E 32) = c) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = a) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = size) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x544e0; 0x544f0] AXF_nzl.scr_pnzc 0x544e0 AXF_nzl.sr_nzl AXF_nzl.kn_nzl 35 _ _ _ E m rom regs AXF_nzl.RES_pnzc_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_nzl.RES_pnzc fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (nzl_mem_pnzc m regs c a size) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold nzl_mem_pnzc. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition nzl_mem_pnzx (m : word -> option byte) (regs : bvmap 5 word) (c a size : Z) : word -> option byte :=
  wbytes (m) (wa (a + 0)) (word_to_le_bytes 1 (wa 0)).

#[using="Type"] Theorem nzl_pnzx : forall regs m rom c a size, nzl_pre regs m c a size ->
  scs_denot SEGS m (Ez regs (VALS_nzl c a size)) (snd (fst AXF_nzl.RES_pnzx)) ->
  exists R, msteps SEGS (mkst regs (wa 0x544e0) m rom) (mkst R (wa 0x544f0) (nzl_mem_pnzx m regs c a size) rom) /\
    getr R 11 = wa (c + -1) /\ getr R 12 = wa (a + size) /\ getr R 24 = wa size /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom c a size P Hsc. destruct (nzl_setup regs m c a size P) as [HR HK].
  set (E := Ez regs (VALS_nzl c a size)) in *. destruct P as [nzl_R11 nzl_R12 nzl_R24 nzl_rng_c nzl_rng_a nzl_rng_size nzl_kwr3].
  assert (Z32 : bv_unsigned (ev E 32) = c) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = a) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = size) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x544e0; 0x544f0] AXF_nzl.scr_pnzx 0x544e0 AXF_nzl.sr_nzl AXF_nzl.kn_nzl 35 _ _ _ E m rom regs AXF_nzl.RES_pnzx_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_nzl.RES_pnzx fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (nzl_mem_pnzx m regs c a size) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold nzl_mem_pnzx. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End NZL.
End AXF_nzlz.

Module AXF_sp0.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

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
    KWord (SA (ELit 0) 416600) 8 (ELit 621568);
    KWord (SA (ELit 0) 621568) 8 e_can;
    KWord (SA (EMd M_MUL (ELit 8) e_sc) 621800) 8 e_hd;
    KDisj STK (ELit 1024) (SA (ELit 0) 416600) (ELit 8);
    KDisj STK (ELit 1024) (SA (ELit 0) 621568) (ELit 8);
    KDisj STK (ELit 1024) (SA (EMd M_MUL (ELit 8) e_sc) 621800) (ELit 8) ].
Definition scr_sp0 : scripts := SCR [] [] [].
Definition ss_sp0 := SS 0x540a8 sr_sp0 [] kn_sp0 37.
Definition RUN_sp0 := sym_exec SEGS 100 true [0x54108] scr_sp0 ss_sp0 [].

Definition scr_psp0 : scripts := SCR [] [] [].
Definition RES_psp0 := Eval vm_compute in sym_exec SEGS 100 true [0x54108] scr_psp0 ss_sp0 [].
Lemma RES_psp0_ok : sym_exec SEGS 100 true [0x54108] scr_psp0 (SS 0x540a8 sr_sp0 [] kn_sp0 37) [] = RES_psp0.
Proof. vm_compute. reflexivity. Qed.
End AXF_sp0.

Module AXF_sp0z.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

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
  sp0_kw5 : rdn SEGS m (wa (0 + 416600)) 8 = Some (word_to_le_bytes 8 (wa 621568)) ;
  sp0_kw6 : rdn SEGS m (wa (0 + 621568)) 8 = Some (word_to_le_bytes 8 (wa can)) ;
  sp0_kw7 : rdn SEGS m (wa (8 * sc + 621800)) 8 = Some (word_to_le_bytes 8 (wa hd)) ;
  sp0_kd8 : sp0 + -1024 + 1024 <= 0 + 416600 \/ 0 + 416600 + 8 <= sp0 + -1024 ;
  sp0_kd9 : sp0 + -1024 + 1024 <= 0 + 621568 \/ 0 + 621568 + 8 <= sp0 + -1024 ;
  sp0_kd10 : sp0 + -1024 + 1024 <= 8 * sc + 621800 \/ 8 * sc + 621800 + 8 <= sp0 + -1024
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
  exists R, msteps SEGS (mkst regs (wa 0x540a8) m rom) (mkst R (wa 0x54108) (sp0_mem_psp0 m regs sc req hd can sp0) rom) /\
    getr R 2 = wa (sp0 + -144) /\ getr R 8 = wa sc /\ getr R 10 = wa can /\ getr R 11 = wa 622832 /\ getr R 12 = wa hd /\ getr R 18 = wa req /\ getr R 20 = wa 621568 /\ getr R 21 = wa ((8 * sc) + 621800) /\ getr R 22 = wa 621712 /\ getr R 23 = wa ((8 * sc) + 621712) /\ (forall k, In k [1; 3; 4; 5; 6; 7; 9; 13; 14; 15; 16; 17; 19; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc req hd can sp0 P Hsc. destruct (sp0_setup regs m sc req hd can sp0 P) as [HR HK].
  set (E := Ez regs (VALS_sp0 sc req hd can sp0)) in *. destruct P as [sp0_R2 sp0_R10 sp0_R11 sp0_HSTK sp0_rng_sc sp0_rng_req sp0_rng_hd sp0_rng_can sp0_rng_sp0 sp0_ka1 sp0_kw5 sp0_kw6 sp0_kw7 sp0_kd8 sp0_kd9 sp0_kd10].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = req) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = hd) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = can) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x54108] AXF_sp0.scr_psp0 0x540a8 AXF_sp0.sr_sp0 AXF_sp0.kn_sp0 37 _ _ _ E m rom regs AXF_sp0.RES_psp0_ok HR HK Hsc) as (R & HR' & _ & Hms).
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

Module AXF_spe.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_G2 := EVar 32.
Definition e_mem2 := EVar 33.
Definition e_hb := EVar 34.
Definition e_W2 := EVar 35.
Definition e_cnt := EVar 36.
Definition sr_spe := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 10 (e_G2)) 11 (e_mem2)) 12 (e_hb)) 13 (e_W2)) 14 (e_cnt)).
Definition kn_spe : list kentry :=
  [ KRange e_G2 1 (2^63-1);
    KAlign e_G2 8;
    KRange e_mem2 1 (2^63-1);
    KRange e_hb 0 255;
    KRange e_W2 0 (2^63-1);
    KRange e_cnt 1 (2^28);
    KWord (SA e_G2 24) 4 (ELit 0);
    KWr (SA e_mem2 8) (ELit 1);
    KDisj (SA e_mem2 8) (ELit 1) (SA e_G2 24) (ELit 4) ].
Definition scr_spe : scripts := SCR [true; false] [] [].
Definition ss_spe := SS 0x545d8 sr_spe [] kn_spe 37.
Definition RUN_spe := sym_exec SEGS 100 true [0x541d0] scr_spe ss_spe [].

Definition scr_pspt : scripts := SCR [true; false] [] [].
Definition RES_pspt := Eval vm_compute in sym_exec SEGS 100 true [0x541d0] scr_pspt ss_spe [].
Lemma RES_pspt_ok : sym_exec SEGS 100 true [0x541d0] scr_pspt (SS 0x545d8 sr_spe [] kn_spe 37) [] = RES_pspt.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pspf : scripts := SCR [false; false] [] [].
Definition RES_pspf := Eval vm_compute in sym_exec SEGS 100 true [0x541d0] scr_pspf ss_spe [].
Lemma RES_pspf_ok : sym_exec SEGS 100 true [0x541d0] scr_pspf (SS 0x545d8 sr_spe [] kn_spe 37) [] = RES_pspf.
Proof. vm_compute. reflexivity. Qed.
End AXF_spe.

Module AXF_spez.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section SPE.
Context {fx : FPState}.

Definition VALS_spe (G2 mem2 hb W2 cnt : Z) : list Z := [G2; mem2; hb; W2; cnt].

Record spe_pre (regs : bvmap 5 word) (m : word -> option byte) (G2 mem2 hb W2 cnt : Z) : Prop := {
  spe_R10 : getr regs 10 = wa G2 ;
  spe_R11 : getr regs 11 = wa mem2 ;
  spe_R12 : getr regs 12 = wa hb ;
  spe_R13 : getr regs 13 = wa W2 ;
  spe_R14 : getr regs 14 = wa cnt ;
  spe_rng_G2 : 1 <= G2 <= 2^63-1 ;
  spe_rng_mem2 : 1 <= mem2 <= 2^63-1 ;
  spe_rng_hb : 0 <= hb <= 255 ;
  spe_rng_W2 : 0 <= W2 <= 2^63-1 ;
  spe_rng_cnt : 1 <= cnt <= 2^28 ;
  spe_ka1 : G2 mod 8 = 0 ;
  spe_kw6 : rdn SEGS m (wa (G2 + 24)) 4 = Some (word_to_le_bytes 4 (wa 0)) ;
  spe_kwr7 : forall d k, 0 <= d -> d + Z.of_nat k <= 1 -> store_ok SEGS m (wa (mem2 + 8 + d)) k = true ;
  spe_kd8 : mem2 + 8 + 1 <= G2 + 24 \/ G2 + 24 + 4 <= mem2 + 8
}.


#[using="Type"] Lemma spe_setup : forall regs m G2 mem2 hb W2 cnt, spe_pre regs m G2 mem2 hb W2 cnt ->
  regs_ok (Ez regs (VALS_spe G2 mem2 hb W2 cnt)) AXF_spe.sr_spe regs /\ know_ok SEGS (Ez regs (VALS_spe G2 mem2 hb W2 cnt)) m AXF_spe.kn_spe.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m G2 mem2 hb W2 cnt P. destruct P as [spe_R10 spe_R11 spe_R12 spe_R13 spe_R14 spe_rng_G2 spe_rng_mem2 spe_rng_hb spe_rng_W2 spe_rng_cnt spe_ka1 spe_kw6 spe_kwr7 spe_kd8].
  set (E := Ez regs (VALS_spe G2 mem2 hb W2 cnt)).
  assert (Z32 : bv_unsigned (ev E 32) = G2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = mem2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = hb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = W2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_spe.sr_spe.
    apply (regs_ok_pin E _ regs 14); [apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 12); [apply (regs_ok_pin E _ regs 11); [apply (regs_ok_pin E _ regs 10); [apply regs_ok_id|]|]|]|]|].
    - rewrite spe_R10. reflexivity.
    - rewrite spe_R11. reflexivity.
    - rewrite spe_R12. reflexivity.
    - rewrite spe_R13. reflexivity.
    - rewrite spe_R14. reflexivity. }
  unfold know_ok, AXF_spe.kn_spe.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_spe.e_G2 AXF_spe.e_mem2 AXF_spe.e_hb AXF_spe.e_W2 AXF_spe.e_cnt a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35, ?Z36.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range G2 _ _ spe_rng_G2 eq_refl eq_refl), ?(mod64_of_range mem2 _ _ spe_rng_mem2 eq_refl eq_refl), ?(mod64_of_range hb _ _ spe_rng_hb eq_refl eq_refl), ?(mod64_of_range W2 _ _ spe_rng_W2 eq_refl eq_refl), ?(mod64_of_range cnt _ _ spe_rng_cnt eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply spe_kwr7]; assumption).
  all: try (clear - spe_rng_G2 spe_rng_mem2 spe_rng_hb spe_rng_W2 spe_rng_cnt spe_ka1; lia).
  all: first [(clear - spe_rng_G2 spe_rng_mem2 spe_rng_hb spe_rng_W2 spe_rng_cnt spe_ka1 spe_kd8; lia) | lia].
Qed.


Definition spe_mem_pspt (m : word -> option byte) (regs : bvmap 5 word) (G2 mem2 hb W2 cnt : Z) : word -> option byte :=
  wbytes (m) (wa (mem2 + 8)) (word_to_le_bytes 1 (wa ((32 * Z.shiftr hb 5) + Z.land (((cnt + -1)) mod 2^64) 31))).

#[using="Type"] Theorem spe_pspt : forall regs m rom G2 mem2 hb W2 cnt, spe_pre regs m G2 mem2 hb W2 cnt ->
  scs_denot SEGS m (Ez regs (VALS_spe G2 mem2 hb W2 cnt)) (snd (fst AXF_spe.RES_pspt)) ->
  exists R, msteps SEGS (mkst regs (wa 0x545d8) m rom) (mkst R (wa 0x541d0) (spe_mem_pspt m regs G2 mem2 hb W2 cnt) rom) /\
    getr R 10 = wa G2 /\ getr R 11 = wa 0 /\ getr R 12 = wa ((32 * Z.shiftr hb 5) + Z.land (((cnt + -1)) mod 2^64) 31) /\ getr R 13 = wa (Z.land W2 31 + 1) /\ getr R 14 = wa (Z.land (((cnt + -1)) mod 2^64) 31) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G2 mem2 hb W2 cnt P Hsc. destruct (spe_setup regs m G2 mem2 hb W2 cnt P) as [HR HK].
  set (E := Ez regs (VALS_spe G2 mem2 hb W2 cnt)) in *. destruct P as [spe_R10 spe_R11 spe_R12 spe_R13 spe_R14 spe_rng_G2 spe_rng_mem2 spe_rng_hb spe_rng_W2 spe_rng_cnt spe_ka1 spe_kw6 spe_kwr7 spe_kd8].
  assert (Z32 : bv_unsigned (ev E 32) = G2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = mem2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = hb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = W2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x541d0] AXF_spe.scr_pspt 0x545d8 AXF_spe.sr_spe AXF_spe.kn_spe 37 _ _ _ E m rom regs AXF_spe.RES_pspt_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_spe.RES_pspt fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (spe_mem_pspt m regs G2 mem2 hb W2 cnt) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold spe_mem_pspt. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition spe_mem_pspf (m : word -> option byte) (regs : bvmap 5 word) (G2 mem2 hb W2 cnt : Z) : word -> option byte :=
  wbytes (m) (wa (mem2 + 8)) (word_to_le_bytes 1 (wa ((32 * Z.shiftr hb 5) + Z.land W2 31))).

#[using="Type"] Theorem spe_pspf : forall regs m rom G2 mem2 hb W2 cnt, spe_pre regs m G2 mem2 hb W2 cnt ->
  scs_denot SEGS m (Ez regs (VALS_spe G2 mem2 hb W2 cnt)) (snd (fst AXF_spe.RES_pspf)) ->
  exists R, msteps SEGS (mkst regs (wa 0x545d8) m rom) (mkst R (wa 0x541d0) (spe_mem_pspf m regs G2 mem2 hb W2 cnt) rom) /\
    getr R 10 = wa G2 /\ getr R 11 = wa 0 /\ getr R 12 = wa ((32 * Z.shiftr hb 5) + Z.land W2 31) /\ getr R 13 = wa (Z.land W2 31 + 1) /\ getr R 14 = wa (Z.land W2 31) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G2 mem2 hb W2 cnt P Hsc. destruct (spe_setup regs m G2 mem2 hb W2 cnt P) as [HR HK].
  set (E := Ez regs (VALS_spe G2 mem2 hb W2 cnt)) in *. destruct P as [spe_R10 spe_R11 spe_R12 spe_R13 spe_R14 spe_rng_G2 spe_rng_mem2 spe_rng_hb spe_rng_W2 spe_rng_cnt spe_ka1 spe_kw6 spe_kwr7 spe_kd8].
  assert (Z32 : bv_unsigned (ev E 32) = G2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = mem2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = hb) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = W2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = cnt) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x541d0] AXF_spe.scr_pspf 0x545d8 AXF_spe.sr_spe AXF_spe.kn_spe 37 _ _ _ E m rom regs AXF_spe.RES_pspf_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_spe.RES_pspf fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (spe_mem_pspf m regs G2 mem2 hb W2 cnt) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold spe_mem_pspf. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End SPE.
End AXF_spez.

Module AXF_spi.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_t0 := EVar 32.
Definition e_a4 := EVar 33.
Definition e_a5 := EVar 34.
Definition e_a6 := EVar 35.
Definition sr_spi := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 5 (e_t0)) 14 (e_a4)) 15 (e_a5)) 16 (e_a6)) 17 (ELit 4096)).
Definition kn_spi : list kentry :=
  [ KRange e_t0 0 (2^28);
    KRange e_a4 0 (2^28);
    KRange e_a5 16 (2^20);
    KRange e_a6 0 (2^28) ].
Definition scr_spi : scripts := SCR [true] [] [].
Definition ss_spi := SS 0x545c4 sr_spi [] kn_spi 36.
Definition RUN_spi := sym_exec SEGS 100 true [0x545c4; 0x545d8] scr_spi ss_spi [].

Definition scr_pspl : scripts := SCR [true] [] [].
Definition RES_pspl := Eval vm_compute in sym_exec SEGS 100 true [0x545c4; 0x545d8] scr_pspl ss_spi [].
Lemma RES_pspl_ok : sym_exec SEGS 100 true [0x545c4; 0x545d8] scr_pspl (SS 0x545c4 sr_spi [] kn_spi 36) [] = RES_pspl.
Proof. vm_compute. reflexivity. Qed.

Definition scr_pspx : scripts := SCR [false] [] [].
Definition RES_pspx := Eval vm_compute in sym_exec SEGS 100 true [0x545c4; 0x545d8] scr_pspx ss_spi [].
Lemma RES_pspx_ok : sym_exec SEGS 100 true [0x545c4; 0x545d8] scr_pspx (SS 0x545c4 sr_spi [] kn_spi 36) [] = RES_pspx.
Proof. vm_compute. reflexivity. Qed.
End AXF_spi.

Module AXF_spiz.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section SPI.
Context {fx : FPState}.

Definition VALS_spi (t0 a4 a5 a6 : Z) : list Z := [t0; a4; a5; a6].

Record spi_pre (regs : bvmap 5 word) (m : word -> option byte) (t0 a4 a5 a6 : Z) : Prop := {
  spi_R5 : getr regs 5 = wa t0 ;
  spi_R14 : getr regs 14 = wa a4 ;
  spi_R15 : getr regs 15 = wa a5 ;
  spi_R16 : getr regs 16 = wa a6 ;
  spi_R17 : getr regs 17 = wa 4096 ;
  spi_rng_t0 : 0 <= t0 <= 2^28 ;
  spi_rng_a4 : 0 <= a4 <= 2^28 ;
  spi_rng_a5 : 16 <= a5 <= 2^20 ;
  spi_rng_a6 : 0 <= a6 <= 2^28
}.


#[using="Type"] Lemma spi_setup : forall regs m t0 a4 a5 a6, spi_pre regs m t0 a4 a5 a6 ->
  regs_ok (Ez regs (VALS_spi t0 a4 a5 a6)) AXF_spi.sr_spi regs /\ know_ok SEGS (Ez regs (VALS_spi t0 a4 a5 a6)) m AXF_spi.kn_spi.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m t0 a4 a5 a6 P. destruct P as [spi_R5 spi_R14 spi_R15 spi_R16 spi_R17 spi_rng_t0 spi_rng_a4 spi_rng_a5 spi_rng_a6].
  set (E := Ez regs (VALS_spi t0 a4 a5 a6)).
  assert (Z32 : bv_unsigned (ev E 32) = t0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = a4) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = a5) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = a6) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_spi.sr_spi.
    apply (regs_ok_pin E _ regs 17); [apply (regs_ok_pin E _ regs 16); [apply (regs_ok_pin E _ regs 15); [apply (regs_ok_pin E _ regs 14); [apply (regs_ok_pin E _ regs 5); [apply regs_ok_id|]|]|]|]|].
    - rewrite spi_R5. reflexivity.
    - rewrite spi_R14. reflexivity.
    - rewrite spi_R15. reflexivity.
    - rewrite spi_R16. reflexivity.
    - rewrite spi_R17. reflexivity. }
  unfold know_ok, AXF_spi.kn_spi.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_spi.e_t0 AXF_spi.e_a4 AXF_spi.e_a5 AXF_spi.e_a6 a_base a_off].
  all: rewrite ?Z32, ?Z33, ?Z34, ?Z35.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range t0 _ _ spi_rng_t0 eq_refl eq_refl), ?(mod64_of_range a4 _ _ spi_rng_a4 eq_refl eq_refl), ?(mod64_of_range a5 _ _ spi_rng_a5 eq_refl eq_refl), ?(mod64_of_range a6 _ _ spi_rng_a6 eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [idtac]; assumption).
  all: try (clear - spi_rng_t0 spi_rng_a4 spi_rng_a5 spi_rng_a6; lia).
  all: first [lia].
Qed.


Definition spi_mem_pspl (m : word -> option byte) (regs : bvmap 5 word) (t0 a4 a5 a6 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem spi_pspl : forall regs m rom t0 a4 a5 a6, spi_pre regs m t0 a4 a5 a6 ->
  scs_denot SEGS m (Ez regs (VALS_spi t0 a4 a5 a6)) (snd (fst AXF_spi.RES_pspl)) ->
  exists R, msteps SEGS (mkst regs (wa 0x545c4) m rom) (mkst R (wa 0x545c4) (spi_mem_pspl m regs t0 a4 a5 a6) rom) /\
    getr R 5 = wa (t0 + a5) /\ getr R 14 = wa (a4 + 1) /\ getr R 15 = wa a5 /\ getr R 16 = wa (a5 + a6) /\ getr R 17 = wa 4096 /\ (forall k, In k [1; 2; 3; 4; 7; 8; 9; 10; 11; 12; 13; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom t0 a4 a5 a6 P Hsc. destruct (spi_setup regs m t0 a4 a5 a6 P) as [HR HK].
  set (E := Ez regs (VALS_spi t0 a4 a5 a6)) in *. destruct P as [spi_R5 spi_R14 spi_R15 spi_R16 spi_R17 spi_rng_t0 spi_rng_a4 spi_rng_a5 spi_rng_a6].
  assert (Z32 : bv_unsigned (ev E 32) = t0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = a4) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = a5) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = a6) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x545c4; 0x545d8] AXF_spi.scr_pspl 0x545c4 AXF_spi.sr_spi AXF_spi.kn_spi 36 _ _ _ E m rom regs AXF_spi.RES_pspl_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_spi.RES_pspl fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (spi_mem_pspl m regs t0 a4 a5 a6) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold spi_mem_pspl. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.


Definition spi_mem_pspx (m : word -> option byte) (regs : bvmap 5 word) (t0 a4 a5 a6 : Z) : word -> option byte :=
  m.

#[using="Type"] Theorem spi_pspx : forall regs m rom t0 a4 a5 a6, spi_pre regs m t0 a4 a5 a6 ->
  scs_denot SEGS m (Ez regs (VALS_spi t0 a4 a5 a6)) (snd (fst AXF_spi.RES_pspx)) ->
  exists R, msteps SEGS (mkst regs (wa 0x545c4) m rom) (mkst R (wa 0x545d8) (spi_mem_pspx m regs t0 a4 a5 a6) rom) /\
    getr R 5 = wa (t0 + a5) /\ getr R 14 = wa (a4 + 1) /\ getr R 15 = wa a5 /\ getr R 16 = wa (a5 + a6) /\ getr R 17 = wa 4096 /\ (forall k, In k [1; 2; 3; 4; 7; 8; 9; 10; 11; 12; 13; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom t0 a4 a5 a6 P Hsc. destruct (spi_setup regs m t0 a4 a5 a6 P) as [HR HK].
  set (E := Ez regs (VALS_spi t0 a4 a5 a6)) in *. destruct P as [spi_R5 spi_R14 spi_R15 spi_R16 spi_R17 spi_rng_t0 spi_rng_a4 spi_rng_a5 spi_rng_a6].
  assert (Z32 : bv_unsigned (ev E 32) = t0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = a4) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = a5) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = a6) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x545c4; 0x545d8] AXF_spi.scr_pspx 0x545c4 AXF_spi.sr_spi AXF_spi.kn_spi 36 _ _ _ E m rom regs AXF_spi.RES_pspx_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_spi.RES_pspx fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (spi_mem_pspx m regs t0 a4 a5 a6) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold spi_mem_pspx. repeat (apply (f_equal3 wbytes)); try reflexivity.
    all: try zpost_one.

  - clear Hms.      (* [comment removed for export] *)
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    split; [zpost_reg HR'|].
    intros k Hk. cbn [In] in Hk. repeat (destruct Hk as [<-|Hk]; [rewrite (HR' _); reflexivity|]). destruct Hk.
Qed.

End SPI.
End AXF_spiz.

Module AXF_t2.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_sp0 := EVar 33.
Definition e_BASE := EVar 34.
Definition e_LEN := EVar 35.
Definition e_ERR := EVar 36.
Definition e_ra := EVar 38.
Definition e_s0 := EVar 39.
Definition e_s1 := EVar 40.
Definition e_s2 := EVar 41.
Definition e_s3 := EVar 42.
Definition STK := SA e_sp0 (-1024).
Definition sr_t2 := (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr_id 1 (ELit 0x55304)) 2 (EAlu ALU_ADD e_sp0 (ELit (-80)))) 4 (ELit 0x77990)) 8 (e_LEN)) 9 (e_BASE)) 10 (ELit 0)) 17 (ELit 215)) 18 (ELit 0x778ec)) 19 (e_ERR)).
Definition kn_t2 : list kentry :=
  [ KRange e_sp0 (2^20) (2^47);
    KAlign e_sp0 16;
    KWr STK (ELit 1024);
    KWord (SA e_sp0 (-56)) 8 (ELit 0x53550);
    KWord (SA e_sp0 (-64)) 8 e_BASE;
    KWord (SA e_sp0 (-72)) 8 e_LEN;
    KWord (SA e_sp0 (-8)) 8 e_ra;
    KWord (SA e_sp0 (-16)) 8 e_s0;
    KWord (SA e_sp0 (-24)) 8 e_s1;
    KWord (SA e_sp0 (-32)) 8 e_s2;
    KWord (SA e_sp0 (-40)) 8 e_s3;
    KWr (SA (ELit 0) 0x778ec) (ELit 4);
    KDisj STK (ELit 1024) (SA (ELit 0) 0x778ec) (ELit 4) ].
Definition scr_t2 : scripts := SCR [true] [] [].
Definition ss_t2 := SS 0x55314 sr_t2 [] kn_t2 43.
Definition RUN_t2 := sym_exec SEGS 100 true [] scr_t2 ss_t2 [].

Definition scr_pt2 : scripts := SCR [true] [] [].
Definition RES_pt2 := Eval vm_compute in sym_exec SEGS 100 true [] scr_pt2 ss_t2 [].
Lemma RES_pt2_ok : sym_exec SEGS 100 true [] scr_pt2 (SS 0x55314 sr_t2 [] kn_t2 43) [] = RES_pt2.
Proof. vm_compute. reflexivity. Qed.
End AXF_t2.

Module AXF_t2z.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Section T2.
Context {fx : FPState}.

Definition VALS_t2 (sp0 BASE LEN ERR ra s0 s1 s2 s3 : Z) : list Z := [0; sp0; BASE; LEN; ERR; 0; ra; s0; s1; s2; s3].

Record t2_pre (regs : bvmap 5 word) (m : word -> option byte) (sp0 BASE LEN ERR ra s0 s1 s2 s3 : Z) : Prop := {
  t2_R1 : getr regs 1 = wa 348932 ;
  t2_R2 : getr regs 2 = wa (sp0 + -80) ;
  t2_R4 : getr regs 4 = wa 489872 ;
  t2_R8 : getr regs 8 = wa LEN ;
  t2_R9 : getr regs 9 = wa BASE ;
  t2_R10 : getr regs 10 = wa 0 ;
  t2_R17 : getr regs 17 = wa 215 ;
  t2_R18 : getr regs 18 = wa 489708 ;
  t2_R19 : getr regs 19 = wa ERR ;
  t2_HSTK : stk_ok SEGS m (wa sp0) 1024 ;
  t2_rng_sp0 : 2^20 <= sp0 <= 2^47 ;
  t2_rng_BASE : 0 <= BASE <= 2^64-1 ;
  t2_rng_LEN : 0 <= LEN <= 2^64-1 ;
  t2_rng_ERR : 0 <= ERR <= 2^64-1 ;
  t2_rng_ra : 0 <= ra <= 2^64-1 ;
  t2_rng_s0 : 0 <= s0 <= 2^64-1 ;
  t2_rng_s1 : 0 <= s1 <= 2^64-1 ;
  t2_rng_s2 : 0 <= s2 <= 2^64-1 ;
  t2_rng_s3 : 0 <= s3 <= 2^64-1 ;
  t2_ka1 : sp0 mod 16 = 0 ;
  t2_kw3 : rdn SEGS m (wa (sp0 + -56)) 8 = Some (word_to_le_bytes 8 (wa 341328)) ;
  t2_kw4 : rdn SEGS m (wa (sp0 + -64)) 8 = Some (word_to_le_bytes 8 (wa BASE)) ;
  t2_kw5 : rdn SEGS m (wa (sp0 + -72)) 8 = Some (word_to_le_bytes 8 (wa LEN)) ;
  t2_kw6 : rdn SEGS m (wa (sp0 + -8)) 8 = Some (word_to_le_bytes 8 (wa ra)) ;
  t2_kw7 : rdn SEGS m (wa (sp0 + -16)) 8 = Some (word_to_le_bytes 8 (wa s0)) ;
  t2_kw8 : rdn SEGS m (wa (sp0 + -24)) 8 = Some (word_to_le_bytes 8 (wa s1)) ;
  t2_kw9 : rdn SEGS m (wa (sp0 + -32)) 8 = Some (word_to_le_bytes 8 (wa s2)) ;
  t2_kw10 : rdn SEGS m (wa (sp0 + -40)) 8 = Some (word_to_le_bytes 8 (wa s3)) ;
  t2_kwr11 : forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (0 + 489708 + d)) k = true ;
  t2_kd12 : sp0 + -1024 + 1024 <= 0 + 489708 \/ 0 + 489708 + 4 <= sp0 + -1024
}.


#[using="Type"] Lemma t2_setup : forall regs m sp0 BASE LEN ERR ra s0 s1 s2 s3, t2_pre regs m sp0 BASE LEN ERR ra s0 s1 s2 s3 ->
  regs_ok (Ez regs (VALS_t2 sp0 BASE LEN ERR ra s0 s1 s2 s3)) AXF_t2.sr_t2 regs /\ know_ok SEGS (Ez regs (VALS_t2 sp0 BASE LEN ERR ra s0 s1 s2 s3)) m AXF_t2.kn_t2.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m sp0 BASE LEN ERR ra s0 s1 s2 s3 P. destruct P as [t2_R1 t2_R2 t2_R4 t2_R8 t2_R9 t2_R10 t2_R17 t2_R18 t2_R19 t2_HSTK t2_rng_sp0 t2_rng_BASE t2_rng_LEN t2_rng_ERR t2_rng_ra t2_rng_s0 t2_rng_s1 t2_rng_s2 t2_rng_s3 t2_ka1 t2_kw3 t2_kw4 t2_kw5 t2_kw6 t2_kw7 t2_kw8 t2_kw9 t2_kw10 t2_kwr11 t2_kd12].
  set (E := Ez regs (VALS_t2 sp0 BASE LEN ERR ra s0 s1 s2 s3)).
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = BASE) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = LEN) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = ERR) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = ra) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = s0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = s1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = s2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = s3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  split.
  { unfold AXF_t2.sr_t2.
    apply (regs_ok_pin E _ regs 19); [apply (regs_ok_pin E _ regs 18); [apply (regs_ok_pin E _ regs 17); [apply (regs_ok_pin E _ regs 10); [apply (regs_ok_pin E _ regs 9); [apply (regs_ok_pin E _ regs 8); [apply (regs_ok_pin E _ regs 4); [apply (regs_ok_pin E _ regs 2); [apply (regs_ok_pin E _ regs 1); [apply regs_ok_id|]|]|]|]|]|]|]|]|].
    - rewrite t2_R1. reflexivity.
    - rewrite t2_R2, zeval_sound. cbn [zeval edenot AXF_t2.e_sp0 AXF_t2.e_BASE AXF_t2.e_LEN AXF_t2.e_ERR AXF_t2.e_ra AXF_t2.e_s0 AXF_t2.e_s1 AXF_t2.e_s2 AXF_t2.e_s3 AXF_t2.STK]. rewrite ?Z33, ?Z34, ?Z35, ?Z36, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42. repeat dsc_mod. litmods. first [reflexivity | (apply wa_eqm; rewrite ?Z.mod_mod by lia; reflexivity) | (apply wa_eqm; f_equal; ring)].
    - rewrite t2_R4. reflexivity.
    - rewrite t2_R8. reflexivity.
    - rewrite t2_R9. reflexivity.
    - rewrite t2_R10. reflexivity.
    - rewrite t2_R17. reflexivity.
    - rewrite t2_R18. reflexivity.
    - rewrite t2_R19. reflexivity. }
  unfold know_ok, AXF_t2.kn_t2.
  repeat (first [apply Forall_nil | apply Forall_cons]).
  all: first [ (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => idtac end; apply (kwr_of_stk_ok SEGS E m AXF_t2.e_sp0 (wa sp0) 1024); [reflexivity | assumption | rewrite u_wa_small by lia; lia])
             | (lazymatch goal with |- kentry_ok _ _ _ (KWord _ _ _) => apply kword_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KRange _ _ _) => apply krange_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KAlign _ _) => apply kalign_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KDisj _ _ _ _) => apply kdisj_z end) | (lazymatch goal with |- kentry_ok _ _ _ (KWr _ _) => apply kwr_z end) ].
  all: cbn [zeval edenot AXF_t2.e_sp0 AXF_t2.e_BASE AXF_t2.e_LEN AXF_t2.e_ERR AXF_t2.e_ra AXF_t2.e_s0 AXF_t2.e_s1 AXF_t2.e_s2 AXF_t2.e_s3 AXF_t2.STK a_base a_off].
  all: rewrite ?Z33, ?Z34, ?Z35, ?Z36, ?Z38, ?Z39, ?Z40, ?Z41, ?Z42.
  all: try zlit.
  all: try assumption.
  all: try zrange.
  all: rewrite ?(mod64_of_range sp0 _ _ t2_rng_sp0 eq_refl eq_refl).
  all: litmods.
  all: change (Z.shiftr ((4503599627370496 * ?w) mod 2^64) 58) with (SCW w).
  all: try assumption.
  all: try (intros d k Hd Hk; first [apply t2_kwr11]; assumption).
  all: try (clear - t2_rng_sp0 t2_rng_BASE t2_rng_LEN t2_rng_ERR t2_rng_ra t2_rng_s0 t2_rng_s1 t2_rng_s2 t2_rng_s3 t2_ka1; lia).
  all: first [(clear - t2_rng_sp0 t2_rng_BASE t2_rng_LEN t2_rng_ERR t2_rng_ra t2_rng_s0 t2_rng_s1 t2_rng_s2 t2_rng_s3 t2_ka1 t2_kd12; lia) | lia].
Qed.


Definition t2_mem_pt2 (m : word -> option byte) (regs : bvmap 5 word) (sp0 BASE LEN ERR ra s0 s1 s2 s3 : Z) : word -> option byte :=
  wbytes (m) (wa (0 + 489708)) (word_to_le_bytes 4 (wa ERR)).

#[using="Type"] Theorem t2_pt2 : forall regs m rom sp0 BASE LEN ERR ra s0 s1 s2 s3, t2_pre regs m sp0 BASE LEN ERR ra s0 s1 s2 s3 ->
  scs_denot SEGS m (Ez regs (VALS_t2 sp0 BASE LEN ERR ra s0 s1 s2 s3)) (snd (fst AXF_t2.RES_pt2)) ->
  exists R, msteps SEGS (mkst regs (wa 0x55314) m rom) (mkst R (wa 0x53574) (t2_mem_pt2 m regs sp0 BASE LEN ERR ra s0 s1 s2 s3) rom) /\
    getr R 1 = wa ra /\ getr R 2 = wa sp0 /\ getr R 4 = wa 489872 /\ getr R 8 = wa s0 /\ getr R 9 = wa s1 /\ getr R 10 = wa 0 /\ getr R 11 = wa 18446744073709547521 /\ getr R 17 = wa 215 /\ getr R 18 = wa s2 /\ getr R 19 = wa s3 /\ (forall k, In k [3; 5; 6; 7; 12; 13; 14; 15; 16; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sp0 BASE LEN ERR ra s0 s1 s2 s3 P Hsc. destruct (t2_setup regs m sp0 BASE LEN ERR ra s0 s1 s2 s3 P) as [HR HK].
  set (E := Ez regs (VALS_t2 sp0 BASE LEN ERR ra s0 s1 s2 s3)) in *. destruct P as [t2_R1 t2_R2 t2_R4 t2_R8 t2_R9 t2_R10 t2_R17 t2_R18 t2_R19 t2_HSTK t2_rng_sp0 t2_rng_BASE t2_rng_LEN t2_rng_ERR t2_rng_ra t2_rng_s0 t2_rng_s1 t2_rng_s2 t2_rng_s3 t2_ka1 t2_kw3 t2_kw4 t2_kw5 t2_kw6 t2_kw7 t2_kw8 t2_kw9 t2_kw10 t2_kwr11 t2_kd12].
  assert (Z33 : bv_unsigned (ev E 33) = sp0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z34 : bv_unsigned (ev E 34) = BASE) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z35 : bv_unsigned (ev E 35) = LEN) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z36 : bv_unsigned (ev E 36) = ERR) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z38 : bv_unsigned (ev E 38) = ra) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z39 : bv_unsigned (ev E 39) = s0) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z40 : bv_unsigned (ev E 40) = s1) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z41 : bv_unsigned (ev E 41) = s2) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z42 : bv_unsigned (ev E 42) = s3) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [] AXF_t2.scr_pt2 0x55314 AXF_t2.sr_t2 AXF_t2.kn_t2 43 _ _ _ E m rom regs AXF_t2.RES_pt2_ok HR HK Hsc) as (R & HR' & _ & Hms).
  exists R. split.
  - cbn [AXF_t2.RES_pt2 fst snd s_pc s_log] in Hms.
    lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (t2_mem_pt2 m regs sp0 BASE LEN ERR ra s0 s1 s2 s3) with M; [exact Hms|] end.
    clear Hms HR'. cbn [mem_denot]. unfold t2_mem_pt2. repeat (apply (f_equal3 wbytes)); try reflexivity.
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

End T2.
End AXF_t2z.

Module AXF_ta0.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_sc := EVar 32.
Definition sr_ta0 := (sr_upd sr_id 12 (ELit 0)).
Definition kn_ta0 : list kentry :=
  [ KRange e_sc 0 47 ].
Definition scr_ta0 : scripts := SCR [] [] [].
Definition ss_ta0 := SS 0x54108 sr_ta0 [] kn_ta0 33.
Definition RUN_ta0 := sym_exec SEGS 100 true [0x54288] scr_ta0 ss_ta0 [].

Definition scr_pta0 : scripts := SCR [] [] [].
Definition RES_pta0 := Eval vm_compute in sym_exec SEGS 100 true [0x54288] scr_pta0 ss_ta0 [].
Lemma RES_pta0_ok : sym_exec SEGS 100 true [0x54288] scr_pta0 (SS 0x54108 sr_ta0 [] kn_ta0 33) [] = RES_pta0.
Proof. vm_compute. reflexivity. Qed.
End AXF_ta0.

Module AXF_ta0z.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

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
  exists R, msteps SEGS (mkst regs (wa 0x54108) m rom) (mkst R (wa 0x54288) (ta0_mem_pta0 m regs sc) rom) /\
    getr R 12 = wa 0 /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom sc P Hsc. destruct (ta0_setup regs m sc P) as [HR HK].
  set (E := Ez regs (VALS_ta0 sc)) in *. destruct P as [ta0_R12 ta0_rng_sc].
  assert (Z32 : bv_unsigned (ev E 32) = sc) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x54288] AXF_ta0.scr_pta0 0x54108 AXF_ta0.sr_ta0 AXF_ta0.kn_ta0 33 _ _ _ E m rom regs AXF_ta0.RES_pta0_ok HR HK Hsc) as (R & HR' & _ & Hms).
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
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Definition e_G := EVar 32.
Definition e_avail := EVar 33.
Definition sr_ta1a := (sr_upd sr_id 12 (e_G)).
Definition kn_ta1a : list kentry :=
  [ KRange e_G 1 (2^63-1);
    KAlign e_G 8;
    KRange e_avail 1 (2^32-1);
    KWord (SA e_G 24) 4 e_avail ].
Definition scr_ta1a : scripts := SCR [false] [] [].
Definition ss_ta1a := SS 0x54108 sr_ta1a [] kn_ta1a 34.
Definition RUN_ta1a := sym_exec SEGS 100 true [0x54248] scr_ta1a ss_ta1a [].

Definition scr_pta1a : scripts := SCR [false] [] [].
Definition RES_pta1a := Eval vm_compute in sym_exec SEGS 100 true [0x54248] scr_pta1a ss_ta1a [].
Lemma RES_pta1a_ok : sym_exec SEGS 100 true [0x54248] scr_pta1a (SS 0x54108 sr_ta1a [] kn_ta1a 34) [] = RES_pta1a.
Proof. vm_compute. reflexivity. Qed.
End AXF_ta1a.

Module AXF_ta1az.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxBits MngZ.

Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

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
  exists R, msteps SEGS (mkst regs (wa 0x54108) m rom) (mkst R (wa 0x54248) (ta1a_mem_pta1a m regs G avail) rom) /\
    getr R 10 = wa G /\ getr R 11 = wa (ext_Z true 0 4 avail) /\ (forall k, In k [1; 2; 3; 4; 5; 6; 7; 8; 9; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat -> getr R (Z_to_bv 5 (Z.of_nat k)) = getr regs (Z_to_bv 5 (Z.of_nat k))).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs m rom G avail P Hsc. destruct (ta1a_setup regs m G avail P) as [HR HK].
  set (E := Ez regs (VALS_ta1a G avail)) in *. destruct P as [ta1a_R12 ta1a_rng_G ta1a_rng_avail ta1a_ka1 ta1a_kw3].
  assert (Z32 : bv_unsigned (ev E 32) = G) by (apply zatom; [reflexivity | reflexivity | zrange]).
  assert (Z33 : bv_unsigned (ev E 33) = avail) by (apply zatom; [reflexivity | reflexivity | zrange]).
  destruct (run_sound SEGS 100 [0x54248] AXF_ta1a.scr_pta1a 0x54108 AXF_ta1a.sr_ta1a AXF_ta1a.kn_ta1a 34 _ _ _ E m rom regs AXF_ta1a.RES_pta1a_ok HR HK Hsc) as (R & HR' & _ & Hms).
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

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Record ntf_frame (regs : bvmap 5 word) (m : word -> option byte) (sp0 canary ra s0 s1 s2 s3 : Z) : Prop := {
  nf_R2 : getr regs 2 = wa (sp0 - 96) ; nf_R9 : getr regs 9 = wa 0x97c00 ;
  nf_Rsp : 2^20 <= sp0 <= 2^47 ; nf_Asp : sp0 mod 16 = 0 ; nf_HSTK : stk_ok SEGS m (wa sp0) 1024 ;
  nf_Rcan : 0 <= canary <= 2^64-1 ; nf_Rra : 0 <= ra <= 2^64-1 ; nf_Rs0 : 0 <= s0 <= 2^64-1 ; nf_Rs1 : 0 <= s1 <= 2^64-1 ;
  nf_Rs2 : 0 <= s2 <= 2^64-1 ; nf_Rs3 : 0 <= s3 <= 2^64-1 ;
  nf_Mra : rdn SEGS m (wa (sp0 + -8)) 8 = Some (word_to_le_bytes 8 (wa ra)) ;
  nf_Ms0 : rdn SEGS m (wa (sp0 + -16)) 8 = Some (word_to_le_bytes 8 (wa s0)) ;
  nf_Ms1 : rdn SEGS m (wa (sp0 + -24)) 8 = Some (word_to_le_bytes 8 (wa s1)) ;
  nf_Ms2 : rdn SEGS m (wa (sp0 + -32)) 8 = Some (word_to_le_bytes 8 (wa s2)) ;
  nf_Ms3 : rdn SEGS m (wa (sp0 + -40)) 8 = Some (word_to_le_bytes 8 (wa s3)) ;
  nf_Mcan : rdn SEGS m (wa (sp0 + -48)) 8 = Some (word_to_le_bytes 8 (wa canary)) ;
  nf_Mgd : rdn SEGS m (wa (0 + 0x97c00)) 8 = Some (word_to_le_bytes 8 (wa canary))
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
    (wa (8 * sc + 621800)) (word_to_le_bytes 8 (wa G))) (wa (G + 28)) (word_to_le_bytes 4 (wa (Z.lor freed (2^idx)))).
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
  ep_DGd : G + 40 <= 0x97c00 \/ 0x97c00 + 8 <= G ;
  ep_DSA : sp0 <= 621800 \/ 622200 <= sp0 - 1024 ;
  ep_DSd : sp0 <= 0x97c00 \/ 0x97c00 + 8 <= sp0 - 1024
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
  rdn SEGS m (wa (8 * sc + 621800)) 8 = Some (word_to_le_bytes 8 (wa H)) ->
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
  rdn SEGS m (wa (8 * sc + 621800)) 8 = Some (word_to_le_bytes 8 (wa H)) ->
  (Z.lor avail freed <> 0 \/ (Z.lor avail freed = 0 /\ H = G)) ->
  exists R, msteps SEGS (mkst regs (wa 0x537e4) m rom) (mkst R (wa 0x53a58) (ee12_mem m G freed idx) rom)
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
  - destruct (run_sound SEGS 200 [] AXF_ee.scr_ee1 0x537e4 AXF_ee.sr_ee AXF_ee.kn_ee 45 _ _ _ E m rom regs AXF_ee.RES_ee1_ok HR HK) as (R & HR' & _ & Hms).
    { cbn [AXF_ee.RES_ee1 fst snd]. SCS. }
    exists R. split.
    + cbn [AXF_ee.RES_ee1 fst snd s_pc s_log] in Hms.
      lazymatch type of Hms with msteps _ _ (mkst _ ?PC ?M _) => replace (ee12_mem m G freed idx) with M; [exact Hms|] end.
      clear Hms HR'. cbn [mem_denot]. unfold ee12_mem. apply (f_equal3 wbytes); [reflexivity | |].
      * rewrite adenot_z. cbn [zeval edenot AXF_ee.e_G]. rewrite Z32. reflexivity.
      * rewrite zeval_sound. cbn [zeval edenot]. rewrite Z33, Z36. repeat dsc_mod. litmods. apply or_store4; assumption.
    + cbn [AXF_ee.RES_ee1 fst snd s_regs] in HR'. clear Hms. exit_post HR'.
  - destruct (run_sound SEGS 200 [] AXF_ee.scr_ee2 0x537e4 AXF_ee.sr_ee AXF_ee.kn_ee 45 _ _ _ E m rom regs AXF_ee.RES_ee2_ok HR HK) as (R & HR' & _ & Hms).
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
  rdn SEGS m (wa (8 * sc + 621800)) 8 = Some (word_to_le_bytes 8 (wa 0)) ->
  rdn SEGS m (wa (G + 0)) 8 = Some (word_to_le_bytes 8 (wa 0)) ->
  rdn SEGS m (wa (G + 8)) 8 = Some (word_to_le_bytes 8 (wa 0)) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS m (wa (G + 0 + d)) k = true) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (8 * sc + 621800 + d)) k = true) ->
  (G + 40 <= 8 * sc + 621800 \/ 8 * sc + 621800 + 8 <= G) ->
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
  rdn SEGS m (wa (8 * sc + 621800)) 8 = Some (word_to_le_bytes 8 (wa 0)) ->
  rdn SEGS m (wa (G + 0)) 8 = Some (word_to_le_bytes 8 (wa 0)) ->
  rdn SEGS m (wa (G + 8)) 8 = Some (word_to_le_bytes 8 (wa 0)) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS m (wa (G + 0 + d)) k = true) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (8 * sc + 621800 + d)) k = true) ->
  (G + 40 <= 8 * sc + 621800 \/ 8 * sc + 621800 + 8 <= G) ->
  Z.lor avail freed = 0 ->
  exists R, msteps SEGS (mkst regs (wa 0x537e4) m rom) (mkst R (wa 0x53a58) (ee3_mem m G sc freed idx) rom)
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
  destruct (run_sound SEGS 200 [] AXF_ee3.scr_pee3 0x537e4 AXF_ee3.sr_ee3 AXF_ee3.kn_ee3 45 _ _ _ E m rom regs AXF_ee3.RES_pee3_ok HR HK) as (R & HR' & _ & Hms).
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
  rdn SEGS m (wa (8 * sc + 621800)) 8 = Some (word_to_le_bytes 8 (wa H)) ->
  rdn SEGS m (wa (G + 0)) 8 = Some (word_to_le_bytes 8 (wa 0)) ->
  rdn SEGS m (wa (G + 8)) 8 = Some (word_to_le_bytes 8 (wa 0)) ->
  rdn SEGS m (wa (H + 0)) 8 = Some (word_to_le_bytes 8 (wa HP)) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS m (wa (G + 0 + d)) k = true) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (H + 0 + d)) k = true) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (HP + 8 + d)) k = true) ->
  H + 40 <= sp0 - 1024 -> HP + 40 <= sp0 - 1024 ->
  (G + 40 <= H \/ H + 40 <= G) -> (G + 40 <= HP \/ HP + 40 <= G) ->
  (H + 40 <= 0x97c00 \/ 0x97c00 + 8 <= H) -> (HP + 40 <= 0x97c00 \/ 0x97c00 + 8 <= HP) ->
  (H + 40 <= 8 * sc + 621800 \/ 8 * sc + 621800 + 8 <= H) -> (HP + 40 <= 8 * sc + 621800 \/ 8 * sc + 621800 + 8 <= HP) ->
  (G + 40 <= 8 * sc + 621800 \/ 8 * sc + 621800 + 8 <= G) ->
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
  rdn SEGS m (wa (8 * sc + 621800)) 8 = Some (word_to_le_bytes 8 (wa H)) ->
  rdn SEGS m (wa (G + 0)) 8 = Some (word_to_le_bytes 8 (wa 0)) ->
  rdn SEGS m (wa (G + 8)) 8 = Some (word_to_le_bytes 8 (wa 0)) ->
  rdn SEGS m (wa (H + 0)) 8 = Some (word_to_le_bytes 8 (wa HP)) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 16 -> store_ok SEGS m (wa (G + 0 + d)) k = true) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (H + 0 + d)) k = true) ->
  (forall d k, 0 <= d -> d + Z.of_nat k <= 8 -> store_ok SEGS m (wa (HP + 8 + d)) k = true) ->
  H + 40 <= sp0 - 1024 -> HP + 40 <= sp0 - 1024 ->
  (G + 40 <= H \/ H + 40 <= G) -> (G + 40 <= HP \/ HP + 40 <= G) ->
  (H + 40 <= 0x97c00 \/ 0x97c00 + 8 <= H) -> (HP + 40 <= 0x97c00 \/ 0x97c00 + 8 <= HP) ->
  (H + 40 <= 8 * sc + 621800 \/ 8 * sc + 621800 + 8 <= H) -> (HP + 40 <= 8 * sc + 621800 \/ 8 * sc + 621800 + 8 <= HP) ->
  (G + 40 <= 8 * sc + 621800 \/ 8 * sc + 621800 + 8 <= G) ->
  Z.lor avail freed = 0 -> H <> G ->
  exists R, msteps SEGS (mkst regs (wa 0x537e4) m rom) (mkst R (wa 0x53a58) (ee4_mem m G freed idx H HP) rom)
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
  destruct (run_sound SEGS 200 [] AXF_ee4.scr_pee4 0x537e4 AXF_ee4.sr_ee4 AXF_ee4.kn_ee4 46 _ _ _ E m rom regs AXF_ee4.RES_pee4_ok HR HK) as (R & HR' & _ & Hms).
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
