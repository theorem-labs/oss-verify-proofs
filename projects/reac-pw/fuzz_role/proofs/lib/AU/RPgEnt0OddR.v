(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgM3dFlt.v at 0312b0cd6c6c; hvl_core_step,
   hvl_hc_core, hvl_mid with its run / float-step / call transports, hvl_at_kept, hvl_base_at, the cut builders,
   hvl_soff, hvl_ge3 / hvl_le3 and hvl_half_words restated for image B over lib/AU/HPgSeg.v / HPgSegM.v and
   lib/AU/HPgM3dBaseU.v's cut CV (the write zone is [R - T_SEG_STK, R) and [R+0x88, R+0x90), s2 and s8 are not
   kept, no float register is written); the six block lemmas of image B's step from cut CV and its chain are new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgM3dCvU.v, with its module paths and module names changed; 264 of its 329 lines of code are new or changed and 1141 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgEnt0OddW.v at 111d25b4415f (its engine runs o_run1a .. o_run4 and their plumbing) for reac-pw/fuzz_rate's image A: module paths changed; the image is fuzz_rate.asan (images.Asan) in place of lib/A/Img0; the code is rate's 24 words 0x81b6c .. 0x81bcc; the shadow token's base is s2 (atom 18) in place of s7; the entry goes to s8 (x24) in place of s9; the copy's destination is s6 (x22) in place of s4; the last run is rate's lone `j` to G 0x8150c (no `mv s9,s8`); RPgSteps / RPgMem / RPgCfgChanges are lib/A/RtPgSteps.v, RtPgMem.v and lib/A/RtPgW7bBase.v's w7_kept_run / w7_same_io_wvb; AR_laws is the kernel theorem AR_laws_ok in place of a Section hypothesis. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgEnt0OddR.v at 21da95a5fcd3; image B (images.AsanUbsan): the code is image B's 29 words 0x81de0 .. 0x81e54; c is in a3 (x13); run 1a ends before the B-only UBSan trap test 0x81e0c with a0 = (c mod 14) << 3, a1 = 0x9be40 and a2 = ~0x9be40, and the new run 1t decides that test from closed-numeral facts and adds the table's address; the shadow token's base is s4 (atom 20); the entry goes to s6 (x22) and t1 is saved in s8 (x24); &ch is s2 (x18); the calls are the strlen wrapper 0x421ec and __asan_memcpy 0x518b8; the last run is `mv t1,s8; j` G 0x8160c; the kit is lib/AU/RtPgW7bBaseB.v (w7b_post) and lib/AU/RtPgStepsB.v; names o_ -> ob_. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgEnt0OddRB.v at cc5ce244897b for reac-pw/fuzz_role's image B (fuzz_role.asan-ubsan): module paths fuzz_rate -> fuzz_role, the segments lib/AU/Img0.v rsegs; the code is role B's 29 words 0x815e0 .. 0x81650 (the runs end at 0x8160c, 0x81618, 0x8162c, the strlen wrapper 0x41b60 with ra 0x8163c, checked_memcpy 0x5116c with ra 0x8164c, and G 0x80dc8); the table is 0x9a820 and its complement ~0x9a820; the shadow token's base is s11 (atom 27); t1 is saved in s4 (x20); the kit is lib/AU/RPgW7bBase.v (w7b_post) and lib/AU/RPgSteps.v. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; addresses measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): the engine runs of the ODD
   block of ent_build's case 0 (pod.h:247-248, `const char *o = odd_ch[c % 14]; memcpy(ch, o, strlen(o) + 1);`)
   from 0x815e0 to G = 0x80dc8, over the journal (no cut state). Proves no function (kind: segment lemma).

   THE CODE and how the walk cuts it (c in a3):
     1a 0x815e0 .. 0x81608  a1 := the constant 0x124924924924924a (`ld` of .rodata 0x10318), q := c / 14 (`mulhu`),
                            a2 := -14 q, a1 := 0x9a820 (`auipc; addi`), a0 := (c - 14 q) << 3 = 8 (c mod 14) (checked
                            on every c in [200, 256) by ob_all56), a2 := ~a1
     1t 0x8160c .. 0x81614  the UBSan pointer-overflow test of odd_ch + 8 (c mod 14) (`bgeu a2,a0,+8`, else `j`
                            0x82604, the trap), then a0 := a1 + a0, the table entry
     1b 0x81618 .. 0x81628  the shadow check of that table entry (`srli`, `add s11`, `lbu`, `beqz`, else `j` to the
                            error path 0x82858): one obligation of the token engine, range_addressable of the entry's
                            8 bytes, so the error path is never reached
     2  0x8162c .. 0x81638  s4 := t1, s6 := the entry (odd_ch[c mod 14], a cell of .data.rel.ro), a0 := s6, `jal`
        0x41b60             the strlen wrapper (RPgW7bCall.w7b_astrlen_realizes, w7b_strlen_at)
     3  0x8163c .. 0x81648  a2 := len + 1, a0 := s2 (= &ch = F + 0xa0), a1 := s6, `jal` checked_memcpy
        0x5116c             checked_memcpy (YG0d.v aintrin_realizes OCpy, RPgW7bKit.w7b_memcpy_at)
     4  0x8164c .. 0x81650  t1 := s4, `j` 0x80dc8
   Run 1 is cut at 0x8160c because the engine keeps no range for a `mulhu` result: run 1a computes a0 as a function
   of c, and run 1t starts from a fresh atom a0 with the closed bounds [0, 104] and a2 with the closed bound
   [~0x9a820, ~0x9a820], so the engine decides the trap test by computation. It is cut again at 0x81618 because the
   engine's shadow token matches only `(x >> 3) + s11`: run 1b starts from a fresh atom for the entry's address with
   the table's range and 8-alignment. Each run is an engine run (lib/Reusable/YCbq.v aj_run_to_tok) from a fresh
   symbolic state to the run's end pc, with RPgW7bBase.w7b_post as its post; lib/AU/RPgEnt0OddW.v chains them. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Tables.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgSteps RPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgW7bBase RPgEnt0OddB.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.


(* ---- the code: the 29 words 0x815e0 .. 0x81650 ---- *)
Definition OB_PC : Z := 0x815e0.
Definition ob_tbl : ctable := build_table rsegs OB_PC 29 TEmpty.
Lemma ob_tbl_ok : table_ok rsegs ob_tbl.
Proof. apply build_table_ok0. unfold OB_PC. lia. Qed.
(* the constant 0x124924924924924a at .rodata 0x10318 is 8 image bytes (its value: RPgEnt0OddB.ob_img_chk) *)
Lemma ob_k14_rom : rom_run_b 0x10318 8 = true.
Proof. vm_compute. reflexivity. Qed.
(* ~0x9a820, the left side of the trap test 0x8160c (`not a2,a1`) *)
Definition OB_NOT : Z := 18446744073708918751.
Lemma ob_not_eq : OB_NOT = 2 ^ 64 - 1 - OB_TBL.
Proof. reflexivity. Qed.

(* ---- a value of the engine that is a function of c, checked on every c in [200, 256) ---- *)
Lemma ob_all56 : forall f : Z -> Z,
forallb (fun i => f (200 + Z.of_nat i) =? 8 * ((200 + Z.of_nat i) mod 14)) (seq 0 56) = true ->
forall c, 200 <= c < 256 -> f c = 8 * (c mod 14).
Proof.
intros f H c Hc. rewrite forallb_forall in H.
specialize (H (Z.to_nat (c - 200)) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia.
replace (200 + (c - 200)) with c in H by lia. apply Z.eqb_eq. exact H.
Qed.
Ltac ob_refl56 c Hc :=
lazymatch goal with |- ?L = _ =>
  let f := eval pattern c in L in
  lazymatch f with ?g c => apply (ob_all56 g); [vm_compute; reflexivity | exact Hc] end end.
(* ---- the same for a function of m in [0, 14): the table entry ---- *)
Lemma ob_all14 : forall f : Z -> Z,
forallb (fun i => f (Z.of_nat i) =? OB_TBL + 8 * Z.of_nat i) (seq 0 14) = true ->
forall m, 0 <= m < 14 -> f m = OB_TBL + 8 * m.
Proof.
intros f H m Hm. rewrite forallb_forall in H.
specialize (H (Z.to_nat m) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia.
apply Z.eqb_eq. exact H.
Qed.
Ltac ob_refl14 m Hm :=
lazymatch goal with |- ?L = _ =>
  let f := eval pattern m in L in
  lazymatch f with ?g m => apply (ob_all14 g); [vm_compute; reflexivity | exact Hm] end end.

(* ---- engine plumbing ---- *)
(* the value of register r at a run's last state *)
Ltac ob_reg HS r :=
rewrite (st_ok_restrict_reg rsegs _ _ _ _ r HS);
lazymatch type of HS with st_ok _ ?Ev ?ssv _ =>
  let e := eval vm_compute in (sr_get (ss_regs ssv) r) in change (sr_get (ss_regs ssv) r) with e end.
(* a region list without a write window writes nothing *)
Ltac ob_kwr_ro :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; lia | ]); destruct Hr.
(* a closed value of the engine: a literal, or literals combined *)
Ltac ob_lit := first [reflexivity | (apply bv_eq; vm_compute; reflexivity)].

(* an atom below 32 of a run's last environment is the register it started as *)
Lemma ob_agree_atom : forall regs extra Ev n (r : bv 5), env_agree 32 (Ereg regs extra) Ev -> (n < 32)%nat ->
Z.of_nat n = bv_unsigned r -> sv_denot Ev (SOff n 0) = getr regs r.
Proof.
intros regs extra Ev n r [HA _] Hn Hr. apply bv_eq.
rewrite denot_SOff, (HA n Hn), (ew_Ereg_nat regs extra n r Hr), Z.add_0_r.
apply zcanon_id. pose proof (bv_unsigned_in_range _ (getr regs r)) as Hb. change (bv_modulus 64) with (2 ^ 64) in Hb.
unfold M64. lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.

(* ======================== run 1a: 0x815e0 -> 0x8160c ======================== *)
Definition ss_O1a : sstate :=
mkSS OB_PC sr_atoms [YP09.mkRegion None 0x10318 (0x10318 + 8) 0 0 [YP09.mkChunk 0x10318 (CImg 8)]] None
  (mkFacts [] [] []).

Lemma ob_run1a : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) c,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 13 = w64 c -> 200 <= c < 256 -> rom_view rsegs W memc ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 OB_PC) memc (seg_rom rsegs)) mdc)
(w7b_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k 0x8160c regs memc mdc [10; 11; 12]%bv (fun _ => False)
(fun regs2 _ => getr regs2 10 = w64 (8 * (c mod 14)) /\ getr regs2 11 = w64 OB_TBL /\ getr regs2 12 = w64 OB_NOT)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs c HJ H13 Hc HR.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof w7b_wx as Hwx. pose proof w7b_segs_low as Hsegs.
assert (E13 : ew (Ereg regs []) 13 = Z_to_bv 64 c) by (rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
assert (HS : st_ok rsegs (Ereg regs []) ss_O1a (restrict (w_H W) (mkst regs (Z_to_bv 64 OB_PC) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. apply img_region_ok_rom; [exact HR | lia | lia | lia | exact ob_k14_rom].
  - cbn. tauto.
  - split; [|split; exact I]. cbn. exact I. }
assert (SHOK : sh_ok rsegs W7B_Bx [] (Ereg regs []) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs []) (Ereg regs [])) by apply env_agree_refl.
aj_run_to_tok ob_tbl_ok HS HJ SHOK W7B_span 0x8160c.
- awr_ok_tac.
- eapply (w7b_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply w7b_same_io_wvb | | | exact HG | ].
  + eapply (w7b_regs_kept _ _ ms regs [] (w_H W) _ HS); [env_agree_chain HAE | vm_compute; reflexivity].
  + intros a Ha Hz. eapply (w7b_kept_run (fun _ => False) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr); [ob_kwr_ro | exact Ha | exact Hz].
  + split; [|split].
    * ob_reg HS (10%bv : bv 5). rewrite denot_lit_U. unfold w64. f_equal.
      lazymatch type of HS with st_ok _ ?Ev _ _ =>
        assert (E13' : ew Ev 13 = Z_to_bv 64 c)
          by (assert (HA' : env_agree 32 (Ereg regs []) Ev) by env_agree_chain HAE;
              try rewrite (proj1 HA' 13%nat ltac:(lia)); exact E13) end.
      rewrite !U_SAlu, ?U_SMd, ?U_SLit, (U_atom _ 13 c E13') by lia.
      ob_refl56 c Hc.
    * ob_reg HS (11%bv : bv 5). ob_lit.
    * ob_reg HS (12%bv : bv 5). ob_lit.
Qed.

(* ======================== run 1t: 0x8160c -> 0x81618 ========================
   a0 and a2 are fresh atoms with closed numeral bounds (a0 in [0, 104], a2 = ~0x9a820), so the engine decides the
   UBSan test `bgeu a2,a0` (taken: the `j` to the trap 0x82604 is never reached); then a0 := a1 + a0. *)
Definition ss_O1t : sstate :=
mkSS 0x8160c sr_atoms [] None
  (mkFacts [(10%nat, mkAF 0 104 0); (12%nat, mkAF 18446744073708918751 18446744073708918751 0)] [] []).

Lemma ob_run1t : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) m,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 10 = w64 (8 * m) -> 0 <= m < 14 -> getr regs 11 = w64 OB_TBL -> getr regs 12 = w64 OB_NOT ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 0x8160c) memc (seg_rom rsegs)) mdc)
(w7b_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k 0x81618 regs memc mdc [10]%bv (fun _ => False)
(fun regs2 _ => getr regs2 10 = w64 (OB_TBL + 8 * m))).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs m HJ H10 Hm H11 H12.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof w7b_wx as Hwx. pose proof w7b_segs_low as Hsegs.
assert (E10 : ew (Ereg regs []) 10 = Z_to_bv 64 (8 * m))
  by (rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew (Ereg regs []) 11 = Z_to_bv 64 OB_TBL)
  by (rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew (Ereg regs []) 12 = Z_to_bv 64 OB_NOT)
  by (rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (HS : st_ok rsegs (Ereg regs []) ss_O1t (restrict (w_H W) (mkst regs (Z_to_bv 64 0x8160c) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. exact I.
  - split; [|split; exact I].
    cbn [ss_O1t f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
    rewrite E10, E12. unfold OB_NOT. rewrite !unsigned_lit_small by lia.
    rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
assert (SHOK : sh_ok rsegs W7B_Bx [] (Ereg regs []) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs []) (Ereg regs [])) by apply env_agree_refl.
aj_run_to_tok ob_tbl_ok HS HJ SHOK W7B_span 0x81618.
- awr_ok_tac.
- eapply (w7b_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply w7b_same_io_wvb | | | exact HG | ].
  + eapply (w7b_regs_kept _ _ ms regs [] (w_H W) _ HS); [env_agree_chain HAE | vm_compute; reflexivity].
  + intros a Ha Hz. eapply (w7b_kept_run (fun _ => False) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr); [ob_kwr_ro | exact Ha | exact Hz].
  + ob_reg HS (10%bv : bv 5). rewrite denot_lit_U. unfold w64. f_equal.
    lazymatch type of HS with st_ok _ ?Ev _ _ =>
      assert (HA' : env_agree 32 (Ereg regs []) Ev) by env_agree_chain HAE;
      assert (E10' : ew Ev 10 = Z_to_bv 64 (8 * m)) by (try rewrite (proj1 HA' 10%nat ltac:(lia)); exact E10);
      assert (E11' : ew Ev 11 = Z_to_bv 64 OB_TBL) by (try rewrite (proj1 HA' 11%nat ltac:(lia)); exact E11) end.
    rewrite ?U_SAlu, ?U_SLit, (U_atom _ 10 (8 * m) E10'), (U_atom _ 11 OB_TBL E11') by (unfold OB_TBL; lia).
    ob_refl14 m Hm.
Qed.

(* ======================== run 1b: 0x81618 -> 0x8162c ========================
   a0 is a fresh atom with the table's range and 8-alignment, so the engine's shadow token matches `(a0 >> 3) + s11`
   at the `lbu` and leaves the entry's range_addressable as the one obligation (so the error path 0x82858 is never
   reached). *)
Definition ss_O1b : sstate :=
mkSS 0x81618 sr_atoms [] None
  (mkFacts [(27%nat, mkAF 0x7fff8000 0x7fff8000 0); (10%nat, mkAF 0x9a820 0x9a888 3)] [] []).

Lemma ob_run1b : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) m,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 27 = w64 SHADOW_OFF -> getr regs 10 = w64 (OB_TBL + 8 * m) -> 0 <= m < 14 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (OB_TBL + 8 * m) 8 ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 0x81618) memc (seg_rom rsegs)) mdc)
(w7b_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k 0x8162c regs memc mdc [11]%bv (fun _ => False)
(fun _ _ => True)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs m HJ H27 H10 Hm HRA.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof w7b_wx as Hwx. pose proof w7b_segs_low as Hsegs.
assert (E27 : ew (Ereg regs []) 27 = getr regs 27) by exact (ew_Ereg_nat regs _ 27 27%bv eq_refl).
assert (E10 : ew (Ereg regs []) 10 = Z_to_bv 64 (OB_TBL + 8 * m))
  by (rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (Hal : (OB_TBL + 8 * m) mod 8 = 0).
{ replace (OB_TBL + 8 * m) with ((79108 + m) * 8) by (unfold OB_TBL; lia). apply Z.mod_mul. lia. }
assert (HS : st_ok rsegs (Ereg regs []) ss_O1b (restrict (w_H W) (mkst regs (Z_to_bv 64 0x81618) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. exact I.
  - split; [|split; exact I].
    cbn [ss_O1b f_atoms atoms_ok]. unfold afact_ok; cbn [af_lo af_hi af_al2].
    rewrite E27, E10, H27. unfold w64. rewrite !unsigned_lit_small by (unfold SHADOW_OFF, OB_TBL; lia).
    change (2 ^ 0) with 1. change (2 ^ 3) with 8. rewrite !Z.mod_1_r. rewrite Hal.
    unfold SHADOW_OFF, OB_TBL. repeat split; lia. }
assert (SHOK : sh_ok rsegs W7B_Bx [] (Ereg regs []) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs []) (Ereg regs [])) by apply env_agree_refl.
aj_run_to_tok ob_tbl_ok HS HJ SHOK W7B_span 0x8162c.
- (* the shadow obligation of the table entry *)
  cbn [ms_mem mkst]. unfold W7B_Bx.
  rewrite (U_atom _ 27 SHADOW_OFF) by first [rewrite E27, H27; reflexivity | unfold SHADOW_OFF; lia].
  rewrite (U_atom _ 10 (OB_TBL + 8 * m) E10) by (unfold OB_TBL; lia).
  exact HRA.
- awr_ok_tac.
- eapply (w7b_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply w7b_same_io_wvb | | | exact HG | ].
  + eapply (w7b_regs_kept _ _ ms regs [] (w_H W) _ HS); [env_agree_chain HAE | vm_compute; reflexivity].
  + intros a Ha Hz. eapply (w7b_kept_run (fun _ => False) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr); [ob_kwr_ro | exact Ha | exact Hz].
  + exact I.
Qed.

(* ======================== run 2: 0x8162c -> 0x41b60 (the strlen wrapper) ======================== *)
Definition ss_O2 : sstate :=
mkSS 0x8162c sr_atoms [YP09.mkRegion (Some 10%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))]] None
  (mkFacts [] [] []).

Lemma ob_run2 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) a o,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 10 = w64 a -> 0 <= a -> a + 8 <= 2 ^ 64 -> 0 <= o < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) a 8 o ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 0x8162c) memc (seg_rom rsegs)) mdc)
(w7b_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k W7B_STRLEN regs memc mdc [1; 10; 20; 22]%bv (fun _ => False)
(fun regs2 _ => getr regs2 22 = w64 o /\ getr regs2 10 = w64 o /\ getr regs2 1 = w64 0x8163c /\
  getr regs2 20 = getr regs 6)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs a o HJ H10 Ha0 Ha8 Ho Hval.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof w7b_wx as Hwx. pose proof w7b_segs_low as Hsegs.
assert (B10 : bv_unsigned (ew (Ereg regs [Z_to_bv 64 o]) 10) = a)
  by (rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), H10; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew (Ereg regs [Z_to_bv 64 o]) 32 = Z_to_bv 64 o) by exact (ew_Ereg_extra regs [Z_to_bv 64 o] 0).
assert (D32 : sv_denot (Ereg regs [Z_to_bv 64 o]) (SOff 32 0) = Z_to_bv 64 o).
{ apply bv_eq. rewrite denot_SOff, E32, Z.add_0_r, !unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia. }
assert (HS : st_ok rsegs (Ereg regs [Z_to_bv 64 o]) ss_O2 (restrict (w_H W) (mkst regs (Z_to_bv 64 0x8162c) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (rm_ro_region rsegs _ (w_H W) memc 10%nat a 0 8); [exact B10 | lia | lia |].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs _ _ a 0 8 (SOff 32 0) o);
      [exact D32 | change (8 * Z.of_N 8) with 64; lia | cbn; lia | rewrite Z.add_0_r; exact Hval].
  - cbn. tauto.
  - split; [|split; exact I]. cbn. exact I. }
assert (SHOK : sh_ok rsegs W7B_Bx [] (Ereg regs [Z_to_bv 64 o]) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 o]) (Ereg regs [Z_to_bv 64 o])) by apply env_agree_refl.
aj_run_to_tok ob_tbl_ok HS HJ SHOK W7B_span 0x41b60.
- awr_ok_tac.
- eapply (w7b_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply w7b_same_io_wvb | | | exact HG | ].
  + eapply (w7b_regs_kept _ _ ms regs [Z_to_bv 64 o] (w_H W) _ HS); [env_agree_chain HAE | vm_compute; reflexivity].
  + intros a' Ha Hz. eapply (w7b_kept_run (fun _ => False) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr); [ob_kwr_ro | exact Ha | exact Hz].
  + lazymatch type of HS with st_ok _ ?Ev _ _ =>
      assert (HA' : env_agree 32 (Ereg regs [Z_to_bv 64 o]) Ev) by env_agree_chain HAE end.
    split; [|split; [|split]].
    * ob_reg HS (22%bv : bv 5). exact D32.
    * ob_reg HS (10%bv : bv 5). exact D32.
    * ob_reg HS (1%bv : bv 5). reflexivity.
    * ob_reg HS (20%bv : bv 5). exact (ob_agree_atom regs [Z_to_bv 64 o] _ 6 6%bv HA' ltac:(lia) eq_refl).
Qed.

(* ======================== run 3: 0x8163c -> 0x5116c (checked_memcpy) ======================== *)
Definition ss_Opc (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).

Lemma ob_run3 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) n,
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 10 = w64 n -> 0 <= n -> n + 1 < 2 ^ 64 ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 0x8163c) memc (seg_rom rsegs)) mdc)
(w7b_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k W7B_MEMCPY regs memc mdc [1; 10; 11; 12]%bv (fun _ => False)
(fun regs2 _ => getr regs2 12 = w64 (n + 1) /\ getr regs2 10 = getr regs 18 /\ getr regs2 11 = getr regs 22 /\
  getr regs2 1 = w64 0x8164c)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs n HJ H10 Hn0 Hn1.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof w7b_wx as Hwx. pose proof w7b_segs_low as Hsegs.
assert (HS : st_ok rsegs (Ereg regs []) (ss_Opc 0x8163c) (restrict (w_H W) (mkst regs (Z_to_bv 64 0x8163c) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn. tauto.
  - split; [|split; exact I]. cbn. exact I. }
assert (SHOK : sh_ok rsegs W7B_Bx [] (Ereg regs []) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs []) (Ereg regs [])) by apply env_agree_refl.
aj_run_to_tok ob_tbl_ok HS HJ SHOK W7B_span 0x5116c.
- awr_ok_tac.
- eapply (w7b_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply w7b_same_io_wvb | | | exact HG | ].
  + eapply (w7b_regs_kept _ _ ms regs [] (w_H W) _ HS); [env_agree_chain HAE | vm_compute; reflexivity].
  + intros a' Ha Hz. eapply (w7b_kept_run (fun _ => False) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr); [ob_kwr_ro | exact Ha | exact Hz].
  + lazymatch type of HS with st_ok _ ?Ev _ _ =>
      assert (HA' : env_agree 32 (Ereg regs []) Ev) by env_agree_chain HAE end.
    split; [|split; [|split]].
    * ob_reg HS (12%bv : bv 5). cbn [sv_denot].
      try rewrite (proj1 HA' 10%nat ltac:(lia)). rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), H10.
      unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    * ob_reg HS (10%bv : bv 5). exact (ob_agree_atom regs [] _ 18 18%bv HA' ltac:(lia) eq_refl).
    * ob_reg HS (11%bv : bv 5). exact (ob_agree_atom regs [] _ 22 22%bv HA' ltac:(lia) eq_refl).
    * ob_reg HS (1%bv : bv 5). reflexivity.
Qed.

(* ======================== run 4: 0x8164c -> G 0x80dc8 ======================== *)
Lemma ob_run4 : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 0x8164c) memc (seg_rom rsegs)) mdc)
(w7b_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k 0x80dc8 regs memc mdc [6]%bv (fun _ => False)
(fun regs2 _ => getr regs2 6 = getr regs 20)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof w7b_wx as Hwx. pose proof w7b_segs_low as Hsegs.
assert (HS : st_ok rsegs (Ereg regs []) (ss_Opc 0x8164c) (restrict (w_H W) (mkst regs (Z_to_bv 64 0x8164c) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn. tauto.
  - split; [|split; exact I]. cbn. exact I. }
assert (SHOK : sh_ok rsegs W7B_Bx [] (Ereg regs []) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs []) (Ereg regs [])) by apply env_agree_refl.
aj_run_to_tok ob_tbl_ok HS HJ SHOK W7B_span 0x80dc8.
- awr_ok_tac.
- eapply (w7b_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply w7b_same_io_wvb | | | exact HG | ].
  + eapply (w7b_regs_kept _ _ ms regs [] (w_H W) _ HS); [env_agree_chain HAE | vm_compute; reflexivity].
  + intros a' Ha Hz. eapply (w7b_kept_run (fun _ => False) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr); [ob_kwr_ro | exact Ha | exact Hz].
  + lazymatch type of HS with st_ok _ ?Ev _ _ =>
      assert (HA' : env_agree 32 (Ereg regs []) Ev) by env_agree_chain HAE end.
    ob_reg HS (6%bv : bv 5). exact (ob_agree_atom regs [] _ 20 20%bv HA' ltac:(lia) eq_refl).
Qed.
End d.
End b.

Print Assumptions ob_run1a.
Print Assumptions ob_run1t.
Print Assumptions ob_run1b.
Print Assumptions ob_run2.
Print Assumptions ob_run3.
Print Assumptions ob_run4.
