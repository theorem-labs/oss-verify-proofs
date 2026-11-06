(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_up.v, with its module paths and module names changed; 264 of its 309 lines of code are new or changed and 2644 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/fuzz_recv_cp.v, with its module names changed; 298 of its 337 lines of code are new or changed and 270 lines of the source are left out. *)
(* text_of on image A: THE TABLE ARM of its walk, from text_ofDefs.v's TABLE CUT (+0x144) to the return:
     +0x144 .. +0x184  i := (a1 & 0xff) mod 11 (multiply by 0x75, shifts, subw), a0 := texts + 8 i: the PLAIN
                       engine; with the cut's a1 < 128 the address is computed for each of the 128 selectors
                       (to_T_all)
     +0x188 .. +0x194  the check of texts + 8 i (8-byte load; its shadow entry from the table's range_addressable)
     +0x198            s3 := texts[i]; j +0x270; a0 := s3; the seven restores, the pop, `ret` (the TOKEN engine,
                       restarted at +0x188 from the machine state)
   and the Post's table arm (own = 0) by LinkWalk.v-style apost_leaf_app (LinkWalkNoWrite.v).
   Section hypotheses: LAWS, LV, MTL (the image instance's and the meter's facts), TO_AMR (the cursor and *own are
   app memory: the per-piece premise text_of's walk carries until text_of_c.v states it).
   Proves no function (kind: segment lemma of text_of's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YG0p YG08 YGwildCount.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC81 YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkNoWrite LinkWalkSide LinkWalkAlloc text_buf_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMallocDepot.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalk link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkPi LinkWalkSide LinkWalkNoWrite LinkWalkLeaf.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import text_of_c text_ofDefs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* a0 at +0x188 as the engine computes it from the cut (atom 11 = a1, atom 260 = A_OBJ 19 = texts) *)
Definition to_a0 : sv := SAlu ALU_ADD (SOff 260 0) (SAlu ALU_SLL (SAlu ALU_AND (SAluw ALU_SUB (SOff 11 0) (SMd M_MUL (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_SLL (SAluw ALU_SUB (SOff 11 0) (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_AND (SOff 11 0) (SLit 255)) (SLit 117)) (SLit 8))) (SLit 56)) (SLit 57)) (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_AND (SOff 11 0) (SLit 255)) (SLit 117)) (SLit 8))) (SLit 3)) (SLit 11))) (SLit 255)) (SLit 3)).
(* the same term with a1 and texts as literals *)
Definition to_T (n : Z) : sv := SAlu ALU_ADD (SLit LA_TEXTS) (SAlu ALU_SLL (SAlu ALU_AND (SAluw ALU_SUB (SLit n) (SMd M_MUL (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_SLL (SAluw ALU_SUB (SLit n) (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_AND (SLit n) (SLit 255)) (SLit 117)) (SLit 8))) (SLit 56)) (SLit 57)) (SAlu ALU_SRL (SMd M_MUL (SAlu ALU_AND (SLit n) (SLit 255)) (SLit 117)) (SLit 8))) (SLit 3)) (SLit 11))) (SLit 255)) (SLit 3)).

Lemma to_T_all : forall E, forallb (fun k => Z.eqb (bv_unsigned (sv_denot E (to_T (Z.of_nat k))))
  (LA_TEXTS + 8 * (Z.of_nat k mod 11))) (seq 0 128) = true.
Proof. intros E. vm_compute. reflexivity. Qed.

Lemma to_T_val : forall E n, 0 <= n < 128 -> bv_unsigned (sv_denot E (to_T n)) = LA_TEXTS + 8 * (n mod 11).
Proof.
  intros E n Hn. pose proof (to_T_all E) as H.
  apply (proj1 (forallb_forall _ _)) with (x := Z.to_nat n) in H; [|apply in_seq; lia].
  rewrite Z2Nat.id in H by lia. apply Z.eqb_eq in H. exact H.
Qed.

Lemma to_a0_T : forall E n, ew E 11 = Z_to_bv 64 n -> ew E 260 = Z_to_bv 64 LA_TEXTS ->
  sv_denot E to_a0 = sv_denot E (to_T n).
Proof.
  intros E n H11 H260. unfold to_a0, to_T. cbn [sv_denot]. rewrite H11, H260.
  rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* the state at +0x188: a0 = atom 10 (texts + 8 i), x20 = the shadow base (atom 32), the table word (atom 33) and the
   seven saves (atoms 34 .. 40, in TO_SAVED's order at sp' + 56 - 8 j) *)
Definition to_stk7 : YP09.region := YP09.mkRegion (Some 2%nat) 8 64 0 0
  [YP09.mkChunk 56 (CVal 8 (SOff 34 0)); YP09.mkChunk 48 (CVal 8 (SOff 35 0)); YP09.mkChunk 40 (CVal 8 (SOff 36 0));
   YP09.mkChunk 32 (CVal 8 (SOff 37 0)); YP09.mkChunk 24 (CVal 8 (SOff 38 0)); YP09.mkChunk 16 (CVal 8 (SOff 39 0));
   YP09.mkChunk 8 (CVal 8 (SOff 40 0))].
Definition to_tw : YP09.region := YP09.mkRegion (Some 10%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))].
Definition to_ss188 : sstate := mkSS (AF_text_of + 0x188) sr_atoms [to_stk7; to_tw] None
  (mkFacts [(10%nat, mkAF LA_TEXTS (LA_TEXTS + 80) 3); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] []).
Definition to_Bx : sv := SOff 32 0.
Definition to_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition to_xs (q : Z) (regs : bvmap 5 word) : list word :=
  Z_to_bv 64 SHADOW_OFF :: Z_to_bv 64 q :: map (fun r => getr regs (Z_to_bv 5 r)) TO_SAVED.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.

Lemma to_ms_eta : forall ms : machine_state, ms_fregs ms = fp_regs -> ms_svc_pending ms = None ->
  ms_resv ms = None -> ms_fcsr ms = fp_csr -> ms = mkst (ms_regs ms) (ms_pc_val ms) (ms_mem ms) (ms_rom ms).
Proof. intros [] H1 H2 H3 H4; cbn in *; subst; reflexivity. Qed.

Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Notation VAL := (@pa_val _ link_listing PI).
#[local] Notation BASE := (@pa_val _ link_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Variable MT : ameter_ops.
Variable CTX : list (list Z).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis LV : LinkVals.
Hypothesis MTL : ameter_laws MT.
(* the cursor and *own are app memory (the walk's per-piece premise, until text_of_c.v's Pre states it) *)
Hypothesis TO_AMR : forall cx, to_pre SK B MT CTX cx -> amem_range (to_p cx) 16 /\ amem_range (to_o cx) 8.

(* one instrumented check's shadow entry, with the shadow base in atom 32 *)
Lemma to_shent_ok : forall E (H : word -> bool) (m : word -> option byte) (nn : nat) x len,
  ew E 32 = Z_to_bv 64 SHADOW_OFF -> ew E nn = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> 0 <= len ->
  (forall a, x <= a < x + len -> a < kLowMemEnd \/ kHighMemBeg <= a) ->
  range_addressable (aview SEGS H m) SHADOW_OFF x len ->
  sh_ok SEGS to_Bx [mkSHE nn 0 len] E (mrestrict H m).
Proof.
  intros E H m nn x len E32 Ex Hx Hl Happ HR. unfold sh_ok. apply Forall_cons; [|apply Forall_nil].
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  assert (HB : U E to_Bx = SHADOW_OFF) by (unfold to_Bx; rewrite (U_atom E 32 SHADOW_OFF E32) by (unfold SHADOW_OFF; lia); reflexivity).
  assert (Hq : U E (SOff nn 0) = x) by (apply U_atom; [exact Ex | lia]).
  rewrite HB, Hq. split.
  - rewrite Z.add_0_r, Z.sub_0_r. rewrite <- (aview_rd_of SEGS). exact HR.
  - intros a Ha. rewrite Z.min_l, Z.max_r in Ha by lia. destruct (Happ a ltac:(lia)) as [Ha' | Ha'];
      unfold SHADOW_OFF in *; lia.
Qed.

Theorem to_table : to_table_obl SK B MT CTX.
Proof.
  unfold to_table_obl, to_from. intros cx ms3 md3 HPX HGI.
  pose proof HPX as (HPRE & HRD & Hlive & Hmo & Hch & Hctx & Hled & HP).
  destruct HPRE as (HJ & HGok & HROD & Hraw & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hside & Hajw & Hro).
  destruct (TO_AMR cx HPX) as (AMp & AMo).
  unfold to_gi_table in HGI. cbv zeta in HGI.
  destruct HGI as (Hpc & Hrv & Hsv & Hrom & Hfr & Hfc & HJ3 & Hfd & Hfs & R2 & R8 & R20 & (b & R11 & Hb) & RUT & RSV
    & HUN & HPR & HPW & HCUR & HABP & HOWN & HABO & HRAT & HTAB).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof pa_B_ok as (HB0' & HB1' & HB2').
  assert (HK : TEXT_OF_AK = 16448) by reflexivity.
  destruct (aj_gx_unpack SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (to_regs cx) TEXT_OF_AK HJ
    ltac:(lia) Hal16 Hwlo Hwhi) as (_ & _ & _ & _ & HSTK & HXO & _ & _ & _ & _ & Hceil & H47).
  pose proof (proj1 alloc_ceiling_val) as HCE.
  assert (Hsp64 : 0 <= to_sp cx < 2 ^ 64) by (unfold to_sp, spZ; apply getr_rng).
  set (regs := to_regs cx) in *. set (W := to_W cx) in *. set (R := ms_regs ms3) in *.
  set (sp := to_sp cx) in *.
  assert (Esp : sp = spZ regs) by reflexivity.
  (* ---- +0x144 .. +0x184: the PLAIN engine from the cut's machine state ---- *)
  assert (Hms3 : restrict (w_H W) ms3 =
     mkst R (Z_to_bv 64 (BASE + TO_CUT_TABLE)) (mrestrict (w_H W) (ms_mem ms3)) (seg_rom SEGS)).
  { rewrite (to_ms_eta ms3 Hfr Hsv Hrv Hfc) at 1. rewrite Hpc, Hrom. rewrite restrict_mkst_fx. reflexivity. }
  remember (Eimg (Ereg R [])) as E1 eqn:HE1.
  assert (HEI1 : img_env VAL A_LIM E1) by (subst E1; apply Eimg_env).
  assert (ER1 : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> (n < A_TEXT)%nat -> ew E1 n = getr R r)
    by (intros n r Hr Hn; subst E1; rewrite Eimg_low by exact Hn; exact (ew_Ereg_nat _ _ n r Hr)).
  assert (HRO1 : regs_ok E1 sr_atoms R) by (subst E1; apply regs_ok_Eimg_Ereg).
  clear HE1.
  assert (HS : st_ok_pi SEGS VAL E1 (mkSS TO_CUT_TABLE sr_atoms [] None (mkFacts [] [] [])) (restrict (w_H W) ms3)).
  { rewrite Hms3. apply pa_entry_st_ok_full.
    - exact HRO1.
    - vm_compute. reflexivity.
    - apply Forall_nil.
    - cbn [pairwise_disjoint all_disjoint]. tauto.
    - split; [exact I | split; exact I]. }
  pose (RUNPT := paj_run_to_plain_x SK B LAWS (to_G cx) HGok (to_XO cx) (to_OUT cx)).
  lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx (restrict (w_H ?Wx) ?msx) =>
    let r := eval vm_compute in (sym_run_toN_pi link_tpi FUEL (AF_text_of + 0x188) ssx) in
    lazymatch r with (?ssf, ?stf) =>
      let Hrun := fresh "Hrun" in
      assert (Hrun : sym_run_toN_pi link_tpi FUEL (AF_text_of + 0x188) ssx = (ssf, stf)) by (vm_compute; reflexivity);
      eapply (RUNPT Wx FUEL (AF_text_of + 0x188) Ev ssx ssf stf msx _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI1 HS Hrun I HJ3);
      [clear Hrun | clear Hrun HS HJ3]
    end
  end.
  { cbn [ss_mem]. apply awr_ok_x_nil. }
  intros ms4 mat4 HS4 HJ4 HF4 HFr4 HG4. cbn [ms_mem mkst] in HF4, HFr4, HG4, HJ4.
  assert (Hmem4 : ms_mem ms4 = ms_mem ms3).
  { apply functional_extensionality. intros x. apply HF4. cbn [ss_mem]. intros (r0 & Hin & _). destruct Hin. }
  assert (Hms4 : ms4 = mkst (ms_regs ms4) (Z_to_bv 64 (BASE + (AF_text_of + 0x188))) (ms_mem ms4) (seg_rom SEGS))
    by exact (st_ok_pi_restrict_mkst (w_H W) _ _ _ HS4 eq_refl).
  prreg_raw HS4 (10%bv : bv 5) Q10. cbn [ms_regs restrict mkst] in Q10.
  assert (A10 : getr (ms_regs ms4) 10 = sv_denot E1 to_a0) by exact Q10.
  clear Q10.
  prreg HS4 (2%bv : bv 5) Q2. prreg HS4 (3%bv : bv 5) Q3. prreg HS4 (4%bv : bv 5) Q4. prreg HS4 (20%bv : bv 5) Q20.
  prreg HS4 (22%bv : bv 5) Q22. prreg HS4 (23%bv : bv 5) Q23. prreg HS4 (24%bv : bv 5) Q24.
  prreg HS4 (25%bv : bv 5) Q25. prreg HS4 (26%bv : bv 5) Q26. prreg HS4 (27%bv : bv 5) Q27.
  rewrite (ER1 2%nat 2%bv eq_refl ltac:(unfold A_TEXT; lia)) in Q2.
  rewrite (ER1 3%nat 3%bv eq_refl ltac:(unfold A_TEXT; lia)) in Q3.
  rewrite (ER1 4%nat 4%bv eq_refl ltac:(unfold A_TEXT; lia)) in Q4.
  rewrite (ER1 20%nat 20%bv eq_refl ltac:(unfold A_TEXT; lia)) in Q20.
  rewrite (ER1 22%nat 22%bv eq_refl ltac:(unfold A_TEXT; lia)) in Q22.
  rewrite (ER1 23%nat 23%bv eq_refl ltac:(unfold A_TEXT; lia)) in Q23.
  rewrite (ER1 24%nat 24%bv eq_refl ltac:(unfold A_TEXT; lia)) in Q24.
  rewrite (ER1 25%nat 25%bv eq_refl ltac:(unfold A_TEXT; lia)) in Q25.
  rewrite (ER1 26%nat 26%bv eq_refl ltac:(unfold A_TEXT; lia)) in Q26.
  rewrite (ER1 27%nat 27%bv eq_refl ltac:(unfold A_TEXT; lia)) in Q27.
  (* the address texts + 8 i *)
  assert (H11 : ew E1 11 = Z_to_bv 64 b) by (rewrite (ER1 11%nat 11%bv eq_refl ltac:(unfold A_TEXT; lia)); exact R11).
  assert (H260 : ew E1 260 = Z_to_bv 64 LA_TEXTS).
  { rewrite (img_env_atomP E1 260 HEI1 ltac:(unfold A_TEXT, A_LIM; lia)). change 260%nat with (A_OBJ 19).
    rewrite (lv_obj LV 19 ltac:(vm_compute; lia)). reflexivity. }
  set (i := b mod 11).
  assert (Hi : 0 <= i < 11) by (unfold i; apply Z.mod_pos_bound; lia).
  assert (A10v : bv_unsigned (getr (ms_regs ms4) 10) = LA_TEXTS + 8 * i)
    by (rewrite A10, (to_a0_T E1 b H11 H260); apply to_T_val; exact Hb).
  (* ---- +0x188 .. +0x294: the TOKEN engine from the machine state ---- *)
  destruct (HTAB i ltac:(unfold TEXTS_N; lia)) as (q & s & Hq0 & Hq3 & Hq64 & Hcs & Hl320 & Hro0).
  set (xs := to_xs q regs).
  remember (Eimg (Ereg (ms_regs ms4) xs)) as E2 eqn:HE2.
  assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
  assert (ER2 : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> (n < A_TEXT)%nat ->
            ew E2 n = getr (ms_regs ms4) r)
    by (intros n r Hr Hn; subst E2; rewrite Eimg_low by exact Hn; exact (ew_Ereg_nat _ _ n r Hr)).
  assert (EX2 : forall j, (j < 9)%nat -> ew E2 (32 + j) = nth j xs (Z_to_bv 64 0))
    by (intros j Hj; subst E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ xs j)).
  assert (HRO2 : regs_ok E2 sr_atoms (ms_regs ms4)) by (subst E2; apply regs_ok_Eimg_Ereg).
  clear HE2.
  assert (Hsp' : 0 <= sp - 64 < 2 ^ 64) by (unfold TEXT_OF_AK, TEXT_OF_AFRAME in *; lia).
  assert (U2 : bv_unsigned (ew E2 2) = sp - 64).
  { rewrite (ER2 2%nat 2%bv eq_refl ltac:(unfold A_TEXT; lia)), Q2, R2. unfold TO_FRAME. apply unsigned_lit_small. lia. }
  assert (U10 : bv_unsigned (ew E2 10) = LA_TEXTS + 8 * i)
    by (rewrite (ER2 10%nat 10%bv eq_refl ltac:(unfold A_TEXT; lia)); exact A10v).
  assert (E10 : ew E2 10 = Z_to_bv 64 (LA_TEXTS + 8 * i)) by (rewrite <- U10; symmetry; apply Z_to_bv_bv_unsigned).
  assert (E32 : ew E2 32 = Z_to_bv 64 SHADOW_OFF) by exact (EX2 0%nat ltac:(lia)).
  assert (E33 : ew E2 33 = Z_to_bv 64 q) by exact (EX2 1%nat ltac:(lia)).
  assert (U32 : bv_unsigned (ew E2 32) = SHADOW_OFF) by (rewrite E32; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (CH : forall (j : nat) off, (j < 7)%nat -> off = 56 - 8 * Z.of_nat j ->
            YP09.chunk_ok SEGS E2 (mrestrict (w_H W) (ms_mem ms4)) (sp - 64)
              (YP09.mkChunk off (CVal 8 (SOff (34 + j) 0)))).
  { intros j off Hj Hoff.
    pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 (nth j TO_SAVED 0)))) as Hr.
    change (bv_modulus 64) with (2 ^ 64) in Hr.
    apply (chunk_ok_val SEGS E2 _ (sp - 64) off 8 (SOff (34 + j) 0)
             (bv_unsigned (getr regs (Z_to_bv 5 (nth j TO_SAVED 0))))).
    - cbn [sv_denot]. replace (34 + j)%nat with (32 + (2 + j))%nat by lia.
      rewrite (EX2 (2 + j)%nat ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite Z_to_bv_bv_unsigned.
      destruct j as [|[|[|[|[|[|[|j]]]]]]]; [reflexivity.. | lia].
    - change (8 * Z.of_N 8) with 64. exact Hr.
    - cbn. lia.
    - apply (val_mem_of_rdword SEGS). rewrite Hmem4.
      replace (sp - 64 + off) with (sp - 8 - 8 * Z.of_nat j) by lia. exact (RSV j Hj). }
  assert (HS5 : st_ok_pi SEGS VAL E2 to_ss188
      (restrict (w_H W) (mkst (ms_regs ms4) (Z_to_bv 64 (BASE + (AF_text_of + 0x188))) (ms_mem ms4) (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - exact HRO2.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; unfold region_ok, to_stk7, to_tw;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]; rewrite ?U2, ?U10.
      + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        repeat apply Forall_cons; try apply Forall_nil.
        * exact (CH 0%nat 56 ltac:(lia) ltac:(reflexivity)).
        * exact (CH 1%nat 48 ltac:(lia) ltac:(reflexivity)).
        * exact (CH 2%nat 40 ltac:(lia) ltac:(reflexivity)).
        * exact (CH 3%nat 32 ltac:(lia) ltac:(reflexivity)).
        * exact (CH 4%nat 24 ltac:(lia) ltac:(reflexivity)).
        * exact (CH 5%nat 16 ltac:(lia) ltac:(reflexivity)).
        * exact (CH 6%nat 8 ltac:(lia) ltac:(reflexivity)).
      + split; [unfold LA_TEXTS; lia|]. split; [unfold LA_TEXTS; lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E2 _ (LA_TEXTS + 8 * i) 0 8 (SOff 33 0) q).
        * cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
        * change (8 * Z.of_N 8) with 64. lia.
        * cbn. lia.
        * rewrite Z.add_0_r, Hmem4. exact Hq3.
    - apply pairwise_disjoint_of_extents. unfold to_stk7, to_tw, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U10.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold LA_TEXTS. repeat split; lia.
    - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U10, U32. change (2 ^ 3) with 8. rewrite Z.pow_0_r, Z.mod_1_r. unfold LA_TEXTS.
      repeat split; lia. }
  clear HS4.
  pose proof (ast_ok_pi_set_reg_fp E2 _ _ (20%bv : bv 5) (SOff 32 0) HS5 ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned, Q20, R20; reflexivity))
    as HS6.
  clear HS5.
  assert (SHOK : sh_ok SEGS to_Bx [mkSHE 10 0 8] E2 (mrestrict (w_H W) (ms_mem ms4))).
  { apply (to_shent_ok E2 (w_H W) (ms_mem ms4) 10 (LA_TEXTS + 8 * i) 8 E32 E10).
    - unfold LA_TEXTS. lia.
    - lia.
    - intros a Ha. left. unfold LA_TEXTS, kLowMemEnd in *. lia.
    - rewrite Hmem4. intros x Hx. apply HRAT. unfold TEXTS_N in *. lia. }
  rewrite Hms4.
  pose (RUN := paj_run_x SK B LAWS (to_G cx) HGok (to_XO cx) (to_OUT cx)).
  paj_run_tok RUN HS6 HJ4 SHOK to_span.
  { unfold to_ss188, to_stk7, to_tw. cbn [ss_mem]. apply awr_ok_x_cons;
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; lia
      | apply awr_ok_x_cons; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val]; intros a Ha; lia | apply awr_ok_x_nil]]. }
  lazymatch type of HS6 with st_ok_pi _ _ ?Ef _ (restrict _ ?msF) =>
    set (ms6 := msF) in *;
    assert (O6 : forall n, (n < 41)%nat -> ew Ef n = ew E2 n) by (intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity)
  end.
  prreg HS6 (1%bv : bv 5) T1. prreg HS6 (10%bv : bv 5) T10.
  assert (T1' : getr (ms_regs ms6) 1 = getr regs 1) by (rewrite T1; try rewrite O6 by lia; exact (EX2 2%nat ltac:(lia))).
  assert (T10' : getr (ms_regs ms6) 10 = w64 q) by (rewrite T10; try rewrite O6 by lia; exact E33).
  clear T1 T10.
  (* the callee-saved registers: the seven restores and the untouched ones *)
  assert (KEEP : aregs_preserved regs (ms_regs ms6)).
  { intros rr Hr. unfold acallee_saved in Hr.
    assert (Hc : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/
                 rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
    clear Hr.
    assert (UT : forall c : nat, In (Z.of_nat c) TO_UNTOUCHED -> (c < 32)%nat ->
              getr (ms_regs ms4) (Z_to_bv 5 (Z.of_nat c)) = getr R (Z_to_bv 5 (Z.of_nat c)) ->
              ew E2 c = getr regs (Z_to_bv 5 (Z.of_nat c))).
    { intros c Hin Hc32 Hq.
      rewrite (ER2 c (Z_to_bv 5 (Z.of_nat c)) ltac:(rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
                 change (2 ^ Z.of_N 5) with 32; symmetry; apply Z.mod_small; lia) ltac:(unfold A_TEXT; lia)).
      rewrite Hq. exact (RUT _ Hin). }
    repeat (destruct Hc as [Hc | Hc]; [subst rr;
      lazymatch goal with |- getr _ (Z_to_bv 5 ?c) = _ =>
        let Q := fresh "Q" in prreg HS6 (Z_to_bv 5 c) Q; rewrite Q; try rewrite O6 by lia;
        first [ exact (UT 3%nat ltac:(unfold TO_UNTOUCHED; cbn; tauto) ltac:(lia) Q3)
              | exact (UT 4%nat ltac:(unfold TO_UNTOUCHED; cbn; tauto) ltac:(lia) Q4)
              | exact (UT 22%nat ltac:(unfold TO_UNTOUCHED; cbn; tauto) ltac:(lia) Q22)
              | exact (UT 23%nat ltac:(unfold TO_UNTOUCHED; cbn; tauto) ltac:(lia) Q23)
              | exact (UT 24%nat ltac:(unfold TO_UNTOUCHED; cbn; tauto) ltac:(lia) Q24)
              | exact (UT 25%nat ltac:(unfold TO_UNTOUCHED; cbn; tauto) ltac:(lia) Q25)
              | exact (UT 26%nat ltac:(unfold TO_UNTOUCHED; cbn; tauto) ltac:(lia) Q26)
              | first [ exact (EX2 3%nat ltac:(lia)) | exact (EX2 4%nat ltac:(lia))
                                         | exact (EX2 5%nat ltac:(lia)) | exact (EX2 6%nat ltac:(lia))
                                         | exact (EX2 7%nat ltac:(lia)) | exact (EX2 8%nat ltac:(lia)) ]
              | rewrite U2; replace (sp - 64 + 64) with (spZ regs) by lia;
                unfold spZ; apply Z_to_bv_bv_unsigned ]
      end |]).
    subst rr. prreg HS6 (Z_to_bv 5 27) Q. rewrite Q. try rewrite O6 by lia.
    exact (UT 27%nat ltac:(unfold TO_UNTOUCHED; cbn; tauto) ltac:(lia) Q27). }
  (* the run wrote nothing *)
  assert (Hmem6 : ms_mem ms6 = ms_mem ms4).
  { apply functional_extensionality. intros x. apply HF. intros (r0 & Hin & Hw).
    unfold to_ss188, to_stk7, to_tw in Hin. cbn [ss_mem In] in Hin.
    destruct Hin as [<- | [<- | []]]; cbn [YP09.r_wlo YP09.r_whi YP09.r_base base_val] in Hw; lia. }
  eapply (paj_ret_at (PL := PL_link) (PI := PI) W _ _ _ _ _ HS6 eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'.
  rewrite T1'. unfold YK0s.ret_ok in Hraw. rewrite Hraw.
  unfold to_post.
  apply (apost_leaf_app SK SEGS B LAWS pa_segs_low TEXT_OF_AK 1 (to_E cx)
    (to_G cx) (to_XO cx) (to_OUT cx) (to_STK cx) (to_sp0 cx) (to_FP cx) (to_ly cx) (to_S cx) (to_W0 cx) (to_mem0 cx)
    (to_md0 cx) (to_own cx) (to_lyc cx) (to_Sc cx) W (to_memc cx) (to_mdc cx) (to_k cx) regs _ _ _ _ HJ).
  - first [ exact HJ4 | (repeat rewrite wvb_collapse in HJ4); exact HJ4
          | apply (ajournal_gx_materialize SEGS B LAWS pa_segs_low);
            first [exact HJ4 | (repeat rewrite wvb_collapse in HJ4); exact HJ4] ].
  - lia.
  - exact Hwlo.
  - lia.
  - repeat rewrite (proj1 (wvb_fds_fs _ _ _)). exact Hfd.
  - repeat rewrite (proj2 (wvb_fds_fs _ _ _)). exact Hfs.
  - exact KEEP.
  - intros a Ha Hw HE. rewrite Hmem6, Hmem4. exact (HUN a Ha Hw HE).
  - intros a Hp. rewrite Hmem6, Hmem4. exact (HPR a Hp).
  - intros a Ha. rewrite Hmem6, Hmem4. exact (HPW a Ha).
  - intros x ((lo, hi) & Hin & Hx). unfold to_E, to_wr, text_of_awr in Hin. cbn [In] in Hin.
    unfold amem_range in AMp, AMo. unfold to_p, to_o in AMp, AMo.
    destruct Hin as [Heq | [Heq | []]]; injection Heq as <- <-; cbn [fst snd] in Hx;
      unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia.
  - split.
    { apply (mo_le_mono MT MTL _ _ 0); [apply (mo_le_refl MT MTL) | apply (mo_malloc_nonneg MT MTL); unfold TEXT_OF_LIVE; lia]. }
    split; [unfold text_of_ledpost; lia|].
    unfold text_of_apostA. intros c0 c1 Hc0 Hc1 Hr0 Hr1.
    destruct (HCUR c0 c1 Hc0 Hc1 Hr0 Hr1) as (adv & Hadv & Hp0 & Hp8).
    exists 0, q, s.
    split; [exact T10'|]. split; [lia|].
    rewrite Hmem6, Hmem4.
    split; [exact Hcs|]. split; [exact Hl320|]. split; [exact HOWN|]. split; [lia|].
    split; [exists adv; split; [exact Hadv|]; split; [exact Hp0|]; split; [exact Hp8 | exact HABP]|].
    split.
    + intros _. split; [apply Permutation_refl|]. split; [exists i; split; [exact Hi | exact Hq0] | exact Hro0].
    + intros Hne. exfalso. exact (Hne eq_refl).
Qed.

End b.
End a.

About to_table.
Print Assumptions to_table.
