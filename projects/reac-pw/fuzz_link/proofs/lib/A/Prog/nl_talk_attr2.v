(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed and off_img at fuzz_command's ASan image end 0x606000; ajournal no longer keeps footprint (FP) bytes in the image or at or above alloc_ceiling (fp_spares FP a also requires ~ inFP FP a, and the clause for bytes at or above alloc_ceiling outside [sp0 - STK, sp0) requires ~ inFP FP a), awr_byte (and awr_ok) take the start state's side-stack frames as a new parameter and also admit footprint writes to the program's statics as_prog_static in the image, to the caller's stack above sp0 and to those caller frames (awr_prog_or_caller), acall_kept_of_journal, region_kept_stack_sub, awr_byte_present and aj_intrin_at take the matching premises, ajournal_sub_wide composes a callee whose footprint lies in what the caller may write, awr_byte_present_prog and aj_intrin_at_prog take prog_rw for stores to the statics, AR_errno_present gives the errno cell's value from errno_rom, and astack_rd/astack_pres (stack bytes readable/present from sp to the stack top) give a frame chain for any s0 but an aligned sp + 8 (chain_pre_any, achain_any) and carry across an ajournal (astack_rd_journal, astack_pres_journal). *)
(* Modified by Theorem Labs, 2026-10: the malloc/free journal lemmas (aj_free_at, aj_free_at_io, aj_free_null_at, aj_free_null_at_io, aj_malloc_at, aj_malloc_at_io, aj_malloc_at04, aj_malloc_at04_io, aj_malloc, aj_free) no longer take In (call_trace0 ...) (as_universe B); the model laws get the trace length (call_trace_len) and the contracts the event bound. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/Reusable/YCbq.v, with its module paths and module names changed; 1154 of its 1305 lines of code are new or changed and 3194 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LinkWalkSide.v, with its module paths and module names changed; 1431 of its 1477 lines of code are new or changed and 1259 lines of the source are left out. *)
(* nl_talk on image A (fuzz_link.asan 0x88974), THE ATTRIBUTE PHASE, part 2: the symbolic states at the cuts, the
   segments between them, the two loops by induction on the fuel of link_spec's attr_scan / kind_scan, and the phase
   lemma nt_attr. Part 1 (nl_talk_attr.v) holds the cut invariants na_c1 (+0x338), na_c2 (+0x470), na_c3 (+0x3ac),
   the concrete tail of a turn, the byte transports, and the copy_attr call (na_call).

   The two more cuts of this file:
     +0x454  NT_astep  the attribute loop's step (na_cs): every path of a turn joins here;
     +0x400  NT_istep  the nested loop's step (na_c4): the nested type test and the kind call join here.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality Classical.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit LinkWalk.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkPi LinkWalkSide LinkWalkWseg LinkWalkCall LinkWalkShadow link_aro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import nl_talk_c copy_attr_c nl_talk_defs nl_talk_kit nl_talk_attr.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* an environment that extends another with atoms at k or above agrees with it below k *)
Ltac na_ag :=
  lazymatch goal with
  | |- env_agree ?k ?E1 (ewset ?X ?n ?w) => apply (na_ag_trans k E1 X (ewset X n w)); [na_ag | apply na_ag_ewset; lia]
  | |- env_agree ?k ?E1 ?E1 => apply env_agree_refl
  end.

(* the register of a symbolic state, unnormalised *)
Ltac na_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
      cbn [ms_regs restrict] in Hr
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
      cbn [ms_regs restrict] in Hr
  end.

(* the write obligation of a run whose regions write nothing *)
Ltac na_awr0 :=
  repeat (apply awr_ok_x_cons; [let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
    cbn [na_spill na_hdr YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; lia |]);
  apply awr_ok_x_nil.

(* a cut's machine state, opened into its registers and memory *)
Ltac na_open ms3 Hsh rg mm :=
  let fr := fresh "fr" in let pcv := fresh "pcv" in let sv := fresh "sv" in let rv := fresh "rv" in
  let fc := fresh "fc" in let ro := fresh "ro" in
  let H1 := fresh "H1" in let H2 := fresh "H2" in let H3 := fresh "H3" in let H4 := fresh "H4" in
  let H5 := fresh "H5" in let H6 := fresh "H6" in
  destruct ms3 as [rg fr pcv sv rv fc mm ro]; destruct Hsh as (H1 & H2 & H3 & H4 & H5 & H6);
  cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem] in *; subst pcv sv rv ro fr fc.


(* the memory a run that wrote nothing leaves *)
Ltac na_ro HF := apply (na_frame_ro _ _ _ _ HF); repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil.
Ltac na_mem Hnew HF mm := lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => assert (Hnew : ms_mem m = mm) by (na_ro HF) end.
Ltac na_mem2 Hnew HF Hold mm :=
  lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => assert (Hnew : ms_mem m = mm) by (rewrite <- Hold; na_ro HF) end.
(* the agreement of the run's environment with the cut's registers and extras *)
Ltac na_hae HS HAE0 HE0 E0 name :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ex _ _ => assert (name : env_agree 40 _ Ex)
      by (apply (na_ag_trans 40 _ E0); [exact HAE0 | apply (na_ag_le 512); [lia | rewrite HE0; na_ag]])
  | st_ok _ ?Ex _ _ => assert (name : env_agree 40 _ Ex)
      by (apply (na_ag_trans 40 _ E0); [exact HAE0 | apply (na_ag_le 512); [lia | rewrite HE0; na_ag]])
  end.


Lemma na_S_addw32 : forall E (n : nat) x, ew E n = w64 x -> 16 <= x < 2 ^ 31 ->
  Sg E (SAluw ALU_ADD (SOff n 0) (SLit (-32))) = x - 32.
Proof.
  intros E n x Hn Hx. rewrite S_SAluw. cbn [zalu_raw].
  rewrite (U_atom E n x Hn) by lia. rewrite U_SLit. unfold zcanon, M64.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
  lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.

Section b.
Context {PI : PAImg link_listing}.
#[local] Abbreviation SEGS := (pa_segs).
#[local] Abbreviation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis LV : LinkVals.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.
Hypothesis RELRO_IMG : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img pa_segs a.
Hypothesis CA : copy_attr_acontract SK pa_segs PCAP_RLO PCAP_RHI B.

(* the extra atoms of a symbolic state: 32, 33 the attribute's length and type, 34 .. 37 the two buffers and their
   caps as spilled, 38, 39 the nested attribute's length and type *)
Definition na_ext (cx : ntcx) (c : list byte) (p q : Z) : list word :=
  [w64 (rd16 c p); w64 (rd16 c (p + 2)); w64 (n_alias cx); w64 (n_aliasn cx); w64 (n_kind cx); w64 (n_kindn cx);
   w64 (rd16 c q); w64 (rd16 c (q + 2))].


(* ==========================================================================
   1. The two more cuts
   ========================================================================== *)

(* NT_astep (+0x454): the attribute at aoff passed both bounds; the turn's work is done and its accumulator is a;
   s9 holds the attribute's shadow address *)
Definition na_cs (cx : ntcx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state)
    (md3 : Model) (c rest bs : list byte) (f : nat) (aoff aleft : Z) (a : attrs) : Prop :=
  na_core SK B cx fp k2 ly3 S3 W3 ms3 md3 c rest bs /\ na_slots cx W3 ms3 /\ nt_shape NT_astep ms3 /\
  getr (ms_regs ms3) 26 = w64 (nBUF cx fp + aoff) /\ getr (ms_regs ms3) 22 = w64 aleft /\
  getr (ms_regs ms3) 25 = w64 (SHADOW_OFF + (nBUF cx fp + aoff) / 8) /\
  getr (ms_regs ms3) 20 = w64 131068 /\ getr (ms_regs ms3) 13 = w64 4 /\ getr (ms_regs ms3) 14 = w64 3 /\
  0 <= aoff /\ 4 <= rd16 c aoff <= aleft /\ aoff + aleft <= Z.of_nat (length c) /\ (Z.to_nat aleft <= f)%nat /\
  talk_attrs (n_K0 cx) = attr_scan f c (aoff + nl_align (rd16 c aoff)) (aleft - nl_align (rd16 c aoff)) a /\
  na_bufs cx (rdW W3 (ms_mem ms3)) a.

(* NT_istep (+0x400): inside the IFLA_LINKINFO at aoff, the nested attribute at ioff passed both bounds and its
   kind test (and copy) is done, with the kind so far k; s3 holds its shadow address *)
Definition na_c4 (cx : ntcx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state)
    (md3 : Model) (c rest bs : list byte) (f g : nat) (aoff aleft ioff ileft : Z)
    (k al : option (list byte)) : Prop :=
  na_core SK B cx fp k2 ly3 S3 W3 ms3 md3 c rest bs /\ na_slots cx W3 ms3 /\ nt_shape NT_istep ms3 /\
  getr (ms_regs ms3) 26 = w64 (nBUF cx fp + aoff) /\ getr (ms_regs ms3) 22 = w64 aleft /\
  getr (ms_regs ms3) 25 = w64 (SHADOW_OFF + (nBUF cx fp + aoff) / 8) /\
  getr (ms_regs ms3) 27 = w64 (nBUF cx fp + ioff) /\ getr (ms_regs ms3) 23 = w64 ileft /\
  getr (ms_regs ms3) 19 = w64 (SHADOW_OFF + (nBUF cx fp + ioff) / 8) /\
  getr (ms_regs ms3) 20 = w64 131068 /\ getr (ms_regs ms3) 13 = w64 4 /\ getr (ms_regs ms3) 14 = w64 3 /\
  0 <= aoff /\ 8 <= rd16 c aoff <= aleft /\ aoff + aleft <= Z.of_nat (length c) /\
  aoff + 4 <= ioff /\ ioff + ileft = aoff + rd16 c aoff /\ 4 <= rd16 c ioff <= ileft /\ (Z.to_nat ileft <= g)%nat /\
  aleft <= Z.of_nat f /\
  talk_attrs (n_K0 cx) =
    attr_scan f c (aoff + nl_align (rd16 c aoff)) (aleft - nl_align (rd16 c aoff))
      (Attrs (kind_scan g c (ioff + nl_align (rd16 c ioff)) (ileft - nl_align (rd16 c ioff)) k) al) /\
  na_bufs cx (rdW W3 (ms_mem ms3)) (Attrs k al).

(* ==========================================================================
   2. The symbolic states, built from a cut
   ========================================================================== *)

Lemma na_ew_ext : forall rg ext j, (32 + j < A_TEXT)%nat -> ew (Eimg (Ereg rg ext)) (32 + j) = nth j ext (Z_to_bv 64 0).
Proof. intros rg ext j Hj. rewrite Eimg_low by exact Hj. apply ew_Ereg_extra. Qed.

Lemma na_bu : forall v, 0 <= v < 2 ^ 64 -> bv_unsigned (w64 v) = v.
Proof. intros v Hv. unfold w64. apply unsigned_lit_small. exact Hv. Qed.

(* one attribute header (the outer loop: +0x338, +0x454) *)
Lemma na_st1 : forall cx fp k2 ly3 S3 W3 rg mm md3 c rest bs pc p,
  nt_base SK B cx ->
  na_core SK B cx fp k2 ly3 S3 W3 (mkst rg (w64 (BASE + pc)) mm (seg_rom SEGS)) md3 c rest bs ->
  na_slots cx W3 (mkst rg (w64 (BASE + pc)) mm (seg_rom SEGS)) ->
  getr rg 26 = w64 (nBUF cx fp + p) -> 0 <= p -> p + 4 <= Z.of_nat (length c) ->
  st_ok_pi SEGS pa_val (Eimg (Ereg rg (na_ext cx c p p)))
    (mkSS pc sr_atoms [na_spill; na_hdr 26 32 33] None na_fac1)
    (restrict (w_H W3) (mkst rg (w64 (BASE + pc)) mm (seg_rom SEGS))) /\
  sh_ok SEGS na_Bx na_SH1 (Eimg (Ereg rg (na_ext cx c p p))) (mrestrict (w_H W3) mm).
Proof.
  intros cx fp k2 ly3 S3 W3 rg mm md3 c rest bs pc p HB HC HSl R26 Hp0 Hp4.
  pose proof (na_geom SK B LAWS cx fp k2 ly3 S3 W3 _ md3 c rest bs HB HC) as
    (HAR3 & Hin9 & Hfa9 & HF4 & HFc & HF64 & HFapp & Hsp & Hsp47 & Hsp16 & Hsp1 & Hsp132 & Hwin1 & Hwin2).
  unfold NL_TALK_AK, NL_TALK_AFRAME, NL_TALK_ASLACK, COPY_ATTR_AK, COPY_ATTR_AFRAME, ESTACK in Hsp, Hwin1.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HC as (_ & HR & _ & _ & HS0 & _ & _ & _ & HFS & _ & _ & _ & _ & _ & _ & HBY & HBL & HCL & _).
  cbn [ms_mem ms_regs mkst] in HR, HS0, HFS, HBY.
  pose proof HR as (R2 & R8 & R9 & R18 & R21 & R24 & R3 & R4). cbn [ms_regs mkst] in R2, R9, R21.
  destruct HSl as (SA & SAN). destruct HS0 as (SK0 & SKN & SF).
  unfold nt_at, NS_ALIAS, NS_ALIASN, NS_KIND, NS_KINDN in SA, SAN, SK0, SKN. cbn [ms_mem mkst] in SA, SAN, SK0, SKN.
  assert (Hlen0 : (length c <= 4096)%nat) by (unfold NL_CHUNK_MAX in HCL; exact HCL).
  pose proof (na_aarg_range (n_regs cx) 2) as Rk. pose proof (na_aarg_range (n_regs cx) 3) as Rkn.
  pose proof (na_aarg_range (n_regs cx) 4) as Ra. pose proof (na_aarg_range (n_regs cx) 5) as Ran.
  pose proof (nt_rd16_range c p Hp0 ltac:(lia)) as Rl. pose proof (nt_rd16_range c (p + 2) ltac:(lia) ltac:(lia)) as Rt.
  remember (Eimg (Ereg rg (na_ext cx c p p))) as E eqn:HE.
  assert (E9 : ew E 9 = w64 (n_sp1 cx)) by (rewrite HE, (ew_Eimg_Ereg_nat rg _ 9 9%bv eq_refl); exact R9).
  assert (E21 : ew E 21 = w64 SHADOW_OFF) by (rewrite HE, (ew_Eimg_Ereg_nat rg _ 21 21%bv eq_refl); exact R21).
  assert (E26 : ew E 26 = w64 (nBUF cx fp + p)) by (rewrite HE, (ew_Eimg_Ereg_nat rg _ 26 26%bv eq_refl); exact R26).
  assert (E2 : ew E 2 = w64 (n_sp1 cx)) by (rewrite HE, (ew_Eimg_Ereg_nat rg _ 2 2%bv eq_refl); exact R2).
  assert (E32 : ew E 32 = w64 (rd16 c p)) by (rewrite HE; exact (na_ew_ext rg _ 0 ltac:(unfold A_TEXT; lia))).
  assert (E33 : ew E 33 = w64 (rd16 c (p + 2))) by (rewrite HE; exact (na_ew_ext rg _ 1 ltac:(unfold A_TEXT; lia))).
  assert (E34 : ew E 34 = w64 (n_alias cx)) by (rewrite HE; exact (na_ew_ext rg _ 2 ltac:(unfold A_TEXT; lia))).
  assert (E35 : ew E 35 = w64 (n_aliasn cx)) by (rewrite HE; exact (na_ew_ext rg _ 3 ltac:(unfold A_TEXT; lia))).
  assert (E36 : ew E 36 = w64 (n_kind cx)) by (rewrite HE; exact (na_ew_ext rg _ 4 ltac:(unfold A_TEXT; lia))).
  assert (E37 : ew E 37 = w64 (n_kindn cx)) by (rewrite HE; exact (na_ew_ext rg _ 5 ltac:(unfold A_TEXT; lia))).
  assert (U9 : bv_unsigned (ew E 9) = n_sp1 cx) by (rewrite E9; apply na_bu; lia).
  assert (U2 : bv_unsigned (ew E 2) = n_sp1 cx) by (rewrite E2; apply na_bu; lia).
  assert (U26 : bv_unsigned (ew E 26) = nBUF cx fp + p) by (rewrite E26; apply na_bu; unfold nBUF, NT_BUFOFF; lia).
  assert (U21 : bv_unsigned (ew E 21) = SHADOW_OFF) by (rewrite E21; apply na_bu; unfold SHADOW_OFF; lia).
  assert (U32 : bv_unsigned (ew E 32) = rd16 c p) by (rewrite E32; apply na_bu; lia).
  assert (U33 : bv_unsigned (ew E 33) = rd16 c (p + 2)) by (rewrite E33; apply na_bu; lia).
  split.
  - rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    + rewrite HE. apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (na_spill_ok E W3 mm (n_sp1 cx) (n_alias cx) (n_aliasn cx) (n_kind cx) (n_kindn cx) U9
          ltac:(lia) ltac:(lia) E34 E35 E36 E37 Ra Ran Rk Rkn SA SAN SK0 SKN).
      * apply (na_hdr_ok E _ 26 32 33 (nBUF cx fp + p) (rd16 c p) (rd16 c (p + 2)) U26
          ltac:(unfold nBUF, NT_BUFOFF; lia) ltac:(unfold nBUF, NT_BUFOFF; lia) E32 E33 Rl Rt).
        -- exact (nt_read2 SEGS (rdW W3 mm) (nBUF cx fp) c rest p HBY Hp0 ltac:(lia)).
        -- pose proof (nt_read2 SEGS (rdW W3 mm) (nBUF cx fp) c rest (p + 2) HBY ltac:(lia) ltac:(lia)) as V.
           rewrite Z.add_assoc in V. exact V.
    + apply pairwise_disjoint_of_extents. unfold na_spill, na_hdr, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U26.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold nBUF, NT_BUFOFF. repeat split; lia.
    + split; [|split; exact I].
      unfold na_fac1, na_spf, na_pf, na_hf. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U21, U26, U32, U33, U9, U2. change (2 ^ 5) with 32. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
      unfold nBUF, NT_BUFOFF, SHADOW_OFF in *.
      repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
  - unfold sh_ok, na_SH1. apply Forall_cons; [|apply Forall_nil].
    apply (na_shent_ok E W3 mm 26 (nBUF cx fp + p) E21 E26).
    + unfold nBUF, NT_BUFOFF; lia.
    + unfold in_app, ASAN_CEIL, nBUF, NT_BUFOFF in *. unfold kLowMemEnd, kLowShadowBeg, kHighMemBeg in *. lia.
    + unfold nBUF, NT_BUFOFF; lia.
    + apply (na_ra_buf cx fp W3 (mkst rg (w64 (BASE + pc)) mm (seg_rom SEGS))); [exact HFS | exact HF64 | lia |].
      unfold NT_BUFLEN, nBUF, NT_BUFOFF in *. lia.
Qed.

(* the two-header state (the nested loop: +0x3ac, +0x400) *)
Lemma na_st3 : forall cx fp k2 ly3 S3 W3 rg mm md3 c rest bs pc p q,
  nt_base SK B cx ->
  na_core SK B cx fp k2 ly3 S3 W3 (mkst rg (w64 (BASE + pc)) mm (seg_rom SEGS)) md3 c rest bs ->
  na_slots cx W3 (mkst rg (w64 (BASE + pc)) mm (seg_rom SEGS)) ->
  getr rg 26 = w64 (nBUF cx fp + p) -> getr rg 27 = w64 (nBUF cx fp + q) ->
  0 <= p -> p + 4 <= q -> q + 4 <= Z.of_nat (length c) ->
  st_ok_pi SEGS pa_val (Eimg (Ereg rg (na_ext cx c p q)))
    (mkSS pc sr_atoms [na_spill; na_hdr 26 32 33; na_hdr 27 38 39] None na_fac3)
    (restrict (w_H W3) (mkst rg (w64 (BASE + pc)) mm (seg_rom SEGS))) /\
  sh_ok SEGS na_Bx na_SH3 (Eimg (Ereg rg (na_ext cx c p q))) (mrestrict (w_H W3) mm).
Proof.
  intros cx fp k2 ly3 S3 W3 rg mm md3 c rest bs pc p q HB HC HSl R26 R27 Hp0 Hpq Hq4.
  pose proof (na_geom SK B LAWS cx fp k2 ly3 S3 W3 _ md3 c rest bs HB HC) as
    (HAR3 & Hin9 & Hfa9 & HF4 & HFc & HF64 & HFapp & Hsp & Hsp47 & Hsp16 & Hsp1 & Hsp132 & Hwin1 & Hwin2).
  unfold NL_TALK_AK, NL_TALK_AFRAME, NL_TALK_ASLACK, COPY_ATTR_AK, COPY_ATTR_AFRAME, ESTACK in Hsp, Hwin1.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HC as (_ & HR & _ & _ & HS0 & _ & _ & _ & HFS & _ & _ & _ & _ & _ & _ & HBY & HBL & HCL & _).
  cbn [ms_mem ms_regs mkst] in HR, HS0, HFS, HBY.
  pose proof HR as (R2 & R8 & R9 & R18 & R21 & R24 & R3 & R4). cbn [ms_regs mkst] in R2, R9, R21.
  destruct HSl as (SA & SAN). destruct HS0 as (SK0 & SKN & SF).
  unfold nt_at, NS_ALIAS, NS_ALIASN, NS_KIND, NS_KINDN in SA, SAN, SK0, SKN. cbn [ms_mem mkst] in SA, SAN, SK0, SKN.
  assert (Hlen0 : (length c <= 4096)%nat) by (unfold NL_CHUNK_MAX in HCL; exact HCL).
  pose proof (na_aarg_range (n_regs cx) 2) as Rk. pose proof (na_aarg_range (n_regs cx) 3) as Rkn.
  pose proof (na_aarg_range (n_regs cx) 4) as Ra. pose proof (na_aarg_range (n_regs cx) 5) as Ran.
  pose proof (nt_rd16_range c p Hp0 ltac:(lia)) as Rl. pose proof (nt_rd16_range c (p + 2) ltac:(lia) ltac:(lia)) as Rt.
  pose proof (nt_rd16_range c q ltac:(lia) ltac:(lia)) as Rl'. pose proof (nt_rd16_range c (q + 2) ltac:(lia) ltac:(lia)) as Rt'.
  remember (Eimg (Ereg rg (na_ext cx c p q))) as E eqn:HE.
  assert (E9 : ew E 9 = w64 (n_sp1 cx)) by (rewrite HE, (ew_Eimg_Ereg_nat rg _ 9 9%bv eq_refl); exact R9).
  assert (E21 : ew E 21 = w64 SHADOW_OFF) by (rewrite HE, (ew_Eimg_Ereg_nat rg _ 21 21%bv eq_refl); exact R21).
  assert (E26 : ew E 26 = w64 (nBUF cx fp + p)) by (rewrite HE, (ew_Eimg_Ereg_nat rg _ 26 26%bv eq_refl); exact R26).
  assert (E27 : ew E 27 = w64 (nBUF cx fp + q)) by (rewrite HE, (ew_Eimg_Ereg_nat rg _ 27 27%bv eq_refl); exact R27).
  assert (E2 : ew E 2 = w64 (n_sp1 cx)) by (rewrite HE, (ew_Eimg_Ereg_nat rg _ 2 2%bv eq_refl); exact R2).
  assert (E32 : ew E 32 = w64 (rd16 c p)) by (rewrite HE; exact (na_ew_ext rg _ 0 ltac:(unfold A_TEXT; lia))).
  assert (E33 : ew E 33 = w64 (rd16 c (p + 2))) by (rewrite HE; exact (na_ew_ext rg _ 1 ltac:(unfold A_TEXT; lia))).
  assert (E34 : ew E 34 = w64 (n_alias cx)) by (rewrite HE; exact (na_ew_ext rg _ 2 ltac:(unfold A_TEXT; lia))).
  assert (E35 : ew E 35 = w64 (n_aliasn cx)) by (rewrite HE; exact (na_ew_ext rg _ 3 ltac:(unfold A_TEXT; lia))).
  assert (E36 : ew E 36 = w64 (n_kind cx)) by (rewrite HE; exact (na_ew_ext rg _ 4 ltac:(unfold A_TEXT; lia))).
  assert (E37 : ew E 37 = w64 (n_kindn cx)) by (rewrite HE; exact (na_ew_ext rg _ 5 ltac:(unfold A_TEXT; lia))).
  assert (E38 : ew E 38 = w64 (rd16 c q)) by (rewrite HE; exact (na_ew_ext rg _ 6 ltac:(unfold A_TEXT; lia))).
  assert (E39 : ew E 39 = w64 (rd16 c (q + 2))) by (rewrite HE; exact (na_ew_ext rg _ 7 ltac:(unfold A_TEXT; lia))).
  assert (U9 : bv_unsigned (ew E 9) = n_sp1 cx) by (rewrite E9; apply na_bu; lia).
  assert (U2 : bv_unsigned (ew E 2) = n_sp1 cx) by (rewrite E2; apply na_bu; lia).
  assert (U26 : bv_unsigned (ew E 26) = nBUF cx fp + p) by (rewrite E26; apply na_bu; unfold nBUF, NT_BUFOFF; lia).
  assert (U27 : bv_unsigned (ew E 27) = nBUF cx fp + q) by (rewrite E27; apply na_bu; unfold nBUF, NT_BUFOFF; lia).
  assert (U21 : bv_unsigned (ew E 21) = SHADOW_OFF) by (rewrite E21; apply na_bu; unfold SHADOW_OFF; lia).
  assert (U32 : bv_unsigned (ew E 32) = rd16 c p) by (rewrite E32; apply na_bu; lia).
  assert (U33 : bv_unsigned (ew E 33) = rd16 c (p + 2)) by (rewrite E33; apply na_bu; lia).
  assert (U38 : bv_unsigned (ew E 38) = rd16 c q) by (rewrite E38; apply na_bu; lia).
  assert (U39 : bv_unsigned (ew E 39) = rd16 c (q + 2)) by (rewrite E39; apply na_bu; lia).
  split.
  - rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    + rewrite HE. apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
      * apply (na_spill_ok E W3 mm (n_sp1 cx) (n_alias cx) (n_aliasn cx) (n_kind cx) (n_kindn cx) U9
          ltac:(lia) ltac:(lia) E34 E35 E36 E37 Ra Ran Rk Rkn SA SAN SK0 SKN).
      * apply (na_hdr_ok E _ 26 32 33 (nBUF cx fp + p) (rd16 c p) (rd16 c (p + 2)) U26
          ltac:(unfold nBUF, NT_BUFOFF; lia) ltac:(unfold nBUF, NT_BUFOFF; lia) E32 E33 Rl Rt).
        -- exact (nt_read2 SEGS (rdW W3 mm) (nBUF cx fp) c rest p HBY Hp0 ltac:(lia)).
        -- pose proof (nt_read2 SEGS (rdW W3 mm) (nBUF cx fp) c rest (p + 2) HBY ltac:(lia) ltac:(lia)) as V.
           rewrite Z.add_assoc in V. exact V.
      * apply (na_hdr_ok E _ 27 38 39 (nBUF cx fp + q) (rd16 c q) (rd16 c (q + 2)) U27
          ltac:(unfold nBUF, NT_BUFOFF; lia) ltac:(unfold nBUF, NT_BUFOFF; lia) E38 E39 Rl' Rt').
        -- exact (nt_read2 SEGS (rdW W3 mm) (nBUF cx fp) c rest q HBY ltac:(lia) ltac:(lia)).
        -- pose proof (nt_read2 SEGS (rdW W3 mm) (nBUF cx fp) c rest (q + 2) HBY ltac:(lia) ltac:(lia)) as V.
           rewrite Z.add_assoc in V. exact V.
    + apply pairwise_disjoint_of_extents. unfold na_spill, na_hdr, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U26, U27.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      unfold nBUF, NT_BUFOFF. repeat split; lia.
    + split; [|split; exact I].
      unfold na_fac3, na_spf, na_pf, na_hf. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U21, U26, U27, U32, U33, U38, U39, U9, U2. change (2 ^ 5) with 32. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
      unfold nBUF, NT_BUFOFF, SHADOW_OFF in *.
      repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
  - unfold sh_ok, na_SH3. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (na_shent_ok E W3 mm 26 (nBUF cx fp + p) E21 E26).
      * unfold nBUF, NT_BUFOFF; lia.
      * unfold in_app, ASAN_CEIL, nBUF, NT_BUFOFF in *. unfold kLowMemEnd, kLowShadowBeg, kHighMemBeg in *. lia.
      * unfold nBUF, NT_BUFOFF; lia.
      * apply (na_ra_buf cx fp W3 (mkst rg (w64 (BASE + pc)) mm (seg_rom SEGS))); [exact HFS | exact HF64 | lia |].
        unfold NT_BUFLEN, nBUF, NT_BUFOFF in *. lia.
    + apply (na_shent_ok E W3 mm 27 (nBUF cx fp + q) E21 E27).
      * unfold nBUF, NT_BUFOFF; lia.
      * unfold in_app, ASAN_CEIL, nBUF, NT_BUFOFF in *. unfold kLowMemEnd, kLowShadowBeg, kHighMemBeg in *. lia.
      * unfold nBUF, NT_BUFOFF; lia.
      * apply (na_ra_buf cx fp W3 (mkst rg (w64 (BASE + pc)) mm (seg_rom SEGS))); [exact HFS | exact HF64 | lia |].
        unfold NT_BUFLEN, nBUF, NT_BUFOFF in *. lia.
Qed.

(* the shadow address register a head computed *)
Lemma na_shx_val : forall E (n : nat) v, ew E n = w64 v -> ew E 21 = w64 SHADOW_OFF -> 0 <= v < 2 ^ 47 ->
  sv_denot E (na_shx n) = w64 (SHADOW_OFF + v / 8).
Proof.
  intros E n v Hn H21 Hv. unfold na_shx.
  rewrite (denot_shx E n 21 0 v SHADOW_OFF Hn H21 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold SHADOW_OFF; lia)).
  rewrite Z.add_0_r. reflexivity.
Qed.

(* a cut's core after a run that wrote nothing *)
Lemma na_core_run : forall cx fp k2 ly3 S3 W3 ms ms' md md' c rest bs,
  na_core SK B cx fp k2 ly3 S3 W3 ms md c rest bs ->
  ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms') md' k2 ->
  ms_mem ms' = ms_mem ms ->
  (forall r, In r [2%bv; 8%bv; 9%bv; 18%bv; 21%bv; 24%bv; 3%bv; 4%bv] -> getr (ms_regs ms') r = getr (ms_regs ms) r) ->
  m_fds md' = m_fds md -> m_fs md' = m_fs md ->
  na_core SK B cx fp k2 ly3 S3 W3 ms' md' c rest bs.
Proof.
  intros cx fp k2 ly3 S3 W3 ms ms' md md' c rest bs
    (HJ & HR & HSV & HH & HS0 & HA1 & HA2 & HA3 & HFS & HJB & HK & HG & HGO & HOW & HRC & HBY & HBL & HCL & HBUF)
    HJ' Hm Hr Hfd Hfs.
  unfold na_core, nt_saved, nt_header, nt_slots0, nt_at, nt_frame_shadow in *. rewrite Hm in HJ' |- *.
  split; [exact HJ'|].
  split.
  { destruct HR as (R2 & R8 & R9 & R18 & R21 & R24 & R3 & R4). unfold nt_regs.
    rewrite !Hr by (cbn; tauto). tauto. }
  split; [exact HSV|]. split; [exact HH|]. split; [exact HS0|].
  split; [exact HA1|]. split; [exact HA2|]. split; [exact HA3|]. split; [exact HFS|].
  split.
  { unfold nt_jbk in *. rewrite Hfd, Hfs. exact HJB. }
  tauto.
Qed.

(* ==========================================================================
   3. The segments, inside one call (POST, cx and the frame's slot fp fixed)
   ========================================================================== *)


(* the three instructions after copy_attr returns at +0x390 (alias), the two after +0x3f8 (kind) *)
Lemma na_fetch_r0 : fetch_word SEGS (Z_to_bv 64 (BASE + NT_ca_a_ra)) = Some (Z_to_bv 32 0x00300713).
Proof. apply pa_fetch_pw. vm_compute. reflexivity. Qed.
Lemma na_fetch_r1 : fetch_word SEGS (Z_to_bv 64 (BASE + (NT_ca_a_ra + 4))) = Some (Z_to_bv 32 0x00400693).
Proof. apply pa_fetch_pw. vm_compute. reflexivity. Qed.
Lemma na_fetch_r2 : fetch_word SEGS (Z_to_bv 64 (BASE + (NT_ca_a_ra + 4 + 4))) = Some (Z_to_bv 32 0x0bc0006f).
Proof. apply pa_fetch_pw. vm_compute. reflexivity. Qed.
Lemma na_fetch_k0 : fetch_word SEGS (Z_to_bv 64 (BASE + NT_ca_k_ra)) = Some (Z_to_bv 32 0x00300713).
Proof. apply pa_fetch_pw. vm_compute. reflexivity. Qed.
Lemma na_fetch_k1 : fetch_word SEGS (Z_to_bv 64 (BASE + (NT_ca_k_ra + 4))) = Some (Z_to_bv 32 0x00400693).
Proof. apply pa_fetch_pw. vm_compute. reflexivity. Qed.
Lemma na_dec_a4 : decode_any (Z_to_bv 32 0x00300713) =
  Some (OpImm ALU_ADD (14%bv : bv 5) (0%bv : bv 5) (3%bv : bv 12), 4%Z).
Proof. lazymatch goal with |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true) end. Qed.
Lemma na_dec_a3 : decode_any (Z_to_bv 32 0x00400693) =
  Some (OpImm ALU_ADD (13%bv : bv 5) (0%bv : bv 5) (4%bv : bv 12), 4%Z).
Proof. lazymatch goal with |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true) end. Qed.
Lemma na_dec_jra : decode_any (Z_to_bv 32 0x0bc0006f) = Some (Jal (0%bv : bv 5) (0xbc%bv : bv 21), 4%Z).
Proof. lazymatch goal with |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true) end. Qed.
Lemma na_ecall_a4 : is_ecall (Z_to_bv 32 0x00300713) = false. Proof. vm_compute. reflexivity. Qed.
Lemma na_ecall_a3 : is_ecall (Z_to_bv 32 0x00400693) = false. Proof. vm_compute. reflexivity. Qed.
Lemma na_ecall_jra : is_ecall (Z_to_bv 32 0x0bc0006f) = false. Proof. vm_compute. reflexivity. Qed.

Section c.
Variable POST : ntcx -> world SEGS -> config -> Prop.
Hypothesis HX : nt_from SK B POST (nt_exit_inv B).
Variable cx : ntcx.
Variable fp : Z.
Hypothesis HB : nt_base SK B cx.

Definition K1 (f : nat) : Prop := forall k2 ly3 S3 W3 ms3 md3 c rest bs aoff aleft a,
  na_c1 SK B cx fp k2 ly3 S3 W3 ms3 md3 c rest bs f aoff aleft a -> SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Definition KS (f : nat) : Prop := forall k2 ly3 S3 W3 ms3 md3 c rest bs aoff aleft a,
  na_cs cx fp k2 ly3 S3 W3 ms3 md3 c rest bs f aoff aleft a -> SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Definition K3 (f g : nat) : Prop := forall k2 ly3 S3 W3 ms3 md3 c rest bs aoff aleft ioff ileft k al,
  na_c3 SK B cx fp k2 ly3 S3 W3 ms3 md3 c rest bs f g aoff aleft ioff ileft k al -> SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Definition K4 (f g : nat) : Prop := forall k2 ly3 S3 W3 ms3 md3 c rest bs aoff aleft ioff ileft k al,
  na_c4 cx fp k2 ly3 S3 W3 ms3 md3 c rest bs f g aoff aleft ioff ileft k al -> SRr SEGS W3 (mkCfg ms3 md3) (POST cx).


(* what a run that wrote nothing keeps of a cut *)
Lemma na_keep : forall k2 ly3 S3 W3 ms0 ms md0 md c rest bs a,
  na_core SK B cx fp k2 ly3 S3 W3 ms0 md0 c rest bs -> na_slots cx W3 ms0 -> na_bufs cx (rdW W3 (ms_mem ms0)) a ->
  ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms) md k2 ->
  ms_mem ms = ms_mem ms0 ->
  (forall r, In r [2%bv; 8%bv; 9%bv; 18%bv; 21%bv; 24%bv; 3%bv; 4%bv] -> getr (ms_regs ms) r = getr (ms_regs ms0) r) ->
  m_fds md = m_fds md0 -> m_fs md = m_fs md0 ->
  na_core SK B cx fp k2 ly3 S3 W3 ms md c rest bs /\ na_slots cx W3 ms /\ na_bufs cx (rdW W3 (ms_mem ms)) a.
Proof.
  intros k2 ly3 S3 W3 ms0 ms md0 md c rest bs a HC HSl HBF HJ Hm Hr Hfd Hfs.
  split; [exact (na_core_run cx fp k2 ly3 S3 W3 ms0 ms md0 md c rest bs HC HJ Hm Hr Hfd Hfs)|].
  split; [exact (na_slots_ms cx W3 ms0 ms HSl Hm)|]. rewrite Hm. exact HBF.
Qed.

Lemma na_wvb_fds : forall l X md, m_fds (with_vm_backing l X md) = m_fds md.
Proof. intros l X md. exact (proj1 (wvb_fds_fs l X md)). Qed.
Lemma na_wvb_fs : forall l X md, m_fs (with_vm_backing l X md) = m_fs md.
Proof. intros l X md. exact (proj2 (wvb_fds_fs l X md)). Qed.

Lemma na_shape : forall pc (rg : bvmap 5 word) mm, nt_shape pc (mkst rg (Z_to_bv 64 (BASE + pc)) mm (seg_rom SEGS)).
Proof. intros pc rg mm. unfold nt_shape. cbn. repeat split; reflexivity. Qed.

(* the step (+0x454 .. +0x46c): the next attribute and the bytes left, up to the `bge` *)
Lemma na_seg2 : forall f, K1 f -> KS f.
Proof.
  intros f HK1 k2 ly3 S3 W3 ms3 md3 c rest bs aoff aleft a
    (HC & HSl & Hsh & R26 & R22 & R25 & R20 & R13 & R14 & Ha0 & Hl & Hal & Hf & HM & HBF).
  na_open ms3 Hsh rg mm.
  pose proof HC as (HJ & HR & _ & _ & _ & _ & _ & _ & _ & HJB & _ & _ & _ & _ & _ & HBY & HBL & HCL & _).
  cbn [ms_mem ms_regs] in HJ, HR, HBY.
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & HGok & _).
  assert (Hlen0 : (length c <= 4096)%nat) by (unfold NL_CHUNK_MAX in HCL; exact HCL).
  pose proof (nt_rd16_range c aoff Ha0 ltac:(lia)) as Rl.
  pose proof (na_geom SK B LAWS cx fp k2 ly3 S3 W3 _ md3 c rest bs HB HC) as
    (_ & _ & _ & HF4 & HFc & _ & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof (nt_nl_align_ge (rd16 c aoff) ltac:(lia)) as Hal3.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  destruct (na_st1 cx fp k2 ly3 S3 W3 rg mm md3 c rest bs NT_astep aoff HB HC HSl R26 Ha0 ltac:(lia)) as [HS0 SHOK].
  remember (Eimg (Ereg rg (na_ext cx c aoff aoff))) as E eqn:HE.
  assert (HEI : img_env pa_val A_LIM E) by (rewrite HE; apply Eimg_env).
  assert (HAE : env_agree 40 (Ereg rg (na_ext cx c aoff aoff)) E)
    by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E21 : ew E 21 = w64 SHADOW_OFF) by (rewrite (na_ag_reg 40 rg _ E 21 21%bv ltac:(lia) HAE eq_refl); exact (proj1 (proj2 (proj2 (proj2 (proj2 HR)))))).
  assert (E26 : ew E 26 = w64 (nBUF cx fp + aoff)) by (rewrite (na_ag_reg 40 rg _ E 26 26%bv ltac:(lia) HAE eq_refl); exact R26).
  pose proof (st_ok_pi_set_reg E _ _ 25%bv (na_shx 26) HS0 ltac:(discriminate)
    ltac:(rewrite restrict_mkst_fx; cbn [ms_regs mkst]; rewrite R25, (na_shx_val E 26 (nBUF cx fp + aoff) E26 E21) by (unfold nBUF, NT_BUFOFF; lia); reflexivity)) as HS.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS. clear HS0.
  pose (RUNTO := paj_run_to_x SK B LAWS (n_G cx) HGok (n_XO cx) (n_OUT cx)).
  paj_run_to_tok RUNTO HS HJ SHOK na_span NA_bge.
  { na_awr0. }
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => remember Ex as E' eqn:HE' end.
  assert (HAE' : env_agree 40 (Ereg rg (na_ext cx c aoff aoff)) E')
    by (apply (na_ag_trans 40 _ E); [exact HAE | apply (na_ag_le 512); [lia | rewrite HE'; na_ag]]).
  assert (Hmem : ms_mem ms = mm)
    by (apply (na_frame_ro E _ _ _ HF); repeat (apply Forall_cons; [cbn; lia|]); apply Forall_nil).
  pmkst HS.
  na_reg HS (26%bv : bv 5) Q26. na_reg HS (22%bv : bv 5) Q22.
  pose proof (regs_kept_of_st_ok_pi E' _ _ rg _ [2%bv; 8%bv; 9%bv; 18%bv; 21%bv; 24%bv; 3%bv; 4%bv; 20%bv; 13%bv; 14%bv]
    HS (na_ag_le 40 32 _ _ ltac:(lia) HAE') ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  assert (F26 : ew E' 26 = w64 (nBUF cx fp + aoff)) by (rewrite (na_ag_reg 40 rg _ E' 26 26%bv ltac:(lia) HAE' eq_refl); exact R26).
  assert (F22 : ew E' 22 = w64 aleft) by (rewrite (na_ag_reg 40 rg _ E' 22 22%bv ltac:(lia) HAE' eq_refl); exact R22).
  assert (F20 : ew E' 20 = w64 131068) by (rewrite (na_ag_reg 40 rg _ E' 20 20%bv ltac:(lia) HAE' eq_refl); exact R20).
  assert (F32 : ew E' 32 = w64 (rd16 c aoff)) by (exact (na_ag_ext 40 rg _ E' 32 0 HAE' eq_refl ltac:(lia))).
  assert (UAL : U E' (SAlu ALU_AND (SOff 32 3) (SOff 20 0)) = nl_align (rd16 c aoff))
    by (apply (na_U_al E' 32 20 (rd16 c aoff) F32 ltac:(lia) F20)).
  assert (V26 : getr (ms_regs ms) 26 = w64 (nBUF cx fp + (aoff + nl_align (rd16 c aoff)))).
  { rewrite Q26, denot_lit_U. unfold w64. f_equal.
    rewrite (na_U_addp E' 26 (nBUF cx fp + aoff) _ F26) by (pose proof (U_range E' (SAlu ALU_AND (SOff 32 3) (SOff 20 0))); unfold nBUF, NT_BUFOFF, M64 in *; lia).
    rewrite UAL. lia. }
  assert (V22 : getr (ms_regs ms) 22 = w64 (aleft - nl_align (rd16 c aoff))).
  { rewrite Q22. apply na_denot_of_S.
    rewrite (na_S_subw E' 22 aleft _ F22) by (rewrite ?UAL; lia). rewrite UAL. reflexivity. }
  apply (na_c2_step SK B LAWS POST f cx fp HX HB HK1 k2 ly3 S3 W3 _ _ c rest bs
    (aoff + nl_align (rd16 c aoff)) (aleft - nl_align (rd16 c aoff)) a).
  split.
  { apply (na_core_run cx fp k2 ly3 S3 W3 _ _ md3 _ c rest bs HC); cbn [ms_mem ms_regs mkst].
    - exact HJ.
    - exact Hmem.
    - intros r Hr. apply KR. cbn in Hr |- *. tauto.
    - exact (proj1 (wvb_fds_fs _ _ _)).
    - exact (proj2 (wvb_fds_fs _ _ _)). }
  split; [apply (na_slots_ms cx W3 _ _ HSl); cbn [ms_mem mkst]; exact Hmem|].
  split; [unfold nt_shape; cbn; repeat split; reflexivity|].
  cbn [ms_regs ms_mem mkst].
  split; [exact V26|]. split; [exact V22|].
  split; [rewrite (KR 20%bv ltac:(cbn; tauto)); exact R20|].
  split; [rewrite (KR 13%bv ltac:(cbn; tauto)); exact R13|].
  split; [rewrite (KR 14%bv ltac:(cbn; tauto)); exact R14|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [intros H4; lia|].
  split; [exact HM|]. rewrite Hmem. exact HBF.
Qed.

(* the nested step (+0x400 .. +0x41c): the next nested attribute; then `blt a4, s7` back to the nested head
   (+0x3ac) or, the nested walk done, `j` to the outer step (+0x454) *)
Lemma na_seg4 : forall f g, KS f -> K3 f g -> K4 f g.
Proof.
  intros f g HKS HK3 k2 ly3 S3 W3 ms3 md3 c rest bs aoff aleft ioff ileft k al
    (HC & HSl & Hsh & R26 & R22 & R25 & R27 & R23 & R19 & R20 & R13 & R14 & Ha0 & Hl & Hal & Hio & Hioe & Hil & Hg
       & Hf & HM & HBF).
  na_open ms3 Hsh rg mm.
  pose proof HC as (HJ & HR & _ & _ & _ & _ & _ & _ & _ & HJB & _ & _ & _ & _ & _ & HBY & HBL & HCL & _).
  cbn [ms_mem ms_regs] in HJ, HR, HBY.
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & HGok & _).
  assert (Hlen0 : (length c <= 4096)%nat) by (unfold NL_CHUNK_MAX in HCL; exact HCL).
  pose proof (nt_rd16_range c ioff ltac:(lia) ltac:(lia)) as Rl.
  pose proof (nt_nl_align_ge (rd16 c ioff) ltac:(lia)) as Hal3.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof (na_geom SK B LAWS cx fp k2 ly3 S3 W3 _ md3 c rest bs HB HC) as
    (_ & _ & _ & HF4 & HFc & _ & _ & _ & _ & _ & _ & _ & _ & _).
  destruct (na_st3 cx fp k2 ly3 S3 W3 rg mm md3 c rest bs NT_istep aoff ioff HB HC HSl R26 R27 Ha0 Hio ltac:(lia))
    as [HS0 SHOK].
  remember (Eimg (Ereg rg (na_ext cx c aoff ioff))) as E eqn:HE.
  assert (HEI : img_env pa_val A_LIM E) by (rewrite HE; apply Eimg_env).
  assert (HAE : env_agree 40 (Ereg rg (na_ext cx c aoff ioff)) E)
    by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (R21 : getr rg 21 = w64 SHADOW_OFF) by exact (proj1 (proj2 (proj2 (proj2 (proj2 HR))))).
  assert (E21 : ew E 21 = w64 SHADOW_OFF) by (rewrite (na_ag_reg 40 rg _ E 21 21%bv ltac:(lia) HAE eq_refl); exact R21).
  assert (E26 : ew E 26 = w64 (nBUF cx fp + aoff)) by (rewrite (na_ag_reg 40 rg _ E 26 26%bv ltac:(lia) HAE eq_refl); exact R26).
  assert (E27 : ew E 27 = w64 (nBUF cx fp + ioff)) by (rewrite (na_ag_reg 40 rg _ E 27 27%bv ltac:(lia) HAE eq_refl); exact R27).
  pose proof (st_ok_pi_set_reg E _ _ 25%bv (na_shx 26) HS0 ltac:(discriminate)
    ltac:(rewrite restrict_mkst_fx; cbn [ms_regs mkst]; rewrite R25, (na_shx_val E 26 (nBUF cx fp + aoff) E26 E21) by (unfold nBUF, NT_BUFOFF; lia); reflexivity)) as HS1.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1. clear HS0.
  pose proof (st_ok_pi_set_reg E _ _ 19%bv (na_shx 27) HS1 ltac:(discriminate)
    ltac:(rewrite restrict_mkst_fx; cbn [ms_regs mkst]; rewrite R19, (na_shx_val E 27 (nBUF cx fp + ioff) E27 E21) by (unfold nBUF, NT_BUFOFF; lia); reflexivity)) as HS.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS. clear HS1.
  pose (RUN := paj_run_x SK B LAWS (n_G cx) HGok (n_XO cx) (n_OUT cx)).
  pose (RUNTO := paj_run_to_x SK B LAWS (n_G cx) HGok (n_XO cx) (n_OUT cx)).
  pose (BR := paj_branch (PI := PI)).
  paj_run_tok RUN HS HJ SHOK na_span.
  { na_awr0. }
  na_mem Hm1 HF mm. clear HF HFr HG.
  na_hae HS HAE HE E HAE1.
  assert (F14 : ew _ 14 = w64 3) by (rewrite (na_ag_reg 40 rg _ _ 14 14%bv ltac:(lia) HAE1 eq_refl); exact R14).
  assert (F23 : ew _ 23 = w64 ileft) by (rewrite (na_ag_reg 40 rg _ _ 23 23%bv ltac:(lia) HAE1 eq_refl); exact R23).
  assert (F20 : ew _ 20 = w64 131068) by (rewrite (na_ag_reg 40 rg _ _ 20 20%bv ltac:(lia) HAE1 eq_refl); exact R20).
  assert (F38 : ew _ 38 = w64 (rd16 c ioff)) by (exact (na_ag_ext 40 rg _ _ 38 6 HAE1 eq_refl ltac:(lia))).
  assert (UAL : U _ (SAlu ALU_AND (SOff 38 3) (SOff 20 0)) = nl_align (rd16 c ioff))
    by (apply (na_U_al _ 38 20 (rd16 c ioff) F38 ltac:(lia) F20)).
  assert (SS7 : Sg _ (SAluw ALU_SUB (SOff 23 0) (SAlu ALU_AND (SOff 38 3) (SOff 20 0))) = ileft - nl_align (rd16 c ioff))
    by (rewrite (na_S_subw _ 23 ileft _ F23) by (rewrite ?UAL; lia); rewrite UAL; reflexivity).
  assert (SA4 : Sg _ (SOff 14 0) = 3) by (apply (na_S_atom _ 14 3 F14); lia).
  clear F14 F23 F20 F38 UAL.
  psrr_branch_tok RUN BR HS SHOK na_span.
  - (* 3 < s7: the next nested attribute, back to the nested head *)
    rewrite na_branch_lt, SA4, SS7 in Hc. apply Z.ltb_lt in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK na_span NT_info.
    { na_awr0. }
    na_mem2 Hm2 HF Hm1 mm. clear HF HFr HG.
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => remember Ex as E2 eqn:HE2 end.
    assert (HAE' : env_agree 40 (Ereg rg (na_ext cx c aoff ioff)) E2)
      by (apply (na_ag_trans 40 _ E); [exact HAE | apply (na_ag_le 512); [lia | rewrite HE2; na_ag]]).
    pmkst HS.
    na_reg HS (27%bv : bv 5) Q27. na_reg HS (23%bv : bv 5) Q23. na_reg HS (25%bv : bv 5) Q25.
    pose proof (regs_kept_of_st_ok_pi E2 _ _ rg _ [2%bv; 8%bv; 9%bv; 18%bv; 21%bv; 24%bv; 3%bv; 4%bv; 20%bv; 13%bv; 14%bv; 26%bv; 22%bv]
      HS (na_ag_le 40 32 _ _ ltac:(lia) HAE') ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    assert (G21 : ew E2 21 = w64 SHADOW_OFF) by (rewrite (na_ag_reg 40 rg _ E2 21 21%bv ltac:(lia) HAE' eq_refl); exact R21).
    assert (G26 : ew E2 26 = w64 (nBUF cx fp + aoff)) by (rewrite (na_ag_reg 40 rg _ E2 26 26%bv ltac:(lia) HAE' eq_refl); exact R26).
    assert (G27 : ew E2 27 = w64 (nBUF cx fp + ioff)) by (rewrite (na_ag_reg 40 rg _ E2 27 27%bv ltac:(lia) HAE' eq_refl); exact R27).
    assert (G23 : ew E2 23 = w64 ileft) by (rewrite (na_ag_reg 40 rg _ E2 23 23%bv ltac:(lia) HAE' eq_refl); exact R23).
    assert (G20 : ew E2 20 = w64 131068) by (rewrite (na_ag_reg 40 rg _ E2 20 20%bv ltac:(lia) HAE' eq_refl); exact R20).
    assert (G38 : ew E2 38 = w64 (rd16 c ioff)) by (exact (na_ag_ext 40 rg _ E2 38 6 HAE' eq_refl ltac:(lia))).
    assert (UAL : U E2 (SAlu ALU_AND (SOff 38 3) (SOff 20 0)) = nl_align (rd16 c ioff))
      by (apply (na_U_al E2 38 20 (rd16 c ioff) G38 ltac:(lia) G20)).
    assert (V27 : getr (ms_regs ms0) 27 = w64 (nBUF cx fp + (ioff + nl_align (rd16 c ioff)))).
    { rewrite Q27, denot_lit_U. unfold w64. f_equal.
      rewrite (na_U_addp E2 27 (nBUF cx fp + ioff) _ G27)
        by (try rewrite UAL; unfold nBUF, NT_BUFOFF in *; lia).
      rewrite UAL. lia. }
    assert (V23 : getr (ms_regs ms0) 23 = w64 (ileft - nl_align (rd16 c ioff))).
    { rewrite Q23. apply na_denot_of_S.
      rewrite (na_S_subw E2 23 ileft _ G23) by (rewrite ?UAL; lia). rewrite UAL. reflexivity. }
    assert (V25 : getr (ms_regs ms0) 25 = w64 (SHADOW_OFF + (nBUF cx fp + aoff) / 8))
      by (rewrite Q25; apply (na_shx_val E2 26 _ G26 G21); unfold nBUF, NT_BUFOFF; lia).
    destruct (na_keep k2 ly3 S3 W3 _ (mkst (ms_regs ms0) (Z_to_bv 64 (BASE + 27476)) (ms_mem ms0) (seg_rom SEGS))
      md3 _ c rest bs (Attrs k al) HC HSl HBF HJ ltac:(cbn [ms_mem mkst]; exact Hm2)
      ltac:(intros r Hr; apply KR; cbn in Hr |- *; tauto) (eq_trans (na_wvb_fds _ _ _) (na_wvb_fds _ _ _)) (eq_trans (na_wvb_fs _ _ _) (na_wvb_fs _ _ _))) as (HC' & HSl' & HBF').
    apply (HK3 k2 ly3 S3 W3 _ _ c rest bs aoff aleft (ioff + nl_align (rd16 c ioff)) (ileft - nl_align (rd16 c ioff)) k al).
    split; [exact HC'|]. split; [exact HSl'|]. split; [exact (na_shape NT_info _ _)|].
    cbn [ms_regs ms_mem mkst].
    split; [rewrite (KR 26%bv ltac:(cbn; tauto)); exact R26|].
    split; [rewrite (KR 22%bv ltac:(cbn; tauto)); exact R22|].
    split; [exact V25|]. split; [exact V27|]. split; [exact V23|].
    split; [rewrite (KR 20%bv ltac:(cbn; tauto)); exact R20|].
    split; [rewrite (KR 13%bv ltac:(cbn; tauto)); exact R13|].
    split; [rewrite (KR 14%bv ltac:(cbn; tauto)); exact R14|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [lia|]. split; [lia|].
    split; [exact HM | exact HBF'].
  - (* s7 <= 3: the nested walk is done; `j` to the outer step *)
    rewrite na_branch_lt, SA4, SS7 in Hc. apply Z.ltb_ge in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK na_span NT_astep.
    { na_awr0. }
    na_mem2 Hm2 HF Hm1 mm. clear HF HFr HG.
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => remember Ex as E2 eqn:HE2 end.
    assert (HAE' : env_agree 40 (Ereg rg (na_ext cx c aoff ioff)) E2)
      by (apply (na_ag_trans 40 _ E); [exact HAE | apply (na_ag_le 512); [lia | rewrite HE2; na_ag]]).
    pmkst HS.
    na_reg HS (25%bv : bv 5) Q25.
    pose proof (regs_kept_of_st_ok_pi E2 _ _ rg _ [2%bv; 8%bv; 9%bv; 18%bv; 21%bv; 24%bv; 3%bv; 4%bv; 20%bv; 13%bv; 14%bv; 26%bv; 22%bv]
      HS (na_ag_le 40 32 _ _ ltac:(lia) HAE') ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    assert (G21 : ew E2 21 = w64 SHADOW_OFF) by (rewrite (na_ag_reg 40 rg _ E2 21 21%bv ltac:(lia) HAE' eq_refl); exact R21).
    assert (G26 : ew E2 26 = w64 (nBUF cx fp + aoff)) by (rewrite (na_ag_reg 40 rg _ E2 26 26%bv ltac:(lia) HAE' eq_refl); exact R26).
    assert (V25 : getr (ms_regs ms0) 25 = w64 (SHADOW_OFF + (nBUF cx fp + aoff) / 8))
      by (rewrite Q25; apply (na_shx_val E2 26 _ G26 G21); unfold nBUF, NT_BUFOFF; lia).
    destruct (na_keep k2 ly3 S3 W3 _ (mkst (ms_regs ms0) (Z_to_bv 64 (BASE + 27644)) (ms_mem ms0) (seg_rom SEGS))
      md3 _ c rest bs (Attrs k al) HC HSl HBF HJ ltac:(cbn [ms_mem mkst]; exact Hm2)
      ltac:(intros r Hr; apply KR; cbn in Hr |- *; tauto) (eq_trans (na_wvb_fds _ _ _) (na_wvb_fds _ _ _)) (eq_trans (na_wvb_fs _ _ _) (na_wvb_fs _ _ _))) as (HC' & HSl' & HBF').
    apply (HKS k2 ly3 S3 W3 _ _ c rest bs aoff aleft (Attrs k al)).
    split; [exact HC'|]. split; [exact HSl'|]. split; [exact (na_shape NT_astep _ _)|].
    cbn [ms_regs ms_mem mkst].
    split; [rewrite (KR 26%bv ltac:(cbn; tauto)); exact R26|].
    split; [rewrite (KR 22%bv ltac:(cbn; tauto)); exact R22|].
    split; [exact V25|].
    split; [rewrite (KR 20%bv ltac:(cbn; tauto)); exact R20|].
    split; [rewrite (KR 13%bv ltac:(cbn; tauto)); exact R13|].
    split; [rewrite (KR 14%bv ltac:(cbn; tauto)); exact R14|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [|exact HBF'].
    rewrite HM, (nt_ks_small g (ioff + nl_align (rd16 c ioff)) (ileft - nl_align (rd16 c ioff)) k) by lia. reflexivity.
Qed.

(* the return from the alias call: a4 := 3, a3 := 4, `j` to the outer step (+0x390 .. +0x398) *)
Lemma na_ret_alias : forall f, KS f -> forall k2 ly3 S3 W3 rg mm md3 c rest bs aoff aleft a,
  na_core SK B cx fp k2 ly3 S3 W3 (mkst rg (w64 (BASE + NT_ca_a_ra)) mm (seg_rom SEGS)) md3 c rest bs ->
  na_slots cx W3 (mkst rg (w64 (BASE + NT_ca_a_ra)) mm (seg_rom SEGS)) ->
  getr rg 26 = w64 (nBUF cx fp + aoff) -> getr rg 22 = w64 aleft ->
  getr rg 25 = w64 (SHADOW_OFF + (nBUF cx fp + aoff) / 8) -> getr rg 20 = w64 131068 ->
  0 <= aoff -> 4 <= rd16 c aoff <= aleft -> aoff + aleft <= Z.of_nat (length c) -> (Z.to_nat aleft <= f)%nat ->
  talk_attrs (n_K0 cx) = attr_scan f c (aoff + nl_align (rd16 c aoff)) (aleft - nl_align (rd16 c aoff)) a ->
  na_bufs cx (rdW W3 mm) a ->
  SRr SEGS W3 (mkCfg (mkst rg (w64 (BASE + NT_ca_a_ra)) mm (seg_rom SEGS)) md3) (POST cx).
Proof.
  intros f HKS k2 ly3 S3 W3 rg mm md3 c rest bs aoff aleft a HC HSl R26 R22 R25 R20 Ha0 Hl Hal Hf HM HBF.
  pose proof HC as (_ & HR & _). cbn [ms_regs mkst] in HR.
  eapply (SRr_step SEGS pa_wx W3); [reflexivity | |].
  { rewrite restrict_mkst_fx. eapply step_addi; [exact na_fetch_r0 | exact na_ecall_a4 | exact na_dec_a4]. }
  intros md' Hsame. rewrite (same_but_materialized_wvb md3 md' Hsame). rewrite unrestrict_mkst_mrestrict.
  replace (bv_eqb (14%bv : bv 5) 0) with false by reflexivity.
  rewrite (na_pc_addw NT_ca_a_ra 4) by (unfold NT_ca_a_ra, AF_nl_talk; lia).
  eapply (SRr_step SEGS pa_wx W3); [reflexivity | |].
  { rewrite restrict_mkst_fx. eapply step_addi; [exact na_fetch_r1 | exact na_ecall_a3 | exact na_dec_a3]. }
  intros md'' Hsame2. rewrite (same_but_materialized_wvb _ md'' Hsame2). rewrite unrestrict_mkst_mrestrict.
  replace (bv_eqb (13%bv : bv 5) 0) with false by reflexivity.
  rewrite (na_pc_addw (NT_ca_a_ra + 4) 4) by (unfold NT_ca_a_ra, AF_nl_talk; lia).
  eapply (SRr_step SEGS pa_wx W3); [reflexivity | |].
  { rewrite restrict_mkst_fx. eapply step_jal_x0; [exact na_fetch_r2 | exact na_ecall_jra | exact na_dec_jra]. }
  intros md3' Hsame3. rewrite (same_but_materialized_wvb _ md3' Hsame3). rewrite unrestrict_mkst_mrestrict.
  change (bv_signed (0xbc%bv : bv 21)) with 0xbc. unfold btgt.
  rewrite (na_pc_addw (NT_ca_a_ra + 4 + 4) 0xbc) by (unfold NT_ca_a_ra, AF_nl_talk; lia).
  change (NT_ca_a_ra + 4 + 4 + 0xbc) with NT_astep.
  apply (HKS k2 ly3 S3 W3 _ _ c rest bs aoff aleft a).
  split.
  { apply (na_core_md SK B LAWS). apply (na_core_md SK B LAWS). apply (na_core_md SK B LAWS).
    apply (na_core_ms SK B cx fp k2 ly3 S3 W3 _ _ md3 c rest bs HC); [reflexivity|].
    unfold nt_regs. cbn [ms_regs mkst]. rewrite !getr_other by reg_neq_tac. exact HR. }
  split; [apply (na_slots_ms cx W3 _ _ HSl); reflexivity|].
  split; [exact (na_shape NT_astep _ _)|].
  cbn [ms_regs ms_mem mkst].
  split; [rewrite !getr_other by reg_neq_tac; exact R26|].
  split; [rewrite !getr_other by reg_neq_tac; exact R22|].
  split; [rewrite !getr_other by reg_neq_tac; exact R25|].
  split; [rewrite !getr_other by reg_neq_tac; exact R20|].
  split; [getr_resolve; reflexivity|].
  split; [rewrite getr_other by reg_neq_tac; getr_resolve; reflexivity|].
  tauto.
Qed.

(* the return from the kind call: a4 := 3, a3 := 4, on to the nested step (+0x3f8 .. +0x3fc) *)
Lemma na_ret_kind : forall f g, K4 f g -> forall k2 ly3 S3 W3 rg mm md3 c rest bs aoff aleft ioff ileft k al,
  na_core SK B cx fp k2 ly3 S3 W3 (mkst rg (w64 (BASE + NT_ca_k_ra)) mm (seg_rom SEGS)) md3 c rest bs ->
  na_slots cx W3 (mkst rg (w64 (BASE + NT_ca_k_ra)) mm (seg_rom SEGS)) ->
  getr rg 26 = w64 (nBUF cx fp + aoff) -> getr rg 22 = w64 aleft ->
  getr rg 25 = w64 (SHADOW_OFF + (nBUF cx fp + aoff) / 8) ->
  getr rg 27 = w64 (nBUF cx fp + ioff) -> getr rg 23 = w64 ileft ->
  getr rg 19 = w64 (SHADOW_OFF + (nBUF cx fp + ioff) / 8) -> getr rg 20 = w64 131068 ->
  0 <= aoff -> 8 <= rd16 c aoff <= aleft -> aoff + aleft <= Z.of_nat (length c) ->
  aoff + 4 <= ioff -> ioff + ileft = aoff + rd16 c aoff -> 4 <= rd16 c ioff <= ileft -> (Z.to_nat ileft <= g)%nat ->
  aleft <= Z.of_nat f ->
  talk_attrs (n_K0 cx) =
    attr_scan f c (aoff + nl_align (rd16 c aoff)) (aleft - nl_align (rd16 c aoff))
      (Attrs (kind_scan g c (ioff + nl_align (rd16 c ioff)) (ileft - nl_align (rd16 c ioff)) k) al) ->
  na_bufs cx (rdW W3 mm) (Attrs k al) ->
  SRr SEGS W3 (mkCfg (mkst rg (w64 (BASE + NT_ca_k_ra)) mm (seg_rom SEGS)) md3) (POST cx).
Proof.
  intros f g HK4 k2 ly3 S3 W3 rg mm md3 c rest bs aoff aleft ioff ileft k al HC HSl R26 R22 R25 R27 R23 R19 R20
    Ha0 Hl Hal Hio Hioe Hil Hg Hf HM HBF.
  pose proof HC as (_ & HR & _). cbn [ms_regs mkst] in HR.
  eapply (SRr_step SEGS pa_wx W3); [reflexivity | |].
  { rewrite restrict_mkst_fx. eapply step_addi; [exact na_fetch_k0 | exact na_ecall_a4 | exact na_dec_a4]. }
  intros md' Hsame. rewrite (same_but_materialized_wvb md3 md' Hsame). rewrite unrestrict_mkst_mrestrict.
  replace (bv_eqb (14%bv : bv 5) 0) with false by reflexivity.
  rewrite (na_pc_addw NT_ca_k_ra 4) by (unfold NT_ca_k_ra, AF_nl_talk; lia).
  eapply (SRr_step SEGS pa_wx W3); [reflexivity | |].
  { rewrite restrict_mkst_fx. eapply step_addi; [exact na_fetch_k1 | exact na_ecall_a3 | exact na_dec_a3]. }
  intros md'' Hsame2. rewrite (same_but_materialized_wvb _ md'' Hsame2). rewrite unrestrict_mkst_mrestrict.
  replace (bv_eqb (13%bv : bv 5) 0) with false by reflexivity.
  rewrite (na_pc_addw (NT_ca_k_ra + 4) 4) by (unfold NT_ca_k_ra, AF_nl_talk; lia).
  change (NT_ca_k_ra + 4 + 4) with NT_istep.
  apply (HK4 k2 ly3 S3 W3 _ _ c rest bs aoff aleft ioff ileft k al).
  split.
  { apply (na_core_md SK B LAWS). apply (na_core_md SK B LAWS).
    apply (na_core_ms SK B cx fp k2 ly3 S3 W3 _ _ md3 c rest bs HC); [reflexivity|].
    unfold nt_regs. cbn [ms_regs mkst]. rewrite !getr_other by reg_neq_tac. exact HR. }
  split; [apply (na_slots_ms cx W3 _ _ HSl); reflexivity|].
  split; [exact (na_shape NT_istep _ _)|].
  cbn [ms_regs ms_mem mkst].
  split; [rewrite !getr_other by reg_neq_tac; exact R26|].
  split; [rewrite !getr_other by reg_neq_tac; exact R22|].
  split; [rewrite !getr_other by reg_neq_tac; exact R25|].
  split; [rewrite !getr_other by reg_neq_tac; exact R27|].
  split; [rewrite !getr_other by reg_neq_tac; exact R23|].
  split; [rewrite !getr_other by reg_neq_tac; exact R19|].
  split; [rewrite !getr_other by reg_neq_tac; exact R20|].
  split; [getr_resolve; reflexivity|].
  split; [rewrite getr_other by reg_neq_tac; getr_resolve; reflexivity|].
  tauto.
Qed.

Lemma na_pc_copy_attr : Z_to_bv 64 (pa_sigma LS_copy_attr) = w64 (BASE + AF_copy_attr).
Proof. rewrite (lv_sigma LV), (lv_text LV). reflexivity. Qed.

(* the nested head (+0x3ac .. +0x3e4): the nested attribute's two bounds and its kind test; the bounds end the
   nested walk (`j` to the outer step), a type other than IFLA_INFO_KIND goes to the nested step, and the kind is
   copied by copy_attr (+0x3f4) into the kind buffer *)
Lemma na_seg3 : forall f g, KS f -> K4 f g -> K3 f (S g).
Proof.
  intros f g HKS HK4 k2 ly3 S3 W3 ms3 md3 c rest bs aoff aleft ioff ileft k al
    (HC & HSl & Hsh & R26 & R22 & R25 & R27 & R23 & R20 & R13 & R14 & Ha0 & Hl & Hal & Hio & Hioe & Hil4 & Hg
       & Hf & HM & HBF).
  na_open ms3 Hsh rg mm.
  pose proof HC as (HJ & HR & _ & _ & _ & _ & _ & _ & _ & HJB & _ & _ & _ & _ & _ & HBY & HBL & HCL & _).
  cbn [ms_mem ms_regs] in HJ, HR, HBY.
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & HGok & _).
  assert (Hlen0 : (length c <= 4096)%nat) by (unfold NL_CHUNK_MAX in HCL; exact HCL).
  pose proof (nt_rd16_range c ioff ltac:(lia) ltac:(lia)) as Rl.
  pose proof (nt_rd16_range c (ioff + 2) ltac:(lia) ltac:(lia)) as Rt.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof (na_geom SK B LAWS cx fp k2 ly3 S3 W3 _ md3 c rest bs HB HC) as
    (_ & _ & _ & HF4 & HFc & _ & _ & _ & _ & _ & _ & _ & _ & _).
  destruct (na_st3 cx fp k2 ly3 S3 W3 rg mm md3 c rest bs NT_info aoff ioff HB HC HSl R26 R27 Ha0 Hio ltac:(lia))
    as [HS0 SHOK].
  remember (Eimg (Ereg rg (na_ext cx c aoff ioff))) as E eqn:HE.
  assert (HEI : img_env pa_val A_LIM E) by (rewrite HE; apply Eimg_env).
  assert (HAE : env_agree 40 (Ereg rg (na_ext cx c aoff ioff)) E)
    by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (R21 : getr rg 21 = w64 SHADOW_OFF) by exact (proj1 (proj2 (proj2 (proj2 (proj2 HR))))).
  assert (E21 : ew E 21 = w64 SHADOW_OFF) by (rewrite (na_ag_reg 40 rg _ E 21 21%bv ltac:(lia) HAE eq_refl); exact R21).
  assert (E26 : ew E 26 = w64 (nBUF cx fp + aoff)) by (rewrite (na_ag_reg 40 rg _ E 26 26%bv ltac:(lia) HAE eq_refl); exact R26).
  pose proof (st_ok_pi_set_reg E _ _ 25%bv (na_shx 26) HS0 ltac:(discriminate)
    ltac:(rewrite restrict_mkst_fx; cbn [ms_regs mkst]; rewrite R25, (na_shx_val E 26 (nBUF cx fp + aoff) E26 E21) by (unfold nBUF, NT_BUFOFF; lia); reflexivity)) as HS.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS. clear HS0.
  pose (RUN := paj_run_x SK B LAWS (n_G cx) HGok (n_XO cx) (n_OUT cx)).
  pose (RUNTO := paj_run_to_x SK B LAWS (n_G cx) HGok (n_XO cx) (n_OUT cx)).
  pose (BR := paj_branch (PI := PI)).
  assert (U38 : forall E', env_agree 40 (Ereg rg (na_ext cx c aoff ioff)) E' -> U E' (SOff 38 0) = rd16 c ioff)
    by (intros E' HA'; apply (U_atom E' 38); [exact (na_ag_ext 40 rg _ E' 38 6 HA' eq_refl ltac:(lia)) | lia]).
  assert (U39 : forall E', env_agree 40 (Ereg rg (na_ext cx c aoff ioff)) E' -> U E' (SOff 39 0) = rd16 c (ioff + 2))
    by (intros E' HA'; apply (U_atom E' 39); [exact (na_ag_ext 40 rg _ E' 39 7 HA' eq_refl ltac:(lia)) | lia]).
  assert (U13 : forall E', env_agree 40 (Ereg rg (na_ext cx c aoff ioff)) E' -> U E' (SOff 13 0) = 4)
    by (intros E' HA'; apply (U_atom E' 13); [rewrite (na_ag_reg 40 rg _ E' 13 13%bv ltac:(lia) HA' eq_refl); exact R13 | lia]).
  assert (U23 : forall E', env_agree 40 (Ereg rg (na_ext cx c aoff ioff)) E' -> U E' (SOff 23 0) = ileft)
    by (intros E' HA'; apply (U_atom E' 23); [rewrite (na_ag_reg 40 rg _ E' 23 23%bv ltac:(lia) HA' eq_refl); exact R23 | lia]).
  (* the state after the final run of a path, at a cut: registers and memory *)
  paj_run_tok RUN HS HJ SHOK na_span.
  { na_awr0. }
  na_mem Hm1 HF mm. clear HF HFr HG.
  na_hae HS HAE HE E HAE1.
  psrr_branch_tok RUN BR HS SHOK na_span.
  - (* the nested length is under 4: the nested walk ends *)
    rewrite branch_ltu_U, (U38 _ HAE1), (U13 _ HAE1) in Hc. apply Z.ltb_lt in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK na_span NT_astep.
    { na_awr0. }
    na_mem2 Hm2 HF Hm1 mm. clear HF HFr HG.
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => remember Ex as E2 eqn:HE2 end.
    assert (HAE' : env_agree 40 (Ereg rg (na_ext cx c aoff ioff)) E2)
      by (apply (na_ag_trans 40 _ E); [exact HAE | apply (na_ag_le 512); [lia | rewrite HE2; na_ag]]).
    pmkst HS.
    na_reg HS (25%bv : bv 5) Q25.
    pose proof (regs_kept_of_st_ok_pi E2 _ _ rg _ [2%bv; 8%bv; 9%bv; 18%bv; 21%bv; 24%bv; 3%bv; 4%bv; 20%bv; 13%bv; 14%bv; 26%bv; 22%bv]
      HS (na_ag_le 40 32 _ _ ltac:(lia) HAE') ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    assert (G21 : ew E2 21 = w64 SHADOW_OFF) by (rewrite (na_ag_reg 40 rg _ E2 21 21%bv ltac:(lia) HAE' eq_refl); exact R21).
    assert (G26 : ew E2 26 = w64 (nBUF cx fp + aoff)) by (rewrite (na_ag_reg 40 rg _ E2 26 26%bv ltac:(lia) HAE' eq_refl); exact R26).
    assert (V25 : getr (ms_regs ms0) 25 = w64 (SHADOW_OFF + (nBUF cx fp + aoff) / 8))
      by (rewrite Q25; apply (na_shx_val E2 26 _ G26 G21); unfold nBUF, NT_BUFOFF; lia).
    destruct (na_keep k2 ly3 S3 W3 _ (mkst (ms_regs ms0) (Z_to_bv 64 (BASE + 27644)) (ms_mem ms0) (seg_rom SEGS))
      md3 _ c rest bs (Attrs k al) HC HSl HBF HJ ltac:(cbn [ms_mem mkst]; exact Hm2)
      ltac:(intros r Hr; apply KR; cbn in Hr |- *; tauto)
      (eq_trans (na_wvb_fds _ _ _) (na_wvb_fds _ _ _)) (eq_trans (na_wvb_fs _ _ _) (na_wvb_fs _ _ _))) as (HC' & HSl' & HBF').
    apply (HKS k2 ly3 S3 W3 _ _ c rest bs aoff aleft (Attrs k al)).
    split; [exact HC'|]. split; [exact HSl'|]. split; [exact (na_shape NT_astep _ _)|].
    cbn [ms_regs ms_mem mkst].
    split; [rewrite (KR 26%bv ltac:(cbn; tauto)); exact R26|].
    split; [rewrite (KR 22%bv ltac:(cbn; tauto)); exact R22|].
    split; [exact V25|].
    split; [rewrite (KR 20%bv ltac:(cbn; tauto)); exact R20|].
    split; [rewrite (KR 13%bv ltac:(cbn; tauto)); exact R13|].
    split; [rewrite (KR 14%bv ltac:(cbn; tauto)); exact R14|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [|exact HBF'].
    rewrite HM, (nt_ks_stop g ioff ileft k) by (try lia; apply orb_true_iff; left; apply Z.ltb_lt; lia). reflexivity.
  - rewrite branch_ltu_U, (U38 _ HAE1), (U13 _ HAE1) in Hc. apply Z.ltb_ge in Hc.
    paj_run_tok RUN HS HJ SHOK na_span.
    { na_awr0. }
    na_mem2 Hm2 HF Hm1 mm. clear HF HFr HG.
    na_hae HS HAE HE E HAE2.
    psrr_branch_tok RUN BR HS SHOK na_span.
    + (* the bytes left are under the nested length: the nested walk ends *)
      rewrite branch_ltu_U, (U23 _ HAE2), (U38 _ HAE2) in Hc0. apply Z.ltb_lt in Hc0.
      paj_run_to_tok RUNTO HS HJ SHOK na_span NT_astep.
      { na_awr0. }
      na_mem2 Hm3 HF Hm2 mm. clear HF HFr HG.
      lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => remember Ex as E2 eqn:HE2 end.
      assert (HAE' : env_agree 40 (Ereg rg (na_ext cx c aoff ioff)) E2)
        by (apply (na_ag_trans 40 _ E); [exact HAE | apply (na_ag_le 512); [lia | rewrite HE2; na_ag]]).
      pmkst HS.
      na_reg HS (25%bv : bv 5) Q25.
      pose proof (regs_kept_of_st_ok_pi E2 _ _ rg _ [2%bv; 8%bv; 9%bv; 18%bv; 21%bv; 24%bv; 3%bv; 4%bv; 20%bv; 13%bv; 14%bv; 26%bv; 22%bv]
        HS (na_ag_le 40 32 _ _ ltac:(lia) HAE') ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      assert (G21 : ew E2 21 = w64 SHADOW_OFF) by (rewrite (na_ag_reg 40 rg _ E2 21 21%bv ltac:(lia) HAE' eq_refl); exact R21).
      assert (G26 : ew E2 26 = w64 (nBUF cx fp + aoff)) by (rewrite (na_ag_reg 40 rg _ E2 26 26%bv ltac:(lia) HAE' eq_refl); exact R26).
      assert (V25 : getr (ms_regs ms1) 25 = w64 (SHADOW_OFF + (nBUF cx fp + aoff) / 8))
        by (rewrite Q25; apply (na_shx_val E2 26 _ G26 G21); unfold nBUF, NT_BUFOFF; lia).
      destruct (na_keep k2 ly3 S3 W3 _ (mkst (ms_regs ms1) (Z_to_bv 64 (BASE + 27644)) (ms_mem ms1) (seg_rom SEGS))
        md3 _ c rest bs (Attrs k al) HC HSl HBF HJ ltac:(cbn [ms_mem mkst]; exact Hm3)
        ltac:(intros r Hr; apply KR; cbn in Hr |- *; tauto)
        (eq_trans (na_wvb_fds _ _ _) (eq_trans (na_wvb_fds _ _ _) (na_wvb_fds _ _ _)))
        (eq_trans (na_wvb_fs _ _ _) (eq_trans (na_wvb_fs _ _ _) (na_wvb_fs _ _ _)))) as (HC' & HSl' & HBF').
      apply (HKS k2 ly3 S3 W3 _ _ c rest bs aoff aleft (Attrs k al)).
      split; [exact HC'|]. split; [exact HSl'|]. split; [exact (na_shape NT_astep _ _)|].
      cbn [ms_regs ms_mem mkst].
      split; [rewrite (KR 26%bv ltac:(cbn; tauto)); exact R26|].
      split; [rewrite (KR 22%bv ltac:(cbn; tauto)); exact R22|].
      split; [exact V25|].
      split; [rewrite (KR 20%bv ltac:(cbn; tauto)); exact R20|].
      split; [rewrite (KR 13%bv ltac:(cbn; tauto)); exact R13|].
      split; [rewrite (KR 14%bv ltac:(cbn; tauto)); exact R14|].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [|exact HBF'].
      rewrite HM, (nt_ks_stop g ioff ileft k) by (try lia; apply orb_true_iff; right; apply Z.ltb_lt; lia). reflexivity.
    + rewrite branch_ltu_U, (U23 _ HAE2), (U38 _ HAE2) in Hc0. apply Z.ltb_ge in Hc0.
      paj_run_tok RUN HS HJ SHOK na_span.
      { na_awr0. }
      na_mem2 Hm3 HF Hm2 mm. clear HF HFr HG.
      na_hae HS HAE HE E HAE3.
      psrr_branch_tok RUN BR HS SHOK na_span.
      * (* a type other than IFLA_INFO_KIND: on to the nested step *)
        rewrite branch_ne_U, (U39 _ HAE3), U_lit in Hc1 by lia. apply negb_true_iff, Z.eqb_neq in Hc1.
        paj_run_to_tok RUNTO HS HJ SHOK na_span NT_istep.
        { na_awr0. }
        na_mem2 Hm4 HF Hm3 mm. clear HF HFr HG.
        lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => remember Ex as E2 eqn:HE2 end.
        assert (HAE' : env_agree 40 (Ereg rg (na_ext cx c aoff ioff)) E2)
          by (apply (na_ag_trans 40 _ E); [exact HAE | apply (na_ag_le 512); [lia | rewrite HE2; na_ag]]).
        pmkst HS.
        na_reg HS (25%bv : bv 5) Q25. na_reg HS (19%bv : bv 5) Q19.
        pose proof (regs_kept_of_st_ok_pi E2 _ _ rg _ [2%bv; 8%bv; 9%bv; 18%bv; 21%bv; 24%bv; 3%bv; 4%bv; 20%bv; 13%bv; 14%bv; 26%bv; 22%bv; 27%bv; 23%bv]
          HS (na_ag_le 40 32 _ _ ltac:(lia) HAE') ltac:(vm_compute; reflexivity)) as KR.
        cbn [ms_regs restrict] in KR.
        assert (G21 : ew E2 21 = w64 SHADOW_OFF) by (rewrite (na_ag_reg 40 rg _ E2 21 21%bv ltac:(lia) HAE' eq_refl); exact R21).
        assert (G26 : ew E2 26 = w64 (nBUF cx fp + aoff)) by (rewrite (na_ag_reg 40 rg _ E2 26 26%bv ltac:(lia) HAE' eq_refl); exact R26).
        assert (G27 : ew E2 27 = w64 (nBUF cx fp + ioff)) by (rewrite (na_ag_reg 40 rg _ E2 27 27%bv ltac:(lia) HAE' eq_refl); exact R27).
        assert (V25 : getr (ms_regs ms2) 25 = w64 (SHADOW_OFF + (nBUF cx fp + aoff) / 8))
          by (rewrite Q25; apply (na_shx_val E2 26 _ G26 G21); unfold nBUF, NT_BUFOFF; lia).
        assert (V19 : getr (ms_regs ms2) 19 = w64 (SHADOW_OFF + (nBUF cx fp + ioff) / 8))
          by (rewrite Q19; apply (na_shx_val E2 27 _ G27 G21); unfold nBUF, NT_BUFOFF; lia).
        destruct (na_keep k2 ly3 S3 W3 _ (mkst (ms_regs ms2) (Z_to_bv 64 (BASE + 27560)) (ms_mem ms2) (seg_rom SEGS))
          md3 _ c rest bs (Attrs k al) HC HSl HBF HJ ltac:(cbn [ms_mem mkst]; exact Hm4)
          ltac:(intros r Hr; apply KR; cbn in Hr |- *; tauto)
          (eq_trans (na_wvb_fds _ _ _) (eq_trans (na_wvb_fds _ _ _) (eq_trans (na_wvb_fds _ _ _) (na_wvb_fds _ _ _))))
          (eq_trans (na_wvb_fs _ _ _) (eq_trans (na_wvb_fs _ _ _) (eq_trans (na_wvb_fs _ _ _) (na_wvb_fs _ _ _)))))
          as (HC' & HSl' & HBF').
        apply (HK4 k2 ly3 S3 W3 _ _ c rest bs aoff aleft ioff ileft k al).
        split; [exact HC'|]. split; [exact HSl'|]. split; [exact (na_shape NT_istep _ _)|].
        cbn [ms_regs ms_mem mkst].
        split; [rewrite (KR 26%bv ltac:(cbn; tauto)); exact R26|].
        split; [rewrite (KR 22%bv ltac:(cbn; tauto)); exact R22|].
        split; [exact V25|].
        split; [rewrite (KR 27%bv ltac:(cbn; tauto)); exact R27|].
        split; [rewrite (KR 23%bv ltac:(cbn; tauto)); exact R23|].
        split; [exact V19|].
        split; [rewrite (KR 20%bv ltac:(cbn; tauto)); exact R20|].
        split; [rewrite (KR 13%bv ltac:(cbn; tauto)); exact R13|].
        split; [rewrite (KR 14%bv ltac:(cbn; tauto)); exact R14|].
        split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
        split; [lia|].
        split; [|exact HBF'].
        rewrite HM, (nt_ks_step g ioff ileft k) by lia.
        replace (rd16 c (ioff + 2) =? 1) with false by (symmetry; apply Z.eqb_neq; exact Hc1). reflexivity.
      * (* IFLA_INFO_KIND: copy_attr into the kind buffer *)
        rewrite branch_ne_U, (U39 _ HAE3), U_lit in Hc1 by lia. apply negb_false_iff, Z.eqb_eq in Hc1.
        paj_run_tok RUN HS HJ SHOK na_span.
        { na_awr0. }
        na_mem2 Hm4 HF Hm3 mm. clear HF HFr HG.
        lazymatch type of HS with st_ok _ ?Ex _ _ => remember Ex as E2 eqn:HE2 end.
        assert (HAE' : env_agree 40 (Ereg rg (na_ext cx c aoff ioff)) E2)
          by (apply (na_ag_trans 40 _ E); [exact HAE | apply (na_ag_le 512); [lia | rewrite HE2; na_ag]]).
        assert (HEIk : img_env pa_val A_LIM E2) by (first [assumption | rewrite HE2; assumption]).
        pmkst HS. rewrite na_pc_copy_attr.
        na_reg HS (10%bv : bv 5) Q10. na_reg HS (11%bv : bv 5) Q11. na_reg HS (12%bv : bv 5) Q12.
        na_reg HS (1%bv : bv 5) Q1. na_reg HS (25%bv : bv 5) Q25. na_reg HS (19%bv : bv 5) Q19.
        pose proof (regs_kept_of_st_ok SEGS E2 _ _ rg _ [2%bv; 8%bv; 9%bv; 18%bv; 21%bv; 24%bv; 3%bv; 4%bv; 20%bv; 26%bv; 22%bv; 27%bv; 23%bv]
          HS (na_ag_le 40 32 _ _ ltac:(lia) HAE') ltac:(vm_compute; reflexivity)) as KR.
        cbn [ms_regs restrict] in KR.
        assert (G21 : ew E2 21 = w64 SHADOW_OFF) by (rewrite (na_ag_reg 40 rg _ E2 21 21%bv ltac:(lia) HAE' eq_refl); exact R21).
        assert (G26 : ew E2 26 = w64 (nBUF cx fp + aoff)) by (rewrite (na_ag_reg 40 rg _ E2 26 26%bv ltac:(lia) HAE' eq_refl); exact R26).
        assert (G27 : ew E2 27 = w64 (nBUF cx fp + ioff)) by (rewrite (na_ag_reg 40 rg _ E2 27 27%bv ltac:(lia) HAE' eq_refl); exact R27).
        assert (G36 : ew E2 36 = w64 (n_kind cx)) by (exact (na_ag_ext 40 rg _ E2 36 4 HAE' eq_refl ltac:(lia))).
        assert (G37 : ew E2 37 = w64 (n_kindn cx)) by (exact (na_ag_ext 40 rg _ E2 37 5 HAE' eq_refl ltac:(lia))).
        assert (V25 : getr (ms_regs ms2) 25 = w64 (SHADOW_OFF + (nBUF cx fp + aoff) / 8))
          by (rewrite Q25; apply (na_shx_val E2 26 _ G26 G21); unfold nBUF, NT_BUFOFF; lia).
        assert (V19 : getr (ms_regs ms2) 19 = w64 (SHADOW_OFF + (nBUF cx fp + ioff) / 8))
          by (rewrite Q19; apply (na_shx_val E2 27 _ G27 G21); unfold nBUF, NT_BUFOFF; lia).
        destruct (na_keep k2 ly3 S3 W3 _ (mkst (ms_regs ms2) (w64 (BASE + AF_copy_attr)) (ms_mem ms2) (seg_rom SEGS))
          md3 _ c rest bs (Attrs k al) HC HSl HBF HJ ltac:(cbn [ms_mem mkst]; exact Hm4)
          ltac:(intros r Hr; apply KR; cbn in Hr |- *; tauto)
          (eq_trans (na_wvb_fds _ _ _) (eq_trans (na_wvb_fds _ _ _) (eq_trans (na_wvb_fds _ _ _) (na_wvb_fds _ _ _))))
          (eq_trans (na_wvb_fs _ _ _) (eq_trans (na_wvb_fs _ _ _) (eq_trans (na_wvb_fs _ _ _) (na_wvb_fs _ _ _)))))
          as (HC' & HSl' & HBF').
        apply (na_call SK B LAWS LV TB HSEGS RELRO_IMG CA false cx fp k2 ly3 S3 W3 (ms_regs ms2) (ms_mem ms2) _
          c rest bs ioff NT_ca_k_ra k al (POST cx) HB HC' HBF').
        -- rewrite Q10. exact (sv_off0 E2 27 _ G27).
        -- rewrite Q11. exact (sv_off0 E2 36 _ G36).
        -- rewrite Q12. exact (sv_off0 E2 37 _ G37).
        -- rewrite Q1. exact (codeptr_val E2 _ HEIk).
        -- unfold NT_ca_k_ra, AF_nl_talk; lia.
        -- reflexivity.
        -- lia.
        -- lia.
        -- lia.
        -- intros ly2 S2 W2 regs2 mem2 md2 HC2 HAP HKS2 HBF2.
           apply (na_ret_kind f g HK4 k2 ly2 S2 W2 regs2 mem2 md2 c rest bs aoff aleft ioff ileft
             (Some (slice c (ioff + RTA_HDR) (rd16 c ioff - RTA_HDR))) al HC2).
           ++ destruct HSl' as (SA & SAN). unfold na_slots.
              pose proof (na_geom SK B LAWS cx fp k2 ly3 S3 W3 _ md3 c rest bs HB HC) as
                (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & _).
              split; [apply (na_nt_at_kept W3 W2 _ _ _ _ SA) | apply (na_nt_at_kept W3 W2 _ _ _ _ SAN)];
                intros i Hi; apply HKS2; unfold NS_ALIAS, NS_ALIASN; lia.
           ++ exact (eq_trans (HAP 26 ltac:(unfold acallee_saved; lia)) (eq_trans (KR 26%bv ltac:(cbn; tauto)) R26)).
           ++ exact (eq_trans (HAP 22 ltac:(unfold acallee_saved; lia)) (eq_trans (KR 22%bv ltac:(cbn; tauto)) R22)).
           ++ exact (eq_trans (HAP 25 ltac:(unfold acallee_saved; lia)) V25).
           ++ exact (eq_trans (HAP 27 ltac:(unfold acallee_saved; lia)) (eq_trans (KR 27%bv ltac:(cbn; tauto)) R27)).
           ++ exact (eq_trans (HAP 23 ltac:(unfold acallee_saved; lia)) (eq_trans (KR 23%bv ltac:(cbn; tauto)) R23)).
           ++ exact (eq_trans (HAP 19 ltac:(unfold acallee_saved; lia)) V19).
           ++ exact (eq_trans (HAP 20 ltac:(unfold acallee_saved; lia)) (eq_trans (KR 20%bv ltac:(cbn; tauto)) R20)).
           ++ lia.
           ++ lia.
           ++ lia.
           ++ lia.
           ++ lia.
           ++ lia.
           ++ lia.
           ++ lia.
           ++ rewrite HM, (nt_ks_step g ioff ileft k) by lia. rewrite Hc1. unfold RTA_HDR. reflexivity.
           ++ exact HBF2.
Qed.

Lemma na_attrs_eta' : forall ak aa, Attrs (a_kind (Attrs ak aa)) (a_alias (Attrs ak aa)) = Attrs ak aa.
Proof. reflexivity. Qed.

(* the attribute loop's head (+0x338 .. +0x37c): the attribute's two bounds (either ends the walk, rc = 0), the
   type tests; an IFLA_LINKINFO of 8 bytes or more opens the nested walk (+0x3ac), one shorter goes to the step,
   an IFLA_IFALIAS is copied by copy_attr (+0x38c) into the alias buffer, any other type goes to the step *)
Lemma na_seg1 : forall f, KS f -> K3 f f -> K1 (S f).
Proof.
  intros f HKS HK3 k2 ly3 S3 W3 ms3 md3 c rest bs aoff aleft [ak aa]
    (HC & HSl & Hsh & R26 & R22 & R20 & R13 & R14 & Ha0 & Hl4 & Hal & Hf & HM & HBF).
  na_open ms3 Hsh rg mm.
  pose proof HC as (HJ & HR & _ & _ & _ & _ & _ & _ & _ & HJB & _ & _ & _ & _ & _ & HBY & HBL & HCL & _).
  cbn [ms_mem ms_regs] in HJ, HR, HBY.
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & HGok & _).
  assert (Hlen0 : (length c <= 4096)%nat) by (unfold NL_CHUNK_MAX in HCL; exact HCL).
  pose proof (nt_rd16_range c aoff ltac:(lia) ltac:(lia)) as Rl.
  pose proof (nt_rd16_range c (aoff + 2) ltac:(lia) ltac:(lia)) as Rt.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof (na_geom SK B LAWS cx fp k2 ly3 S3 W3 _ md3 c rest bs HB HC) as
    (_ & _ & _ & HF4 & HFc & _ & _ & _ & _ & _ & Hsp1 & _ & _ & _).
  destruct (na_st1 cx fp k2 ly3 S3 W3 rg mm md3 c rest bs NT_aloop aoff HB HC HSl R26 Ha0 ltac:(lia)) as [HS SHOK].
  remember (Eimg (Ereg rg (na_ext cx c aoff aoff))) as E eqn:HE.
  assert (HEI : img_env pa_val A_LIM E) by (rewrite HE; apply Eimg_env).
  assert (HAE : env_agree 40 (Ereg rg (na_ext cx c aoff aoff)) E)
    by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (R21 : getr rg 21 = w64 SHADOW_OFF) by exact (proj1 (proj2 (proj2 (proj2 (proj2 HR))))).
  pose (RUN := paj_run_x SK B LAWS (n_G cx) HGok (n_XO cx) (n_OUT cx)).
  pose (RUNTO := paj_run_to_x SK B LAWS (n_G cx) HGok (n_XO cx) (n_OUT cx)).
  pose (BR := paj_branch (PI := PI)).
  assert (U32 : forall E', env_agree 40 (Ereg rg (na_ext cx c aoff aoff)) E' -> U E' (SOff 32 0) = rd16 c aoff)
    by (intros E' HA'; apply (U_atom E' 32); [exact (na_ag_ext 40 rg _ E' 32 0 HA' eq_refl ltac:(lia)) | lia]).
  assert (U33 : forall E', env_agree 40 (Ereg rg (na_ext cx c aoff aoff)) E' -> U E' (SOff 33 0) = rd16 c (aoff + 2))
    by (intros E' HA'; apply (U_atom E' 33); [exact (na_ag_ext 40 rg _ E' 33 1 HA' eq_refl ltac:(lia)) | lia]).
  assert (U13 : forall E', env_agree 40 (Ereg rg (na_ext cx c aoff aoff)) E' -> U E' (SOff 13 0) = 4)
    by (intros E' HA'; apply (U_atom E' 13); [rewrite (na_ag_reg 40 rg _ E' 13 13%bv ltac:(lia) HA' eq_refl); exact R13 | lia]).
  assert (U22 : forall E', env_agree 40 (Ereg rg (na_ext cx c aoff aoff)) E' -> U E' (SOff 22 0) = aleft)
    by (intros E' HA'; apply (U_atom E' 22); [rewrite (na_ag_reg 40 rg _ E' 22 22%bv ltac:(lia) HA' eq_refl); exact R22 | lia]).
  paj_run_tok RUN HS HJ SHOK na_span.
  { na_awr0. }
  na_mem Hm1 HF mm. clear HF HFr HG.
  na_hae HS HAE HE E HAE1.
  psrr_branch_tok RUN BR HS SHOK na_span.
  - (* the length is under 4: the walk ends *)
    rewrite branch_ltu_U, (U32 _ HAE1), (U13 _ HAE1) in Hc. apply Z.ltb_lt in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK na_span NT_exit.
    { na_awr0. }
    na_mem2 Hm2 HF Hm1 mm. clear HF HFr HG.
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => remember Ex as E2 eqn:HE2 end.
    assert (HAE' : env_agree 40 (Ereg rg (na_ext cx c aoff aoff)) E2)
      by (apply (na_ag_trans 40 _ E); [exact HAE | apply (na_ag_le 512); [lia | rewrite HE2; na_ag]]).
    pmkst HS.
    na_reg HS (27%bv : bv 5) Q27.
    pose proof (regs_kept_of_st_ok_pi E2 _ _ rg _ [2%bv; 8%bv; 9%bv; 18%bv; 21%bv; 24%bv; 3%bv; 4%bv]
      HS (na_ag_le 40 32 _ _ ltac:(lia) HAE') ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    destruct (na_keep k2 ly3 S3 W3 _ (mkst (ms_regs ms0) (Z_to_bv 64 (BASE + 27780)) (ms_mem ms0) (seg_rom SEGS))
      md3 _ c rest bs (Attrs ak aa) HC HSl HBF HJ ltac:(cbn [ms_mem mkst]; exact Hm2)
      ltac:(intros r Hr; apply KR; cbn in Hr |- *; tauto) (eq_trans (na_wvb_fds _ _ _) (na_wvb_fds _ _ _)) (eq_trans (na_wvb_fs _ _ _) (na_wvb_fs _ _ _))) as (HC' & HSl' & HBF').
    apply (na_exit SK B POST cx fp k2 ly3 S3 W3 _ _ c rest bs HX HB HC' (na_shape NT_exit _ _)).
    { cbn [ms_regs mkst]. rewrite Q27. reflexivity. }
    { rewrite HM, (nt_as_stop f aoff aleft (Attrs ak aa)) by (try lia; apply orb_true_iff; left; apply Z.ltb_lt; lia).
      exact HBF'. }
  - rewrite branch_ltu_U, (U32 _ HAE1), (U13 _ HAE1) in Hc. apply Z.ltb_ge in Hc.
    paj_run_tok RUN HS HJ SHOK na_span.
    { na_awr0. }
    na_mem2 Hm2 HF Hm1 mm. clear HF HFr HG.
    na_hae HS HAE HE E HAE2.
    psrr_branch_tok RUN BR HS SHOK na_span.
    + (* the length is over the bytes left: the walk ends *)
      rewrite branch_ltu_U, (U22 _ HAE2), (U32 _ HAE2) in Hc0. apply Z.ltb_lt in Hc0.
      paj_run_to_tok RUNTO HS HJ SHOK na_span NT_exit.
      { na_awr0. }
      na_mem2 Hm3 HF Hm2 mm. clear HF HFr HG.
      lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => remember Ex as E2 eqn:HE2 end.
      assert (HAE' : env_agree 40 (Ereg rg (na_ext cx c aoff aoff)) E2)
        by (apply (na_ag_trans 40 _ E); [exact HAE | apply (na_ag_le 512); [lia | rewrite HE2; na_ag]]).
      pmkst HS.
      na_reg HS (27%bv : bv 5) Q27.
      pose proof (regs_kept_of_st_ok_pi E2 _ _ rg _ [2%bv; 8%bv; 9%bv; 18%bv; 21%bv; 24%bv; 3%bv; 4%bv]
        HS (na_ag_le 40 32 _ _ ltac:(lia) HAE') ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      destruct (na_keep k2 ly3 S3 W3 _ (mkst (ms_regs ms1) (Z_to_bv 64 (BASE + 27780)) (ms_mem ms1) (seg_rom SEGS))
        md3 _ c rest bs (Attrs ak aa) HC HSl HBF HJ ltac:(cbn [ms_mem mkst]; exact Hm3)
        ltac:(intros r Hr; apply KR; cbn in Hr |- *; tauto) (eq_trans (na_wvb_fds _ _ _) (eq_trans (na_wvb_fds _ _ _) (na_wvb_fds _ _ _))) (eq_trans (na_wvb_fs _ _ _) (eq_trans (na_wvb_fs _ _ _) (na_wvb_fs _ _ _)))) as (HC' & HSl' & HBF').
      apply (na_exit SK B POST cx fp k2 ly3 S3 W3 _ _ c rest bs HX HB HC' (na_shape NT_exit _ _)).
      { cbn [ms_regs mkst]. rewrite Q27. reflexivity. }
      { rewrite HM, (nt_as_stop f aoff aleft (Attrs ak aa)) by (try lia; apply orb_true_iff; right; apply Z.ltb_lt; lia).
        exact HBF'. }

    + rewrite branch_ltu_U, (U22 _ HAE2), (U32 _ HAE2) in Hc0. apply Z.ltb_ge in Hc0.
      assert (Hst : attr_scan (S f) c aoff aleft (Attrs ak aa) =
        attr_scan f c (aoff + nl_align (rd16 c aoff)) (aleft - nl_align (rd16 c aoff))
          (if rd16 c (aoff + 2) =? 20 then Attrs ak (Some (slice c (aoff + 4) (rd16 c aoff - 4)))
           else if rd16 c (aoff + 2) =? 18 then Attrs (kind_scan f c (aoff + 4) (rd16 c aoff - 4) ak) aa
           else Attrs ak aa)) by (apply nt_as_step; lia).
      rewrite Hst in HM. clear Hst.
      paj_run_tok RUN HS HJ SHOK na_span.
      { na_awr0. }
      na_mem2 Hm3 HF Hm2 mm. clear HF HFr HG.
      na_hae HS HAE HE E HAE3.
      psrr_branch_tok RUN BR HS SHOK na_span.
      * (* IFLA_LINKINFO *)
        rewrite branch_eq_U, (U33 _ HAE3), U_lit in Hc1 by lia. apply Z.eqb_eq in Hc1.
        rewrite Hc1 in HM. cbn [Z.eqb Pos.eqb] in HM.
        paj_run_tok RUN HS HJ SHOK na_span.
        { na_awr0. }
        na_mem2 Hm4 HF Hm3 mm. clear HF HFr HG.
        na_hae HS HAE HE E HAE4.
        psrr_branch_tok RUN BR HS SHOK na_span.
        -- (* under 8 bytes: no nested attribute; the step *)
           rewrite branch_ltu_U, (U32 _ HAE4), U_lit in Hc2 by lia. apply Z.ltb_lt in Hc2.
           paj_run_to_tok RUNTO HS HJ SHOK na_span NT_astep.
           { na_awr0. }
           na_mem2 Hm5 HF Hm4 mm. clear HF HFr HG.
          lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => remember Ex as E2 eqn:HE2 end.
          assert (HAE' : env_agree 40 (Ereg rg (na_ext cx c aoff aoff)) E2)
            by (apply (na_ag_trans 40 _ E); [exact HAE | apply (na_ag_le 512); [lia | rewrite HE2; na_ag]]).
          pmkst HS.
          na_reg HS (25%bv : bv 5) Q25.
          pose proof (regs_kept_of_st_ok_pi E2 _ _ rg _ [2%bv; 8%bv; 9%bv; 18%bv; 21%bv; 24%bv; 3%bv; 4%bv; 20%bv; 13%bv; 14%bv; 26%bv; 22%bv]
            HS (na_ag_le 40 32 _ _ ltac:(lia) HAE') ltac:(vm_compute; reflexivity)) as KR.
          cbn [ms_regs restrict] in KR.
          assert (G21 : ew E2 21 = w64 SHADOW_OFF) by (rewrite (na_ag_reg 40 rg _ E2 21 21%bv ltac:(lia) HAE' eq_refl); exact R21).
          assert (G26 : ew E2 26 = w64 (nBUF cx fp + aoff)) by (rewrite (na_ag_reg 40 rg _ E2 26 26%bv ltac:(lia) HAE' eq_refl); exact R26).
          assert (V25 : getr (ms_regs ms3) 25 = w64 (SHADOW_OFF + (nBUF cx fp + aoff) / 8))
            by (rewrite Q25; apply (na_shx_val E2 26 _ G26 G21); unfold nBUF, NT_BUFOFF; lia).
          destruct (na_keep k2 ly3 S3 W3 _ (mkst (ms_regs ms3) (Z_to_bv 64 (BASE + 27644)) (ms_mem ms3) (seg_rom SEGS))
            md3 _ c rest bs (Attrs ak aa) HC HSl HBF HJ ltac:(cbn [ms_mem mkst]; exact Hm5)
            ltac:(intros r Hr; apply KR; cbn in Hr |- *; tauto) (eq_trans (na_wvb_fds _ _ _) (eq_trans (na_wvb_fds _ _ _) (eq_trans (na_wvb_fds _ _ _) (eq_trans (na_wvb_fds _ _ _) (na_wvb_fds _ _ _))))) (eq_trans (na_wvb_fs _ _ _) (eq_trans (na_wvb_fs _ _ _) (eq_trans (na_wvb_fs _ _ _) (eq_trans (na_wvb_fs _ _ _) (na_wvb_fs _ _ _)))))) as (HC' & HSl' & HBF').
          apply (HKS k2 ly3 S3 W3 _ _ c rest bs aoff aleft (Attrs ak aa)).
          split; [exact HC'|]. split; [exact HSl'|]. split; [exact (na_shape NT_astep _ _)|].
          cbn [ms_regs ms_mem mkst].
          split; [rewrite (KR 26%bv ltac:(cbn; tauto)); exact R26|].
          split; [rewrite (KR 22%bv ltac:(cbn; tauto)); exact R22|].
          split; [exact V25|].
          split; [rewrite (KR 20%bv ltac:(cbn; tauto)); exact R20|].
          split; [rewrite (KR 13%bv ltac:(cbn; tauto)); exact R13|].
          split; [rewrite (KR 14%bv ltac:(cbn; tauto)); exact R14|].
          split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
          split; [|exact HBF'].
          rewrite HM, (nt_ks_small f (aoff + 4) (rd16 c aoff - 4) ak) by lia. reflexivity.

        -- (* 8 bytes or more: the nested walk *)
           rewrite branch_ltu_U, (U32 _ HAE4), U_lit in Hc2 by lia. apply Z.ltb_ge in Hc2.
           paj_run_to_tok RUNTO HS HJ SHOK na_span NT_info.
           { na_awr0. }
           na_mem2 Hm5 HF Hm4 mm. clear HF HFr HG.
           lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => remember Ex as E2 eqn:HE2 end.
           assert (HAE' : env_agree 40 (Ereg rg (na_ext cx c aoff aoff)) E2)
             by (apply (na_ag_trans 40 _ E); [exact HAE | apply (na_ag_le 512); [lia | rewrite HE2; na_ag]]).
           pmkst HS.
           na_reg HS (25%bv : bv 5) Q25. na_reg HS (27%bv : bv 5) Q27. na_reg HS (23%bv : bv 5) Q23.
           pose proof (regs_kept_of_st_ok_pi E2 _ _ rg _ [2%bv; 8%bv; 9%bv; 18%bv; 21%bv; 24%bv; 3%bv; 4%bv; 20%bv; 13%bv; 14%bv; 26%bv; 22%bv]
             HS (na_ag_le 40 32 _ _ ltac:(lia) HAE') ltac:(vm_compute; reflexivity)) as KR.
           cbn [ms_regs restrict] in KR.
           assert (G21 : ew E2 21 = w64 SHADOW_OFF) by (rewrite (na_ag_reg 40 rg _ E2 21 21%bv ltac:(lia) HAE' eq_refl); exact R21).
           assert (G26 : ew E2 26 = w64 (nBUF cx fp + aoff)) by (rewrite (na_ag_reg 40 rg _ E2 26 26%bv ltac:(lia) HAE' eq_refl); exact R26).
           assert (G32 : ew E2 32 = w64 (rd16 c aoff)) by (exact (na_ag_ext 40 rg _ E2 32 0 HAE' eq_refl ltac:(lia))).
           assert (V25 : getr (ms_regs ms3) 25 = w64 (SHADOW_OFF + (nBUF cx fp + aoff) / 8))
             by (rewrite Q25; apply (na_shx_val E2 26 _ G26 G21); unfold nBUF, NT_BUFOFF; lia).
           assert (V27 : getr (ms_regs ms3) 27 = w64 (nBUF cx fp + (aoff + 4))).
           { rewrite Q27, denot_lit_U. rewrite (U_atom_off E2 26 (nBUF cx fp + aoff) 4 G26) by (unfold nBUF, NT_BUFOFF; lia).
             unfold w64. f_equal. lia. }
           assert (V23 : getr (ms_regs ms3) 23 = w64 (rd16 c aoff - 4)).
           { rewrite Q23, denot_lit_U. rewrite (U_atom_off E2 32 (rd16 c aoff) (-4) G32) by lia. reflexivity. }
           destruct (na_keep k2 ly3 S3 W3 _ (mkst (ms_regs ms3) (Z_to_bv 64 (BASE + 27476)) (ms_mem ms3) (seg_rom SEGS))
             md3 _ c rest bs (Attrs ak aa) HC HSl HBF HJ ltac:(cbn [ms_mem mkst]; exact Hm5)
             ltac:(intros r Hr; apply KR; cbn in Hr |- *; tauto) (eq_trans (na_wvb_fds _ _ _) (eq_trans (na_wvb_fds _ _ _) (eq_trans (na_wvb_fds _ _ _) (eq_trans (na_wvb_fds _ _ _) (na_wvb_fds _ _ _))))) (eq_trans (na_wvb_fs _ _ _) (eq_trans (na_wvb_fs _ _ _) (eq_trans (na_wvb_fs _ _ _) (eq_trans (na_wvb_fs _ _ _) (na_wvb_fs _ _ _)))))) as (HC' & HSl' & HBF').
           apply (HK3 k2 ly3 S3 W3 _ _ c rest bs aoff aleft (aoff + 4) (rd16 c aoff - 4) ak aa).
           split; [exact HC'|]. split; [exact HSl'|]. split; [exact (na_shape NT_info _ _)|].
           cbn [ms_regs ms_mem mkst].
           split; [rewrite (KR 26%bv ltac:(cbn; tauto)); exact R26|].
           split; [rewrite (KR 22%bv ltac:(cbn; tauto)); exact R22|].
           split; [exact V25|]. split; [exact V27|]. split; [exact V23|].
           split; [rewrite (KR 20%bv ltac:(cbn; tauto)); exact R20|].
           split; [rewrite (KR 13%bv ltac:(cbn; tauto)); exact R13|].
           split; [rewrite (KR 14%bv ltac:(cbn; tauto)); exact R14|].
           split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
           split; [lia|]. split; [lia|].
           split; [exact HM | exact HBF'].
      * rewrite branch_eq_U, (U33 _ HAE3), U_lit in Hc1 by lia. apply Z.eqb_neq in Hc1.
        replace (rd16 c (aoff + 2) =? 18) with false in HM by (symmetry; apply Z.eqb_neq; exact Hc1).
        paj_run_tok RUN HS HJ SHOK na_span.
        { na_awr0. }
        na_mem2 Hm4 HF Hm3 mm. clear HF HFr HG.
        na_hae HS HAE HE E HAE4.
        psrr_branch_tok RUN BR HS SHOK na_span.
        -- (* any other type: the step *)
           rewrite branch_ne_U, (U33 _ HAE4), U_lit in Hc2 by lia. apply negb_true_iff, Z.eqb_neq in Hc2.
           replace (rd16 c (aoff + 2) =? 20) with false in HM by (symmetry; apply Z.eqb_neq; exact Hc2).
           paj_run_to_tok RUNTO HS HJ SHOK na_span NT_astep.
           { na_awr0. }
           na_mem2 Hm5 HF Hm4 mm. clear HF HFr HG.
          lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => remember Ex as E2 eqn:HE2 end.
          assert (HAE' : env_agree 40 (Ereg rg (na_ext cx c aoff aoff)) E2)
            by (apply (na_ag_trans 40 _ E); [exact HAE | apply (na_ag_le 512); [lia | rewrite HE2; na_ag]]).
          pmkst HS.
          na_reg HS (25%bv : bv 5) Q25.
          pose proof (regs_kept_of_st_ok_pi E2 _ _ rg _ [2%bv; 8%bv; 9%bv; 18%bv; 21%bv; 24%bv; 3%bv; 4%bv; 20%bv; 13%bv; 14%bv; 26%bv; 22%bv]
            HS (na_ag_le 40 32 _ _ ltac:(lia) HAE') ltac:(vm_compute; reflexivity)) as KR.
          cbn [ms_regs restrict] in KR.
          assert (G21 : ew E2 21 = w64 SHADOW_OFF) by (rewrite (na_ag_reg 40 rg _ E2 21 21%bv ltac:(lia) HAE' eq_refl); exact R21).
          assert (G26 : ew E2 26 = w64 (nBUF cx fp + aoff)) by (rewrite (na_ag_reg 40 rg _ E2 26 26%bv ltac:(lia) HAE' eq_refl); exact R26).
          assert (V25 : getr (ms_regs ms3) 25 = w64 (SHADOW_OFF + (nBUF cx fp + aoff) / 8))
            by (rewrite Q25; apply (na_shx_val E2 26 _ G26 G21); unfold nBUF, NT_BUFOFF; lia).
          destruct (na_keep k2 ly3 S3 W3 _ (mkst (ms_regs ms3) (Z_to_bv 64 (BASE + 27644)) (ms_mem ms3) (seg_rom SEGS))
            md3 _ c rest bs (Attrs ak aa) HC HSl HBF HJ ltac:(cbn [ms_mem mkst]; exact Hm5)
            ltac:(intros r Hr; apply KR; cbn in Hr |- *; tauto) (eq_trans (na_wvb_fds _ _ _) (eq_trans (na_wvb_fds _ _ _) (eq_trans (na_wvb_fds _ _ _) (eq_trans (na_wvb_fds _ _ _) (na_wvb_fds _ _ _))))) (eq_trans (na_wvb_fs _ _ _) (eq_trans (na_wvb_fs _ _ _) (eq_trans (na_wvb_fs _ _ _) (eq_trans (na_wvb_fs _ _ _) (na_wvb_fs _ _ _)))))) as (HC' & HSl' & HBF').
          apply (HKS k2 ly3 S3 W3 _ _ c rest bs aoff aleft (Attrs ak aa)).
          split; [exact HC'|]. split; [exact HSl'|]. split; [exact (na_shape NT_astep _ _)|].
          cbn [ms_regs ms_mem mkst].
          split; [rewrite (KR 26%bv ltac:(cbn; tauto)); exact R26|].
          split; [rewrite (KR 22%bv ltac:(cbn; tauto)); exact R22|].
          split; [exact V25|].
          split; [rewrite (KR 20%bv ltac:(cbn; tauto)); exact R20|].
          split; [rewrite (KR 13%bv ltac:(cbn; tauto)); exact R13|].
          split; [rewrite (KR 14%bv ltac:(cbn; tauto)); exact R14|].
          split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
          split; [|exact HBF'].
          exact HM.

        -- (* IFLA_IFALIAS: copy_attr into the alias buffer *)
           rewrite branch_ne_U, (U33 _ HAE4), U_lit in Hc2 by lia. apply negb_false_iff, Z.eqb_eq in Hc2.
           rewrite Hc2 in HM. cbn [Z.eqb Pos.eqb] in HM.
           paj_run_tok RUN HS HJ SHOK na_span.
           { na_awr0. }
           na_mem2 Hm5 HF Hm4 mm. clear HF HFr HG.
           lazymatch type of HS with st_ok _ ?Ex _ _ => remember Ex as E2 eqn:HE2 end.
           assert (HAE' : env_agree 40 (Ereg rg (na_ext cx c aoff aoff)) E2)
             by (apply (na_ag_trans 40 _ E); [exact HAE | apply (na_ag_le 512); [lia | rewrite HE2; na_ag]]).
           assert (HEIk : img_env pa_val A_LIM E2) by (first [assumption | rewrite HE2; assumption]).
           pmkst HS. rewrite na_pc_copy_attr.
           na_reg HS (10%bv : bv 5) Q10. na_reg HS (11%bv : bv 5) Q11. na_reg HS (12%bv : bv 5) Q12.
           na_reg HS (1%bv : bv 5) Q1. na_reg HS (25%bv : bv 5) Q25.
           pose proof (regs_kept_of_st_ok SEGS E2 _ _ rg _ [2%bv; 8%bv; 9%bv; 18%bv; 21%bv; 24%bv; 3%bv; 4%bv; 20%bv; 26%bv; 22%bv]
             HS (na_ag_le 40 32 _ _ ltac:(lia) HAE') ltac:(vm_compute; reflexivity)) as KR.
           cbn [ms_regs restrict] in KR.
           assert (G21 : ew E2 21 = w64 SHADOW_OFF) by (rewrite (na_ag_reg 40 rg _ E2 21 21%bv ltac:(lia) HAE' eq_refl); exact R21).
           assert (G26 : ew E2 26 = w64 (nBUF cx fp + aoff)) by (rewrite (na_ag_reg 40 rg _ E2 26 26%bv ltac:(lia) HAE' eq_refl); exact R26).
           assert (G34 : ew E2 34 = w64 (n_alias cx)) by (exact (na_ag_ext 40 rg _ E2 34 2 HAE' eq_refl ltac:(lia))).
           assert (G35 : ew E2 35 = w64 (n_aliasn cx)) by (exact (na_ag_ext 40 rg _ E2 35 3 HAE' eq_refl ltac:(lia))).
           assert (V25 : getr (ms_regs ms3) 25 = w64 (SHADOW_OFF + (nBUF cx fp + aoff) / 8))
             by (rewrite Q25; apply (na_shx_val E2 26 _ G26 G21); unfold nBUF, NT_BUFOFF; lia).
           destruct (na_keep k2 ly3 S3 W3 _ (mkst (ms_regs ms3) (w64 (BASE + AF_copy_attr)) (ms_mem ms3) (seg_rom SEGS))
             md3 _ c rest bs (Attrs ak aa) HC HSl HBF HJ ltac:(cbn [ms_mem mkst]; exact Hm5)
             ltac:(intros r Hr; apply KR; cbn in Hr |- *; tauto) (eq_trans (na_wvb_fds _ _ _) (eq_trans (na_wvb_fds _ _ _) (eq_trans (na_wvb_fds _ _ _) (eq_trans (na_wvb_fds _ _ _) (na_wvb_fds _ _ _))))) (eq_trans (na_wvb_fs _ _ _) (eq_trans (na_wvb_fs _ _ _) (eq_trans (na_wvb_fs _ _ _) (eq_trans (na_wvb_fs _ _ _) (na_wvb_fs _ _ _)))))) as (HC' & HSl' & HBF').
           apply (na_call SK B LAWS LV TB HSEGS RELRO_IMG CA true cx fp k2 ly3 S3 W3 (ms_regs ms3) (ms_mem ms3) _
             c rest bs aoff NT_ca_a_ra ak aa (POST cx) HB HC' HBF').
           ++ rewrite Q10. exact (sv_off0 E2 26 _ G26).
           ++ rewrite Q11. exact (sv_off0 E2 34 _ G34).
           ++ rewrite Q12. exact (sv_off0 E2 35 _ G35).
           ++ rewrite Q1. exact (codeptr_val E2 _ HEIk).
           ++ unfold NT_ca_a_ra, AF_nl_talk; lia.
           ++ reflexivity.
           ++ lia.
           ++ lia.
           ++ lia.
           ++ intros ly2 S2 W2 regs2 mem2 md2 HC2 HAP HKS2 HBF2.
              apply (na_ret_alias f HKS k2 ly2 S2 W2 regs2 mem2 md2 c rest bs aoff aleft
                (Attrs ak (Some (slice c (aoff + RTA_HDR) (rd16 c aoff - RTA_HDR)))) HC2).
              ** destruct HSl' as (SA & SAN). unfold na_slots.
                 split; [apply (na_nt_at_kept W3 W2 _ _ _ _ SA) | apply (na_nt_at_kept W3 W2 _ _ _ _ SAN)];
                   intros i Hi; apply HKS2; unfold NS_ALIAS, NS_ALIASN; lia.
              ** exact (eq_trans (HAP 26 ltac:(unfold acallee_saved; lia)) (eq_trans (KR 26%bv ltac:(cbn; tauto)) R26)).
              ** exact (eq_trans (HAP 22 ltac:(unfold acallee_saved; lia)) (eq_trans (KR 22%bv ltac:(cbn; tauto)) R22)).
              ** exact (eq_trans (HAP 25 ltac:(unfold acallee_saved; lia)) V25).
              ** exact (eq_trans (HAP 20 ltac:(unfold acallee_saved; lia)) (eq_trans (KR 20%bv ltac:(cbn; tauto)) R20)).
              ** lia.
              ** lia.
              ** lia.
              ** lia.
              ** rewrite HM. unfold RTA_HDR. reflexivity.
              ** exact HBF2.
Qed.

(* the stack bytes the entry stores (+0x320, +0x324: the alias buffer and its cap) *)
Definition na_X (a : Z) : Prop := n_sp1 cx + 8 <= a < n_sp1 cx + 24.

(* a cut's core across a run that wrote only the two spill slots *)
Lemma na_core_stack : forall k2 ly3 S3 W3 ms ms' md md' c rest bs,
  na_core SK B cx fp k2 ly3 S3 W3 ms md c rest bs ->
  ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms') md' k2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ na_X a -> aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms) a -> apresent (w_H W3) (ms_mem ms') a) ->
  (forall r, In r [2%bv; 8%bv; 9%bv; 18%bv; 21%bv; 24%bv; 3%bv; 4%bv] -> getr (ms_regs ms') r = getr (ms_regs ms) r) ->
  m_fds md' = m_fds md -> m_fs md' = m_fs md ->
  na_core SK B cx fp k2 ly3 S3 W3 ms' md' c rest bs.
Proof.
  intros k2 ly3 S3 W3 ms ms' md md' c rest bs HC HJ' KV KP Hr Hfd Hfs.
  pose proof (na_geom SK B LAWS cx fp k2 ly3 S3 W3 ms md c rest bs HB HC) as
    (HAR3 & Hin9 & Hfa9 & HF4 & HFc & HF64 & HFapp & Hsp & Hsp47 & Hsp16 & Hsp1 & Hsp132 & Hwin1 & Hwin2).
  unfold NL_TALK_AK, NL_TALK_AFRAME, NL_TALK_ASLACK, COPY_ATTR_AK, COPY_ATTR_AFRAME, ESTACK in Hsp, Hwin1.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof HC as (HJ & HR & HSV & HH & HS0 & HA1 & HA2 & HA3 & HFS & HJB & HK & HG & HGO & HOW & HRC & HBY & HBL & HCL & HBUF).
  pose proof HK as (HKA & HROD3 & HEs).
  pose proof HJB as (Hk2 & Hperm & Hsetfs & Hfrs & Hnin & Hfa & Hwit & Hfds & Hfs0).
  pose proof HB as (HPRE & _). pose proof HPRE as (HJc & _).
  pose proof HJc as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (HARc & _).
  assert (KW : forall a i, n_sp1 cx + 24 <= a -> a + 8 <= spZ (n_regs cx) + 8 -> 0 <= i < 8 ->
    aview SEGS (w_H W3) (ms_mem ms') (a + i) = aview SEGS (w_H W3) (ms_mem ms) (a + i))
    by (intros a i H1 H2 Hi; apply KV; [lia | unfold na_X; lia]).
  assert (KL : forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms) a)
    by (intros a Ha; apply KV; [lia | unfold na_X; lia]).
  assert (KF : forall a i, nF cx fp <= a -> a + 8 <= nF cx fp + 32768 -> 0 <= i < 8 ->
    aview SEGS (w_H W3) (ms_mem ms') (a + i) = aview SEGS (w_H W3) (ms_mem ms) (a + i))
    by (intros a i H1 H2 Hi; apply KL; lia).
  unfold na_core.
  split; [exact HJ'|].
  split.
  { destruct HR as (R2 & R8 & R9 & R18 & R21 & R24 & R3 & R4). unfold nt_regs.
    rewrite !Hr by (cbn; tauto). tauto. }
  split.
  { destruct HSV as (HS1 & HS2). split.
    - apply (na_nt_at_kept W3 W3 ms ms' _ _ HS1). intros i Hi. apply KW; [lia | lia | exact Hi].
    - intros j Hj. apply (na_nt_at_kept W3 W3 ms ms' _ _ (HS2 j Hj)). intros i Hi. apply KW; [lia | lia | exact Hi]. }
  split.
  { destruct HH as (H1 & H2 & H3 & H4). rewrite na_fsz in H4. unfold nt_header. rewrite na_fsz.
    split; [apply (na_nt_at_kept W3 W3 ms ms' _ _ H1); intros i Hi; apply KF; [lia | lia | exact Hi]|].
    split; [apply (na_nt_at_kept W3 W3 ms ms' _ _ H2); intros i Hi; apply KF; [lia | lia | exact Hi]|].
    split; [apply (na_nt_at_kept W3 W3 ms ms' _ _ H3); intros i Hi; apply KF; [lia | lia | exact Hi]|].
    apply (na_nt_at_kept W3 W3 ms ms' _ _ H4); intros i Hi; apply KF; [lia | lia | exact Hi]. }
  split.
  { destruct HS0 as (H1 & H2 & H3). unfold NS_KIND, NS_KINDN, NS_F in *.
    split; [apply (na_nt_at_kept W3 W3 ms ms' _ _ H1); intros i Hi; apply KW; [lia | lia | exact Hi]|].
    split; [apply (na_nt_at_kept W3 W3 ms ms' _ _ H2); intros i Hi; apply KW; [lia | lia | exact Hi]|].
    apply (na_nt_at_kept W3 W3 ms ms' _ _ H3); intros i Hi; apply KW; [lia | lia | exact Hi]. }
  unfold NS_SH4, NS_FK, NS_FD in *.
  split; [apply (na_nt_at_kept W3 W3 ms ms' _ _ HA1); intros i Hi; apply KW; [lia | lia | exact Hi]|].
  split; [apply (na_nt_at_kept W3 W3 ms ms' _ _ HA2); intros i Hi; apply KW; [lia | lia | exact Hi]|].
  split; [apply (na_nt_at_kept W3 W3 ms ms' _ _ HA3); intros i Hi; apply KW; [lia | lia | exact Hi]|].
  split.
  { destruct HFS as (H1 & H2 & H3). unfold nt_frame_shadow.
    unfold nSH, shadow_of_addr in *.
    split; [intros i Hi; rewrite KL by (unfold SHADOW_OFF; lia); exact (H1 i Hi)|].
    split; [intros i Hi; rewrite KL by (unfold SHADOW_OFF; lia); exact (H2 i Hi)|].
    intros i Hi; rewrite KL by (unfold SHADOW_OFF; lia); exact (H3 i Hi). }
  split.
  { unfold nt_jbk in *. rewrite Hfd, Hfs. exact HJB. }
  split.
  { unfold nt_kept. split; [|split; [|exact HEs]].
    - apply (akept_step SK SEGS B LAWS pa_segs_low (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) W3 (ms_mem ms)
        W3 (ms_mem ms') (spZ (n_regs cx) - NL_TALK_AK) (spZ (n_regs cx))
        (fun a => n_E cx a \/ aside_rng (n_lyc cx) NT_CID fp a) (fun a => n_E cx a \/ aside_rng (n_lyc cx) NT_CID fp a)
        na_X HARc).
      + unfold NL_TALK_AK, NL_TALK_AFRAME, NL_TALK_ASLACK, COPY_ATTR_AK, COPY_ATTR_AFRAME, ESTACK. lia.
      + lia.
      + exact HKA.
      + exact KV.
      + intros a _ Hp. exact (KP a Hp).
      + intros a Ha. exact Ha.
      + intros a Ha. right. unfold na_X in Ha. unfold NL_TALK_AK, NL_TALK_AFRAME, NL_TALK_ASLACK, COPY_ATTR_AK, COPY_ATTR_AFRAME, ESTACK. lia.
    - intros a Hro' Ho' He'.
      assert (Hi : in_img SEGS a)
        by (destruct Hro' as [(sg & Hsg & _ & Hr') | Hr']; [exists sg; split; [exact Hsg | exact Hr'] | exact (RELRO_IMG a Hr')]).
      pose proof (pa_img_range a Hi) as Hai. rewrite img_end_val in Hai.
      rewrite KL by lia. exact (HROD3 a Hro' Ho' He'). }
  split.
  { destruct HG as (HU & HLn). split; [|exact HLn].
    apply (na_au8arr_kept HSEGS W3 W3 (ms_mem ms) (ms_mem ms') LA_G_NL bs HU).
    - intros i Hi. apply KL. rewrite HLn in Hi. unfold LA_G_NL, NK_SIZE in *. lia.
    - intros i Hi. rewrite HLn in Hi. exact (proj2 (proj2 (na_gnl_img B TB HSEGS (LA_G_NL + i) ltac:(unfold NK_SIZE in *; lia)))). }
  split; [exact HGO|]. split; [exact HOW|]. split; [exact HRC|].
  split.
  { apply (na_abytes_kept W3 W3 (ms_mem ms) (ms_mem ms') _ _ HBY). intros i Hi. apply KL.
    unfold NT_BUFLEN in HBL. rewrite HBL in Hi. unfold nBUF, NT_BUFOFF. lia. }
  split; [exact HBL|]. split; [exact HCL|].
  { apply (na_abuf_kept HSEGS W3 W3 (ms_mem ms) (ms_mem ms') _ _ HBUF).
    - intros i Hi. apply KL. unfold NT_BUFLEN in Hi. unfold nBUF, NT_BUFOFF. lia.
    - intros i Hi. apply (na_not_ro_off RELRO_IMG).
      apply (proj2 (aside_rng_low SK SEGS B LAWS pa_segs_low ly3 S3 W3 (ms_mem ms) md NT_CID fp (nBUF cx fp + i) HAR3 Hin9 ltac:(
        left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite Hfa9, na_fsz; unfold NT_BUFLEN in Hi; unfold nBUF, NT_BUFOFF; lia))). }
Qed.

(* the caller's two buffers across that run *)
Lemma na_same_stack : forall (W3 : world SEGS) (m m' : word -> option byte), nt_bufs_same cx (rdW W3 m) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ na_X a -> aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a) ->
  nt_bufs_same cx (rdW W3 m').
Proof.
  intros W3 m m' (K1 & K2 & K3 & K4) KV.
  pose proof HB as (HPRE & _ & HNP & _).
  pose proof HPRE as (HJc & _ & _ & _ & _ & _ & _ & H16 & _ & _ & _ & _ & _ & Hro).
  destruct HNP as (kbs & req & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & HKE & HAE & HKA & HKF & HAF & HKC & HAC).
  assert (Hsp1 : spZ (n_regs cx) - 208 <= n_sp1 cx <= spZ (n_regs cx) - 192).
  { pose proof (aj_window_bounds SK SEGS B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc) as (Hw0 & _).
    pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & Hwlo & _).
    pose proof asan_consts as ((C1a & C1b) & _).
    unfold NL_TALK_AK, NL_TALK_AFRAME, NL_TALK_ASLACK, COPY_ATTR_AK, COPY_ATTR_AFRAME, ESTACK in Hwlo.
    destruct (nt_sp1_range (spZ (n_regs cx)) ltac:(unfold NL_TALK_AFRAME; lia) H16) as (S1 & _).
    unfold n_sp1, NL_TALK_AFRAME in *. lia. }
  pose proof (na_aarg_range (n_regs cx) 2) as Rk. pose proof (na_aarg_range (n_regs cx) 3) as Rkn.
  pose proof (na_aarg_range (n_regs cx) 4) as Ra. pose proof (na_aarg_range (n_regs cx) 5) as Ran.
  assert (KK : n_kind cx <> 0 -> forall i, 0 <= i < n_kindn cx -> aview SEGS (w_H W3) m' (n_kind cx + i) = aview SEGS (w_H W3) m (n_kind cx + i)).
  { intros Hk i Hi. destruct (HKF Hk) as (Hapf & _).
    assert (Hn1 : 1 <= n_kindn cx) by lia. destruct (HKC Hk Hn1) as (Hamr & _). unfold amem_range in Hamr.
    pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
    apply KV; [unfold n_kind, n_kindn, kHighMemEnd, kLowMemEnd in *; lia|].
    unfold na_X, apart_frame, n_kind, n_kindn, NL_TALK_AK, NL_TALK_AFRAME, NL_TALK_ASLACK, COPY_ATTR_AK, COPY_ATTR_AFRAME, ESTACK in *. lia. }
  assert (KA : n_alias cx <> 0 -> forall i, 0 <= i < n_aliasn cx -> aview SEGS (w_H W3) m' (n_alias cx + i) = aview SEGS (w_H W3) m (n_alias cx + i)).
  { intros Hk i Hi. destruct (HAF Hk) as (Hapf & _).
    assert (Hn1 : 1 <= n_aliasn cx) by lia. destruct (HAC Hk Hn1) as (Hamr & _). unfold amem_range in Hamr.
    pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
    apply KV; [unfold n_alias, n_aliasn, kHighMemEnd, kLowMemEnd in *; lia|].
    unfold na_X, apart_frame, n_alias, n_aliasn, NL_TALK_AK, NL_TALK_AFRAME, NL_TALK_ASLACK, COPY_ATTR_AK, COPY_ATTR_AFRAME, ESTACK in *. lia. }
  assert (RK : n_kind cx <> 0 -> forall i, 0 <= i < n_kindn cx -> ~ in_roP SEGS PCAP_RLO PCAP_RHI (n_kind cx + i)).
  { intros Hk i Hi. apply Hro. exists (aivl (n_kind cx) (n_kindn cx)). split; [right; left; reflexivity|].
    unfold aivl. cbn [fst snd]. destruct (Z.eqb_spec (n_kind cx) 0); [contradiction | lia]. }
  assert (RA : n_alias cx <> 0 -> forall i, 0 <= i < n_aliasn cx -> ~ in_roP SEGS PCAP_RLO PCAP_RHI (n_alias cx + i)).
  { intros Hk i Hi. apply Hro. exists (aivl (n_alias cx) (n_aliasn cx)). split; [right; right; left; reflexivity|].
    unfold aivl. cbn [fst snd]. destruct (Z.eqb_spec (n_alias cx) 0); [contradiction | lia]. }
  split; [|split; [|split]].
  - intros Hk s0 Hs Hc0. apply (na_acstr_kept W3 W3 m m' _ _ (K1 Hk s0 Hs Hc0)). intros i Hi. apply KK; [exact Hk | lia].
  - intros Hk s0 Hs Hc0. apply (na_acstr_kept W3 W3 m m' _ _ (K2 Hk s0 Hs Hc0)). intros i Hi. apply KA; [exact Hk | lia].
  - intros Hk Hn. apply (na_abuf_kept HSEGS W3 W3 m m' _ _ (K3 Hk Hn)); intros i Hi; [apply KK | apply RK]; assumption.
  - intros Hk Hn. apply (na_abuf_kept HSEGS W3 W3 m m' _ _ (K4 Hk Hn)); intros i Hi; [apply KA | apply RA]; assumption.
Qed.

(* the phase's entry (+0x314 .. +0x334): the bytes left, the walk's empty test (rc = 0 at the exit), the two spill
   stores and the loop's registers *)
Lemma na_seg0 : (forall f, K1 f) -> forall k2 ly3 S3 W3 ms3 md3,
  ajournal_gx SEGS B (n_G cx) (n_XO cx) (n_OUT cx) (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx)
    (n_W0 cx) (n_mem0 cx) (n_md0 cx) ((NT_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  nt_attr_inv B cx fp k2 ly3 S3 W3 ms3 md3 -> SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
  intros HK1 k2 ly3 S3 W3 ms3 md3 HJ
    (c & rest & off & ml & f & bs & Hsh & HR & HSV & HH & HS0 & HA1 & HA2 & HA3 & R11 & R13 & R25 & R23 & HFS & HJB & HK
       & HGl & HGO & HOW & HSM & HBY & HBL & HCL & HBUF & Hoff & Hml & Hoffml & Hf & HRC & HM).
  assert (HC : na_core SK B cx fp k2 ly3 S3 W3 ms3 md3 c rest bs)
    by exact (conj HJ (conj HR (conj HSV (conj HH (conj HS0 (conj HA1 (conj HA2 (conj HA3 (conj HFS (conj HJB
      (conj HK (conj HGl (conj HGO (conj HOW (conj HRC (conj HBY (conj HBL (conj HCL HBUF)))))))))))))))))).
  na_open ms3 Hsh rg mm.
  cbn [ms_mem ms_regs] in HJ, R11, R13, R25, R23, HBY, HSM.
  pose proof HR as (R2 & R8 & R9 & R18 & R21 & R24 & R3 & R4). cbn [ms_regs] in R2, R9.
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & HGok & _).
  assert (Hlen0 : (length c <= 4096)%nat) by (unfold NL_CHUNK_MAX in HCL; exact HCL).
  unfold NL_HDR, IFI_LEN in Hml, Hf, HM.
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  pose proof (na_geom SK B LAWS cx fp k2 ly3 S3 W3 _ md3 c rest bs HB HC) as
    (HAR3 & Hin9 & Hfa9 & HF4 & HFc & HF64 & HFapp & Hsp & Hsp47 & Hsp16 & Hsp1 & Hsp132 & Hwin1 & Hwin2).
  unfold NL_TALK_AK, NL_TALK_AFRAME, NL_TALK_ASLACK, COPY_ATTR_AK, COPY_ATTR_AFRAME, ESTACK in Hsp, Hwin1.
  remember (Eimg (Ereg rg [])) as E eqn:HE.
  assert (HEI : img_env pa_val A_LIM E) by (rewrite HE; apply Eimg_env).
  assert (HAE : env_agree 40 (Ereg rg []) E)
    by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E9 : ew E 9 = w64 (n_sp1 cx)) by (rewrite (na_ag_reg 40 rg _ E 9 9%bv ltac:(lia) HAE eq_refl); exact R9).
  assert (E2 : ew E 2 = w64 (n_sp1 cx)) by (rewrite (na_ag_reg 40 rg _ E 2 2%bv ltac:(lia) HAE eq_refl); exact R2).
  assert (U9 : bv_unsigned (ew E 9) = n_sp1 cx) by (rewrite E9; apply na_bu; lia).
  assert (U2 : bv_unsigned (ew E 2) = n_sp1 cx) by (rewrite E2; apply na_bu; lia).
  assert (HS : st_ok_pi SEGS pa_val E na_ss0 (restrict (w_H W3) (mkst rg (w64 (BASE + NT_attr)) mm (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold na_ss0. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil]. unfold region_ok, na_spill0.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
      split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS).
      apply (aj_gx_present SK SEGS B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). lia.
    - apply pairwise_disjoint_of_extents. cbn. repeat split; try exact I.
    - split; [|split; exact I].
      unfold na_fac0, na_spf. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U9, U2. change (2 ^ 5) with 32.
      repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
  assert (SHOK : sh_ok SEGS na_Bx [] E (mrestrict (w_H W3) mm)) by apply Forall_nil.
  pose (RUN := paj_run_x SK B LAWS (n_G cx) HGok (n_XO cx) (n_OUT cx)).
  pose (RUNTO := paj_run_to_x SK B LAWS (n_G cx) HGok (n_XO cx) (n_OUT cx)).
  pose (BR := paj_branch (PI := PI)).
  assert (AWR : forall x, n_sp1 cx + 8 <= x < n_sp1 cx + 24 ->
    (awr_byte (n_STK cx) (n_sp0 cx) (n_FP cx) (ablocks B (n_ly cx) (n_S cx)) (ablocks B ly3 S3) ly3 ((NT_CID, fp) :: n_own cx) x
      /\ ~ (n_sp0 cx <= x < n_sp0 cx + n_XO cx)) \/ inG (n_G cx) x \/ (inFP (n_OUT cx) x /\ n_sp0 cx <= x < n_sp0 cx + n_XO cx)).
  { intros x Hx. left. split; [left; lia | lia]. }
  paj_run_tok RUN HS HJ SHOK na_span.
  { apply awr_ok_x_cons; [|apply awr_ok_x_nil]. intros x Hx. cbn [na_spill0 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx.
    rewrite U9 in Hx. exact (AWR x Hx). }
  pose proof (kept_of_frame (segs := SEGS) E _ (w_H W3) mm _ na_X HFr
    ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
          let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
          intros b wlo whi x Hin Hrr; vm_compute in Hin; destruct Hin as [Hq | []]; injection Hq as <- <- <-;
          cbn [base_val] in Hrr; rewrite U9 in Hrr; unfold na_X; lia)) as KV1.
  pose proof (fun x Hp => apresent_grows _ _ _ x HG Hp) as KP1.
  clear HF HFr HG.
  na_hae HS HAE HE E HAE1.
  psrr_branch_tok RUN BR HS SHOK na_span.
  - (* fewer than 4 bytes of attributes: the walk is empty, rc = 0 *)
    rewrite na_branch_lt, (na_S_addw32 _ 13 ml) in Hc
      by (try (rewrite (na_ag_reg 40 rg _ _ 13 13%bv ltac:(lia) HAE1 eq_refl); exact R13); lia).
    rewrite na_S_lit in Hc by lia. apply Z.ltb_lt in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK na_span NT_exit.
    { apply awr_ok_x_cons; [|apply awr_ok_x_nil]. intros x Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx.
      rewrite (eq_trans (f_equal bv_unsigned (na_ag_reg 40 rg _ _ 9 9%bv ltac:(lia) HAE1 eq_refl)) (f_equal bv_unsigned R9)) in Hx.
      rewrite na_bu in Hx by lia. exact (AWR x Hx). }
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => remember Ex as E3 eqn:HE3 end.
    assert (HAE' : env_agree 40 (Ereg rg []) E3)
      by (first [exact HAE | apply (na_ag_trans 40 _ E); [exact HAE | apply (na_ag_le 512); [lia | rewrite HE3; na_ag]]]).
    pose proof (kept_of_frame (segs := SEGS) _ _ (w_H W3) _ _ na_X HFr
      ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
            let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
            intros b wlo whi x Hin Hrr; vm_compute in Hin; destruct Hin as [Hq | []]; injection Hq as <- <- <-;
            cbn [base_val] in Hrr;
            rewrite (eq_trans (f_equal bv_unsigned (na_ag_reg 40 rg _ _ 9 9%bv ltac:(lia) HAE1 eq_refl)) (f_equal bv_unsigned R9)) in Hrr;
            rewrite na_bu in Hrr by lia; unfold na_X; lia)) as KV2.
    pose proof (fun x Hp => apresent_grows _ _ _ x HG Hp) as KP2.
    pmkst HS.
    na_reg HS (27%bv : bv 5) Q27.
    pose proof (regs_kept_of_st_ok_pi E3 _ _ rg _ [2%bv; 8%bv; 9%bv; 18%bv; 21%bv; 24%bv; 3%bv; 4%bv]
      HS (na_ag_le 40 32 _ _ ltac:(lia) HAE') ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    assert (KV : forall a, 0 <= a < 2 ^ 64 -> ~ na_X a -> aview SEGS (w_H W3) (ms_mem ms0) a = aview SEGS (w_H W3) mm a)
      by (intros a Ha Hx; rewrite (KV2 a Ha Hx); exact (KV1 a Ha Hx)).
    assert (KP : forall a, apresent (w_H W3) mm a -> apresent (w_H W3) (ms_mem ms0) a)
      by (intros a Hp; exact (KP2 a (KP1 a Hp))).
    pose proof (na_core_stack k2 ly3 S3 W3 _ (mkst (ms_regs ms0) (Z_to_bv 64 (BASE + 27780)) (ms_mem ms0) (seg_rom SEGS))
      md3 _ c rest bs HC HJ KV KP ltac:(intros r Hr; apply KR; cbn in Hr |- *; tauto)
      (eq_trans (na_wvb_fds _ _ _) (na_wvb_fds _ _ _)) (eq_trans (na_wvb_fs _ _ _) (na_wvb_fs _ _ _))) as HC'.
    apply (na_exit SK B POST cx fp k2 ly3 S3 W3 _ _ c rest bs HX HB HC' (na_shape NT_exit _ _)).
    + cbn [ms_regs mkst]. rewrite Q27. reflexivity.
    + rewrite HM, (na_as_small_eq f c _ _ no_attrs) by lia.
      apply na_bufs_init. cbn [ms_mem mkst]. exact (na_same_stack W3 mm (ms_mem ms0) HSM KV).
  - rewrite na_branch_lt, (na_S_addw32 _ 13 ml) in Hc
      by (try (rewrite (na_ag_reg 40 rg _ _ 13 13%bv ltac:(lia) HAE1 eq_refl); exact R13); lia).
    rewrite na_S_lit in Hc by lia. apply Z.ltb_ge in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK na_span NT_aloop.
    { apply awr_ok_x_cons; [|apply awr_ok_x_nil]. intros x Hx. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx.
      rewrite (eq_trans (f_equal bv_unsigned (na_ag_reg 40 rg _ _ 9 9%bv ltac:(lia) HAE1 eq_refl)) (f_equal bv_unsigned R9)) in Hx.
      rewrite na_bu in Hx by lia. exact (AWR x Hx). }
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => remember Ex as E3 eqn:HE3 end.
    assert (HAE' : env_agree 40 (Ereg rg []) E3)
      by (first [exact HAE | apply (na_ag_trans 40 _ E); [exact HAE | apply (na_ag_le 512); [lia | rewrite HE3; na_ag]]]).
    pose proof (kept_of_frame (segs := SEGS) _ _ (w_H W3) _ _ na_X HFr
      ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
            let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
            intros b wlo whi x Hin Hrr; vm_compute in Hin; destruct Hin as [Hq | []]; injection Hq as <- <- <-;
            cbn [base_val] in Hrr;
            rewrite (eq_trans (f_equal bv_unsigned (na_ag_reg 40 rg _ _ 9 9%bv ltac:(lia) HAE1 eq_refl)) (f_equal bv_unsigned R9)) in Hrr;
            rewrite na_bu in Hrr by lia; unfold na_X; lia)) as KV2.
    pose proof (fun x Hp => apresent_grows _ _ _ x HG Hp) as KP2.
    pmkst HS.
    na_reg HS (26%bv : bv 5) Q26. na_reg HS (22%bv : bv 5) Q22. na_reg HS (20%bv : bv 5) Q20.
    na_reg HS (13%bv : bv 5) Q13. na_reg HS (14%bv : bv 5) Q14.
    pose proof (regs_kept_of_st_ok_pi E3 _ _ rg _ [2%bv; 8%bv; 9%bv; 18%bv; 21%bv; 24%bv; 3%bv; 4%bv]
      HS (na_ag_le 40 32 _ _ ltac:(lia) HAE') ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    assert (KV : forall a, 0 <= a < 2 ^ 64 -> ~ na_X a -> aview SEGS (w_H W3) (ms_mem ms0) a = aview SEGS (w_H W3) mm a)
      by (intros a Ha Hx; rewrite (KV2 a Ha Hx); exact (KV1 a Ha Hx)).
    assert (KP : forall a, apresent (w_H W3) mm a -> apresent (w_H W3) (ms_mem ms0) a)
      by (intros a Hp; exact (KP2 a (KP1 a Hp))).
    assert (G11 : ew E3 11 = w64 (nBUF cx fp + off)) by (rewrite (na_ag_reg 40 rg _ E3 11 11%bv ltac:(lia) HAE' eq_refl); exact R11).
    assert (G13 : ew E3 13 = w64 ml) by (rewrite (na_ag_reg 40 rg _ E3 13 13%bv ltac:(lia) HAE' eq_refl); exact R13).
    assert (G25 : ew E3 25 = w64 (n_alias cx)) by (rewrite (na_ag_reg 40 rg _ E3 25 25%bv ltac:(lia) HAE' eq_refl); exact R25).
    assert (G23 : ew E3 23 = w64 (n_aliasn cx)) by (rewrite (na_ag_reg 40 rg _ E3 23 23%bv ltac:(lia) HAE' eq_refl); exact R23).
    assert (G9 : bv_unsigned (ew E3 9) = n_sp1 cx)
      by (rewrite (na_ag_reg 40 rg _ E3 9 9%bv ltac:(lia) HAE' eq_refl), R9; apply na_bu; lia).
    pose proof (na_core_stack k2 ly3 S3 W3 _ (mkst (ms_regs ms0) (Z_to_bv 64 (BASE + 27360)) (ms_mem ms0) (seg_rom SEGS))
      md3 _ c rest bs HC HJ KV KP ltac:(intros r Hr; apply KR; cbn in Hr |- *; tauto)
      (eq_trans (na_wvb_fds _ _ _) (na_wvb_fds _ _ _)) (eq_trans (na_wvb_fs _ _ _) (na_wvb_fs _ _ _))) as HC'.
    (* the two spill stores *)
    lazymatch type of HS with st_ok_pi _ _ _ ?ssx (restrict _ ?msx) =>
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) na_spill0) in
      pose proof (st_ok_pi_region_nth E3 ssx (restrict _ msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
      cbn [ms_mem restrict] in HR0 end.
    pose proof (field_of_region E3 _ 9%nat (n_sp1 cx) _ _ _ _ _ 8 8%N (SOff 25 0) (n_alias cx) HR0 G9 ltac:(cbn; tauto)
      (sv_off0 E3 25 _ G25) ltac:(pose proof (na_aarg_range (n_regs cx) 4); unfold n_alias; cbn; lia) ltac:(cbn; lia)) as VA.
    pose proof (field_of_region E3 _ 9%nat (n_sp1 cx) _ _ _ _ _ 16 8%N (SOff 23 0) (n_aliasn cx) HR0 G9 ltac:(cbn; tauto)
      (sv_off0 E3 23 _ G23) ltac:(pose proof (na_aarg_range (n_regs cx) 5); unfold n_aliasn; cbn; lia) ltac:(cbn; lia)) as VAN.
    apply (HK1 f k2 ly3 S3 W3 _ _ c rest bs (off + 32) (ml - 32) no_attrs).
    split; [exact HC'|].
    split.
    { unfold na_slots, nt_at, NS_ALIAS, NS_ALIASN. cbn [ms_mem mkst].
      split; apply rdword_of_val_mem; [exact VA | pose proof (na_aarg_range (n_regs cx) 4); unfold n_alias; lia
                                     | exact VAN | pose proof (na_aarg_range (n_regs cx) 5); unfold n_aliasn; lia]. }
    split; [exact (na_shape NT_aloop _ _)|].
    cbn [ms_regs ms_mem mkst].
    split.
    { rewrite Q26, denot_lit_U, (U_atom_off E3 11 (nBUF cx fp + off) 32 G11) by (unfold nBUF, NT_BUFOFF; lia).
      unfold w64. f_equal. lia. }
    split; [rewrite Q22; apply na_denot_of_S; apply (na_S_addw32 E3 13 ml G13); lia|].
    split; [rewrite Q20; reflexivity|]. split; [rewrite Q13; reflexivity|]. split; [rewrite Q14; reflexivity|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [replace (off + 32) with (off + 16 + 16) by lia; replace (ml - 32) with (ml - 16 - 16) by lia; exact HM|].
    apply na_bufs_init. exact (na_same_stack W3 mm (ms_mem ms0) HSM KV).
Qed.

End c.

(* ==========================================================================
   4. The two loops, and the phase
   ========================================================================== *)

(* the nested walk, by induction on kind_scan's fuel *)
Lemma na_K3_all : forall POST cx fp, nt_base SK B cx -> forall f, KS POST cx fp f -> forall g, K3 POST cx fp f g.
Proof.
  intros POST cx fp HB f HKS g. induction g as [|g IH].
  - intros k2 ly3 S3 W3 ms3 md3 c rest bs aoff aleft ioff ileft k al
      (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hg & _). lia.
  - eapply na_seg3; try eassumption. eapply na_seg4; eassumption.
Qed.

(* the attribute walk, by induction on attr_scan's fuel *)
Lemma na_K1_all : forall POST, nt_from SK B POST (nt_exit_inv B) -> forall cx fp, nt_base SK B cx ->
  forall f, K1 POST cx fp f.
Proof.
  intros POST HX cx fp HB f. induction f as [|f IH].
  - intros k2 ly3 S3 W3 ms3 md3 c rest bs aoff aleft a (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hf & _). lia.
  - assert (HKS : KS POST cx fp f) by (eapply na_seg2; eassumption).
    eapply na_seg1; try eassumption. eapply na_K3_all; eassumption.
Qed.

(* THE PHASE: from the first RTM_NEWLINK (+0x314) to the exit (+0x4dc) *)
Lemma nt_attr : forall POST, nt_from SK B POST (nt_exit_inv B) -> nt_from SK B POST (nt_attr_inv B).
Proof.
  intros POST HX cx fp k2 ly3 S3 W3 ms3 md3 HB HJ _ HI.
  eapply na_seg0; try eassumption. intros f. eapply na_K1_all; eassumption.
Qed.

End b.
End a.

About nt_attr.
Print Assumptions nt_attr.
