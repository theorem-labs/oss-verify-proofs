(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the run / keep / branch / leaf tactics, kept_run and same_io_wvb are the text of
   projects/reac-pw/fuzz_qdisc/proofs/lib/A/QPgSlots.v:123-188 (made there from proofs/libreac/fuzz_knock/lib/A/APgStep.v,
   origin/ossv/recipes 6ebe35ba632), the stack-slot write tactics that of QPgCheck.v:52-69, the entry regions those of
   QPgRt.v:61-65 / 193-243, the shadow entry that of proofs/libreac/fuzz_identity/lib/A/Prog/sb_dec.v:354-370
   (origin/ossv/recipes 4b6f0df50aa7), cw_U_sx32_eqb that of proofs/libreac/fuzz_knock/lib/A/APgStep.v:54-68
   (U_sx32_eqb, origin/ossv/recipes 4b6f0df50aa7), cw_join_win that of proofs/reac-pw/fuzz_qdisc/lib/A/QPgLoop0.v:169-196
   (ra_join_win, a working branch b0f706c04a19), cw_bcmp_at that of lib/Reusable/YCbq.v:2262-2310 (aj_bcmp_at) with
   the wrapper's same_but_materialized kept in its post, cw_st_ok_at that of lib/Reusable/YI04.v:342-356 (entry_st_ok_full)
   with the env apart from the registers, renamed with the prefix cw_ and moved to libdiginet/fuzz_codec's ASan
   build (image A); the leaf ends in lib/A/Prog/CPgBase.v's cdc_post, whose memory clause is CodecCJ's tcj_kept. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/CPgWalk.v; 312 of its 358 lines of code are new or changed and 587 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/check_bytes_A.v; 465 of its 501 lines of code are new or changed and 322 lines of the source are left out. *)
(* The image-A walk of diginet_counter_encode (diginet_codec.c:371-386; fuzz_codec.asan 0x86608, 168
   instructions, frame 64) against lib/A/Prog/CPgEncC.v's cdc_counter_specX, with __asan_memcpy (0x51998) as the
   premise aintrin_realizes OCpy. States, regions and the byte lemmas: diginet_counter_encode_A_st.v.
   - pd = None (p = 0): 0x86628 beqz a1 is not taken (0 < seg), 0x8662c beqz a0 is taken: a0 = -1 = E_ARG, out
     untouched (the walk writes its save area only).
   - pd = Some d: the three NULL tests are decided by the atom facts; 0x86634-0x8663c load the shadow offset through
     the .got slot, after which the slot and the cell are dropped and the personality bytes / the segment bytes are
     added in turn (the contract does not keep them apart). Every instrumented check (p + 19, seg[7 - i], p + 16, the
     stores to out, the 4-byte store at out + 28) is decided by the engine's shadow entries of the three ranges, built
     from pers_argA's cimg_range, crd_ok of seg and cdst_ok of out, so no error path is reached.
     0x866c8 bltz (lb device): taken when device >= 128, a0 = -1 = E_ARG (sysex_spec's first test). 0x866d8 bltz,
     ten times, on the payload bytes counter_addr, dots, seg[7], ..., seg[0] at sp + 14 .. sp + 23: taken when bit 7 of
     the byte is set, a0 = -11 = E_RANGE. On every failing return out is untouched.
     Otherwise out[0..4) = f0 13 device 30, __asan_memcpy(out + 4, sp + 14, 10) through cw_intrin_call (the source is
     the function's own save area, whose shadow is zero: cw_stack_src), then out[14] = f7, out[24] = 15, out[25] = 1
     and the key KEY 6 counter_addr at out + 28; a0 = 0. The bytes of out at the return are read from the final
     state's regions, the others (15..23, 26, 27) are kept. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgEncC CPgWalk CPgWalkIntr CPgWalkStr CPgWalkFrame.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import diginet_counter_encode_A_st.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- walk-local tactics ---- *)
(* the atom equations of the walk's base env, through the token atoms (ewset) and the call's havoc *)
Ltac ctr_peel := repeat (first [rewrite ew_ewset_other by (discriminate || lia) | rewrite ew_havoc_old by (apply Nat.ltb_lt; reflexivity) | rewrite ew_havoc_old by lia]).
Ltac ctr_peel_in H := repeat (first [rewrite ew_ewset_other in H by (discriminate || lia) | rewrite ew_havoc_old in H by (apply Nat.ltb_lt; reflexivity) | rewrite ew_havoc_old in H by lia]).
(* a byte of the final state's chunk, as the value of its atom *)
Ltac ctr_val V lem kk v ef :=
  lazymatch type of V with context [sv_denot ?Ex (_ (SOff kk 0))] =>
    rewrite (lem Ex kk v ltac:(ctr_peel; exact ef) ltac:(lia)) in V
  | context [sv_denot ?Ex (SOff kk 0)] =>
    rewrite (lem Ex kk v ltac:(ctr_peel; exact ef) ltac:(lia)) in V end.
(* keep the regions idxs of the state (drops the others) *)
Ltac ctr_pick HS idxs :=
  lazymatch type of HS with YP0l.st_ok ?segs ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (pick (ss_mem ssx) idxs) in
  let HS3 := fresh "HS3" in
  pose proof (st_ok_submem segs Ex ssx msx rs HS ltac:(submem_tac) ltac:(vm_compute; reflexivity)) as HS3;
  clear HS; rename HS3 into HS; norm_ss HS end.
(* add region R in front, okt proving region_ok, djt the disjointness from the state's regions *)
Ltac ctr_add HS R okt djt :=
  lazymatch type of HS with YP0l.st_ok ?segs ?Ex ?ssx ?msx =>
  let HS3 := fresh "HS3" in
  pose proof (ast_ok_add_region segs Ex ssx msx R HS eq_refl) as HS3;
  specialize (HS3 ltac:(okt)); specialize (HS3 ltac:(djt));
  clear HS; rename HS3 into HS; norm_ss HS end.
(* the one-byte chunks of a read-only region over the bytes of garr8 fact HG, chunk offset o is byte o - off0 *)
Ltac ctr_chunks HG EXn off0 :=
  repeat apply Forall_cons; try apply Forall_nil;
  match goal with |- YP09.chunk_ok _ _ _ ?base (YP09.mkChunk ?o (CVal 1 (SOff ?kk 0))) =>
    let j := eval vm_compute in (Z.to_nat (o - off0)) in
    eapply (ctr_chunk1 _ _ base o _ _ j kk HG);
    [ cbn [length]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
    | ctr_peel; rewrite EXn by lia; reflexivity ] end.
(* cw_run / cw_run_to with the save-area fact B2 restated for the current env (the token atoms of the last run
   extend it); the restated fact is dropped after the run, so cw_kwr_stk finds the base one *)
Ltac ctr_b2 run :=
  lazymatch goal with HS : YP0l.st_ok _ ?Ex _ _, B : bv_unsigned (ew ?E0 2) = ?spv |- _ =>
    let H := fresh "B2c" in assert (H : bv_unsigned (ew Ex 2) = spv) by (ctr_peel; exact B);
    run; try clear H end.
Ltac ctr_run := ctr_b2 ltac:(idtac; cw_run cw_awr_stk); cw_keep cw_kwr_stk.
Ltac ctr_run_to pc := ctr_b2 ltac:(idtac; cw_run_to cw_awr_stk pc); cw_keep cw_kwr_stk.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.

(* the write windows of a state: the save area of atom 2, the windows of out (atom 13, the contract's twr_ok
   HTW), every other region read-only *)
Ltac ctr_awr HTW :=
  idtac; lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own);
  lazymatch goal with B2 : bv_unsigned (ew E 2) = ?spv |- _ =>
  lazymatch type of HTW with twr_ok _ _ _ _ _ _ _ _ _ _ _ _ _ ?q ?n =>
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [azlit_tac|]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spv - sp0));
    [reflexivity | rewrite B2; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |]
  | eapply (cw_awr_ok_cons_twr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q n 13%nat);
    [ reflexivity
    | ctr_peel;
      lazymatch goal with H : ew _ 13 = Z_to_bv 64 q |- _ => rewrite H end; apply unsigned_lit_small; lia
    | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | exact HTW | ] ]
  end end end.
(* every write window of a state lies in the zone of the goal (a disjunction of ranges) *)
Ltac ctr_kwr :=
  idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
  intros a (r & Hr & Hb); cbv beta;
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
  repeat (destruct Hr as [<- | Hr];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
      ctr_peel_in Hb;
      repeat match goal with H : ew ?E0 ?n = Z_to_bv 64 _ |- _ =>
        match type of Hb with context [ew E0 n] => rewrite H in Hb end end;
      repeat match goal with H : bv_unsigned (ew ?E0 ?n) = _ |- _ =>
        match type of Hb with context [bv_unsigned (ew E0 n)] => rewrite H in Hb end end;
      rewrite ?unsigned_lit_small in Hb by lia; rewrite ?T_counter_val; lia | ]);
  destruct Hr.
Ltac ctr_runo HTW := ctr_b2 ltac:(idtac; cw_run ltac:(ctr_awr HTW)); cw_keep ctr_kwr.
(* a read-only region of one-byte chunks over the bytes of HG, based on the atom of fact Eb *)
Ltac ctr_rok Eb HG EXn off0 :=
  unfold region_ok, ctr_rpers, ctr_rseg, ctr_rpl;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
  ctr_peel; rewrite Eb, unsigned_lit_small by lia;
  split; [lia|]; split; [lia|]; split; [intros oo Hoo; lia|];
  ctr_chunks HG EXn off0.
(* a new region is disjoint from the state's regions *)
Ltac ctr_dj :=
  lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
  unfold ctr_rpers, ctr_rseg, ctr_rpl, ctr_rout0, ctr_rout14, ctr_rout24, ctr_rout28;
  cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  ctr_peel;
  repeat match goal with H : ew ?E0 ?n = Z_to_bv 64 _ |- context [ew ?E0 ?n] => rewrite H end;
  repeat match goal with H : bv_unsigned (ew ?E0 ?n) = _ |- context [bv_unsigned (ew ?E0 ?n)] => rewrite H end;
  rewrite ?unsigned_lit_small by lia; repeat split; lia.
(* a writable region of out with no chunk: its bytes are present (the contract's twr_ok, kept by KE) *)
Ltac ctr_wok Eb HAR HTD HTW KE :=
  unfold region_ok, ctr_rout0, ctr_rout14, ctr_rout24, ctr_rout28;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
  ctr_peel; rewrite Eb, unsigned_lit_small by lia;
  split; [lia|]; split; [lia|];
  split; [ intros oo Hoo; apply (apresent_writable tfibsegs);
           lazymatch goal with |- apresent _ _ ?a =>
           eapply (apresent_transfer tfibsegs);
           [ lia | intros Him; exact (cw_tdst_not_img tfibsegs _ LAWS tfib_segs_low _ _ _ _ _ _ 32 a HAR HTD ltac:(lia) Him)
           | apply KE; rewrite ?T_counter_val; lia | exact (proj1 (proj2 (HTW a ltac:(lia)))) ] end
         | constructor ].
(* the read-only region of the ten payload bytes at out + 4 after __asan_memcpy (HPL: each byte from the save
   area's chunk it was copied from) *)
Ltac ctr_plok HPL Eb :=
  unfold region_ok, ctr_rpl;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
  ctr_peel; rewrite Eb, unsigned_lit_small by lia;
  split; [lia|]; split; [lia|]; split; [intros oo Hoo; lia|];
  repeat apply Forall_cons; try apply Forall_nil;
  match goal with |- YP09.chunk_ok _ _ _ ?bs (YP09.mkChunk ?o (CVal 1 (SOff ?kk 0))) =>
    lazymatch goal with H : ew ?E0 kk = Z_to_bv 64 ?v |- _ =>
    apply (chunk_ok_val tfibsegs _ _ bs o 1 (SOff kk 0) v);
    [ rewrite sv_denot_SOff0; ctr_peel; exact H
    | change (2 ^ (8 * Z.of_N 1)) with 256; lia
    | cbn; lia
    | apply (HPL o kk v); [lia | lia | cbn [In]; repeat (first [left; reflexivity | right]) | exact H | lia] ] end end.
(* the value of chunk od of region i of the final state, a byte of out *)
Ltac ctr_vb HS i od Hv :=
  lazymatch type of HS with YP0l.st_ok _ ?Ex _ (restrict ?Hh ?msx) =>
  let HR := fresh "HR" in
  pose proof (st_ok_region_nth _ _ _ i _ HS eq_refl) as HR; cbn [ms_mem restrict] in HR;
  lazymatch type of HR with region_ok _ _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
  lazymatch cs with context [YP09.mkChunk od (CVal ?w ?e)] =>
  pose proof (field_of_region_any Ex _ n _ cs lo hi wlo whi od w e HR
    ltac:(ctr_peel;
          lazymatch goal with H : ew _ n = Z_to_bv 64 _ |- _ => rewrite H end; apply unsigned_lit_small; lia)
    ltac:(cbn [In]; repeat (first [left; reflexivity | right]))
    ltac:(cbn; lia)) as Hv
  end end; clear HR; change (N.to_nat 1) with 1%nat in Hv; change (N.to_nat 4) with 4%nat in Hv;
  try (lazymatch type of Hv with val_mem _ _ _ _ (bv_unsigned (sv_denot ?Ey (SLit ?z)) mod ?mm) =>
    let c := eval vm_compute in (bv_unsigned (sv_denot Ey (SLit z)) mod mm) in
    change (bv_unsigned (sv_denot Ey (SLit z)) mod mm) with c in Hv end) end.
(* the branch condition of `lb` + `bltz` on the byte of atom kk, as a test of bit 7 *)
Ltac ctr_bsx Hc :=
  lazymatch type of Hc with branch_taken BC_LT (sv_denot ?Ex (SExt true 8 (SOff ?kk 0))) _ = _ =>
    lazymatch goal with H : ew _ kk = Z_to_bv 64 ?v |- _ =>
      rewrite (ctr_br_sext8 Ex kk v ltac:(ctr_peel; exact H) ltac:(lia)) in Hc end end.
(* the leaf of a failing return: rcq rewrites the spec to (rc, None); out is untouched (the walk wrote only its
   save area) *)
Ltac ctr_err rcq :=
  cw_leaf
    ltac:(idtac; eapply (cw_tcj_of_zone tfibsegs _ LAWS tfib_segs_low);
      [ eassumption | eassumption
      | rewrite T_counter_val; lia | lia
      | intros a Ha Himg;
        lazymatch goal with HA : AR _ _ ?lyc ?Sc ?W ?memc ?mdc, HT : tdst_ok _ ?lyc ?Sc ?q 32 |- _ =>
          exact (cw_tdst_not_img tfibsegs _ LAWS tfib_segs_low lyc Sc W memc mdc q 32 a HA HT Ha Himg) end
      | eassumption | intros a Ha; cbv beta in Ha; left; rewrite T_counter_val; lia ])
    ltac:(idtac; unfold cenc_res; rewrite rcq; cbn [fst snd cmd_outZ]; split;
      [ lazymatch goal with R : getr (ms_regs _) (10%bv : bv 5) = sv_denot _ _ |- _ => rewrite R end;
        apply bv_eq; vm_compute; reflexivity
      | eapply ctr_garr8_kept; [| eassumption];
        lazymatch goal with Hl : length ?bf = 32%nat |- context [length ?bf] => rewrite Hl end;
        intros a Ha; lazymatch goal with KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ => apply KE end; lia ]).

Theorem diginet_counter_encode_A_holds :
  aintrin_realizes tfibsegs B OCpy 0x51998 -> cdc_counter_specX tfibsegs B MT 0x86608.
Proof using MTL TL LAWS.
intros AMC. unfold cdc_counter_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs pd p sg dots out seg before
  HE H10 HPA H11 Hsg0 HGseg Hlen HCRDseg H12 H13 HOUT HPD HSO.
pose proof Hwx_tfa as Hwx. pose proof tfib_segs_low as Hsegs.
pose proof HE as (HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hlive).
cw_keep_j0 HJ HJ0.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HTC : T_counter = 4160) by reflexivity.
destruct H12 as [Hdots H12].
destruct HOUT as (HCOUT & HGout & Hblen).
pose proof HCOUT as (Hout0 & Hout1 & HTDout & HTWout & HRAout & HHVout & HAMout & HCWout).
pose proof HCRDseg as (Hsgq0 & Hsgq1 & _ & HRAseg & HHVseg & HAMseg & HCWseg).
destruct pd as [d|].
{ (* pd = Some d *)
  destruct (ctr_entry B TL LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs d p sg dots out seg
    HE H10 H11 H12 ltac:(lia) H13 HPA Hsg0 Hlen HCRDseg HCOUT HGseg) as [HS SHOK].
  cbn [pers_argA] in HPA. destruct HPA as (Hp0 & Hp1 & Hdv & Hst & Hch & Hdc & HGp & HCRp).
  pose proof HCRp as (_ & _ & _ & HAMp & HCWp & HIMp & HUSp).
  unfold coff_win in HCWp, HCWseg, HCWout. cbn [cpers_disj] in HPD.
  remember (Ereg regs (cw_extra (ctr_xs (d_dev d) (d_strips d) (d_chars d) (d_counter d) seg))) as E eqn:HEE.
  assert (HAE : env_agree 32 (Ereg regs (cw_extra (ctr_xs (d_dev d) (d_strips d) (d_chars d) (d_counter d) seg))) E)
    by (subst E; apply env_agree_refl).
  assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
  assert (B2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
  assert (E3 : ew E 3 = getr regs 3) by (subst E; exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
  assert (E4 : ew E 4 = getr regs 4) by (subst E; exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
  assert (E10 : ew E 10 = Z_to_bv 64 p) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
  assert (E11 : ew E 11 = Z_to_bv 64 sg) by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
  assert (E12 : ew E 12 = Z_to_bv 64 dots) by (subst E; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
  assert (E13 : ew E 13 = Z_to_bv 64 out) by (subst E; rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
  assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
  assert (EXn : forall n, (33 <= n)%nat ->
    ew E n = Z_to_bv 64 (nth (n - 33) (ctr_xs (d_dev d) (d_strips d) (d_chars d) (d_counter d) seg) 0))
    by (intros n Hn; subst E; replace n with (33 + (n - 33))%nat at 1 by lia; apply cw_ew_x).
  assert (E33 : ew E 33 = Z_to_bv 64 (d_dev d)) by (rewrite EXn by lia; reflexivity).
  assert (E36 : ew E 36 = Z_to_bv 64 (d_counter d)) by (rewrite EXn by lia; reflexivity).
  assert (E37 : ew E 37 = Z_to_bv 64 (nth 0 seg 0)) by (rewrite EXn by lia; reflexivity).
  assert (E38 : ew E 38 = Z_to_bv 64 (nth 1 seg 0)) by (rewrite EXn by lia; reflexivity).
  assert (E39 : ew E 39 = Z_to_bv 64 (nth 2 seg 0)) by (rewrite EXn by lia; reflexivity).
  assert (E40 : ew E 40 = Z_to_bv 64 (nth 3 seg 0)) by (rewrite EXn by lia; reflexivity).
  assert (E41 : ew E 41 = Z_to_bv 64 (nth 4 seg 0)) by (rewrite EXn by lia; reflexivity).
  assert (E42 : ew E 42 = Z_to_bv 64 (nth 5 seg 0)) by (rewrite EXn by lia; reflexivity).
  assert (E43 : ew E 43 = Z_to_bv 64 (nth 6 seg 0)) by (rewrite EXn by lia; reflexivity).
  assert (E44 : ew E 44 = Z_to_bv 64 (nth 7 seg 0)) by (rewrite EXn by lia; reflexivity).
  clear HEE.
  assert (Hs8 : forall j, (j < 8)%nat -> 0 <= nth j seg 0 < 256) by (intros j Hj; apply (HGseg j); lia).
  pose proof (Hs8 0%nat ltac:(lia)) as S0. pose proof (Hs8 1%nat ltac:(lia)) as S1.
  pose proof (Hs8 2%nat ltac:(lia)) as S2. pose proof (Hs8 3%nat ltac:(lia)) as S3.
  pose proof (Hs8 4%nat ltac:(lia)) as S4. pose proof (Hs8 5%nat ltac:(lia)) as S5.
  pose proof (Hs8 6%nat ltac:(lia)) as S6. pose proof (Hs8 7%nat ltac:(lia)) as S7.
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) ->
    aview tfibsegs (w_H W) memc a = aview tfibsegs (w_H W) memc a) by (intros; reflexivity).
  unfold cfg_at. change (w64 0x86608) with (Z_to_bv 64 A_CTR).
  (* 0x86608-0x8663c: the frame, the three NULL tests (decided by the atom facts), the shadow offset s2 *)
  ctr_run_to 0x86640.
  (* the .got slot and the cell are not needed again: drop them, add the personality bytes *)
  cw_drop_gb. norm_ss HS.
  lazymatch goal with HS : YP0l.st_ok _ _ _ (restrict _ ?msx) |- _ =>
    assert (HGp1 : garr8 tfibsegs (mrestrict (w_H W) (ms_mem msx)) (p + 16) [d_dev d; d_strips d; d_chars d; d_counter d])
    by (apply (ctr_garr8_kept _ memc); [intros a Ha; apply KE; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in Ha; lia | exact HGp]) end.
  ctr_add HS ctr_rpers ltac:(ctr_rok E10 HGp1 EXn 16) ltac:(ctr_dj).
  (* 0x86640-0x86664: the check of p + 19, lbu counter_addr to sp + 14, dots to sp + 15 *)
  ctr_run_to 0x86668.
  ctr_pick HS [1%nat].
  lazymatch goal with HS : YP0l.st_ok _ _ _ (restrict _ ?msx) |- _ =>
    assert (HGs1 : garr8 tfibsegs (mrestrict (w_H W) (ms_mem msx)) sg seg)
    by (apply (ctr_garr8_kept _ memc); [intros a Ha; apply KE; lia | exact HGseg]) end.
  ctr_add HS ctr_rseg ltac:(ctr_rok E11 HGs1 EXn 0) ltac:(ctr_dj).
  (* 0x86668-0x8669c: seg[7 - i] to sp + 16 + i, each behind its check *)
  ctr_run_to 0x866b0.
  ctr_pick HS [1%nat].
  lazymatch goal with HS : YP0l.st_ok _ _ _ (restrict _ ?msx) |- _ =>
    assert (HGp2 : garr8 tfibsegs (mrestrict (w_H W) (ms_mem msx)) (p + 16) [d_dev d; d_strips d; d_chars d; d_counter d])
    by (apply (ctr_garr8_kept _ memc); [intros a Ha; apply KE; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in Ha; lia | exact HGp]) end.
  ctr_add HS ctr_rpers ltac:(ctr_rok E10 HGp2 EXn 16) ltac:(ctr_dj).
  (* 0x866b0-0x866c8: the check of p + 16, lb device, bltz *)
  ctr_run.
  cw_branch Hdev; ctr_bsx Hdev.
  { (* device >= 128: to 0x867e8, a3 = -1 = E_ARG *)
    apply Z.leb_le in Hdev. ctr_run.
    ctr_err (ctr_spec_arg d seg dots ltac:(lia)). }
  apply Z.leb_gt in Hdev.
  (* 0x866cc-0x866e4: the seven-bit test of the ten payload bytes sp + 14 .. sp + 23 (lb, bltz to 0x867f0) *)
  ctr_run. cw_branch Hb0; ctr_bsx Hb0.
  { apply Z.leb_le in Hb0. ctr_run.
    ctr_err (ctr_spec_range d seg dots (d_counter d) ltac:(lia) Hlen ltac:(cbn [ctr_pl In]; repeat (first [left; reflexivity | right])) ltac:(lia)). }
  apply Z.leb_gt in Hb0.
  ctr_run. cw_branch Hb1; ctr_bsx Hb1.
  { apply Z.leb_le in Hb1. ctr_run.
    ctr_err (ctr_spec_range d seg dots dots ltac:(lia) Hlen ltac:(cbn [ctr_pl In]; repeat (first [left; reflexivity | right])) ltac:(lia)). }
  apply Z.leb_gt in Hb1.
  ctr_run. cw_branch Hb2; ctr_bsx Hb2.
  { apply Z.leb_le in Hb2. ctr_run.
    ctr_err (ctr_spec_range d seg dots (nth 7 seg 0) ltac:(lia) Hlen ltac:(cbn [ctr_pl In]; repeat (first [left; reflexivity | right])) ltac:(lia)). }
  apply Z.leb_gt in Hb2.
  ctr_run. cw_branch Hb3; ctr_bsx Hb3.
  { apply Z.leb_le in Hb3. ctr_run.
    ctr_err (ctr_spec_range d seg dots (nth 6 seg 0) ltac:(lia) Hlen ltac:(cbn [ctr_pl In]; repeat (first [left; reflexivity | right])) ltac:(lia)). }
  apply Z.leb_gt in Hb3.
  ctr_run. cw_branch Hb4; ctr_bsx Hb4.
  { apply Z.leb_le in Hb4. ctr_run.
    ctr_err (ctr_spec_range d seg dots (nth 5 seg 0) ltac:(lia) Hlen ltac:(cbn [ctr_pl In]; repeat (first [left; reflexivity | right])) ltac:(lia)). }
  apply Z.leb_gt in Hb4.
  ctr_run. cw_branch Hb5; ctr_bsx Hb5.
  { apply Z.leb_le in Hb5. ctr_run.
    ctr_err (ctr_spec_range d seg dots (nth 4 seg 0) ltac:(lia) Hlen ltac:(cbn [ctr_pl In]; repeat (first [left; reflexivity | right])) ltac:(lia)). }
  apply Z.leb_gt in Hb5.
  ctr_run. cw_branch Hb6; ctr_bsx Hb6.
  { apply Z.leb_le in Hb6. ctr_run.
    ctr_err (ctr_spec_range d seg dots (nth 3 seg 0) ltac:(lia) Hlen ltac:(cbn [ctr_pl In]; repeat (first [left; reflexivity | right])) ltac:(lia)). }
  apply Z.leb_gt in Hb6.
  ctr_run. cw_branch Hb7; ctr_bsx Hb7.
  { apply Z.leb_le in Hb7. ctr_run.
    ctr_err (ctr_spec_range d seg dots (nth 2 seg 0) ltac:(lia) Hlen ltac:(cbn [ctr_pl In]; repeat (first [left; reflexivity | right])) ltac:(lia)). }
  apply Z.leb_gt in Hb7.
  ctr_run. cw_branch Hb8; ctr_bsx Hb8.
  { apply Z.leb_le in Hb8. ctr_run.
    ctr_err (ctr_spec_range d seg dots (nth 1 seg 0) ltac:(lia) Hlen ltac:(cbn [ctr_pl In]; repeat (first [left; reflexivity | right])) ltac:(lia)). }
  apply Z.leb_gt in Hb8.
  ctr_run. cw_branch Hb9; ctr_bsx Hb9.
  { apply Z.leb_le in Hb9. ctr_run.
    ctr_err (ctr_spec_range d seg dots (nth 0 seg 0) ltac:(lia) Hlen ltac:(cbn [ctr_pl In]; repeat (first [left; reflexivity | right])) ltac:(lia)). }
  apply Z.leb_gt in Hb9.
  ctr_run_to 0x866e8.
  (* the four bytes of out written before __asan_memcpy *)
  ctr_add HS ctr_rout0 ltac:(ctr_wok E13 HAR HTDout HTWout KE) ltac:(ctr_dj).
  (* the zone the rest of the walk writes: its stack window, and the bytes of out it stores to or copies into *)
  lazymatch goal with KE0 : forall a, _ -> ~ _ -> aview _ (w_H W) ?mx a = aview _ (w_H W) memc a |- _ =>
    assert (KE1 : forall a, 0 <= a < 2 ^ 64 -> ~ ((spZ regs - T_counter <= a < spZ regs) \/ (out <= a < out + 4)) ->
      aview tfibsegs (w_H W) mx a = aview tfibsegs (w_H W) memc a)
    by (intros a Ha Hz; apply KE0; [exact Ha|]; rewrite T_counter_val in Hz; lia); clear KE0 end.
  (* 0x866e8-0x8675c: the four checked stores out[0..4), then the call of __asan_memcpy(out + 4, sp + 14, 10) *)
  ctr_runo HTWout.
  (* 0x8675c: __asan_memcpy(out + 4, sp + 14, 10) through the runtime contract (aintrin_realizes OCpy) *)
  lazymatch goal with HS : YP0l.st_ok _ _ _ (restrict _ ?msx) |- _ => rename msx into msC end.
  pose proof (st_ok_region_nth _ _ _ 2 _ HS eq_refl) as HRst. cbn [ms_mem restrict] in HRst.
  rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1. rreg HS (12%bv : bv 5) Ra2.
  rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
  pose proof (cw_stack_src B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem msC) _ k (spZ regs - 50) 10 LAWS HJ
    ltac:(rewrite T_counter_val in Hwlo; lia) ltac:(lia) ltac:(lia)) as HSRC.
  assert (Hspc : spZ (ms_regs msC) = spZ regs - 64) by (unfold spZ at 1; rewrite Rsp, B2, unsigned_lit_small by lia; lia).
  unfold SHADOW_OFF in HRAout. rewrite T_counter_val in Hwlo, HCWout, HCWp.
  lazymatch goal with HS : YP0l.st_ok _ _ ?ss _ |- _ =>
    let K := eval vm_compute in (run_K 0 (SOff 32 0) [] ss) in
    let rs := eval vm_compute in (pick (ss_mem ss) [0; 2]%nat) in
    eapply (cw_intrin_call B LAWS OCpy CA_MEMCPY AMC W _ ss msC _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc k
      (out + 4) (spZ regs - 50) 10 550752 K rs) end.
  - exact HS.
  - reflexivity.
  - reflexivity.
  - exact HJ.
  - rewrite Ra0, E13, unsigned_lit_small by lia. reflexivity.
  - rewrite Ra1, B2. unfold w64. f_equal; try lia.
  - exact Ra2.
  - lia.
  - lia.
  - lia.
  - rewrite Hspc. unfold ESTACK. lia.
  - rewrite Hspc. lia.
  - rewrite Hspc. replace (spZ regs - 64) with (spZ regs + (-4) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
  - exact Hsp0al.
  - rewrite Rgp, E3. exact Hgp.
  - rewrite Rtp, E4. exact Htp.
  - reflexivity.
  - lia.
  - unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity.
  - intros a Ha. split; [exact (proj1 (HTWout a ltac:(lia))) | rewrite Hspc; unfold ESTACK; lia].
  - unfold amem_range in *. lia.
  - apply (range_addressable_sub _ _ out 32); [ | lia | lia ].
    apply (ctr_ra_kept (w_H W) memc (ms_mem msC) out 32); [ | lia | unfold amem_range in HAMout; lia | exact HRAout ].
    intros a Ha. unfold SHADOW_OFF in Ha. apply KE1; [lia|]. unfold amem_range in HAMout. rewrite ?T_counter_val. lia.
  - intros _. apply (cw_hull_sub _ out 32); [ | lia | lia | lia ].
    apply (ctr_hull_kept (w_H W) memc (ms_mem msC) out 32); [ | lia | unfold amem_range in HAMout; lia | lia | apply HHVout; lia ].
    intros a Ha. unfold SHADOW_OFF in Ha. apply KE1; [lia|]. unfold amem_range in HAMout. rewrite ?T_counter_val. lia.
  - split; [lia|]. split; [lia|]. split.
    { intros a Ha. split.
      - apply (proj2 (proj2 (proj2 HSRC))). lia.
      - rewrite Hspc. unfold ESTACK. lia. }
    split; [lia|]. split; [exact (proj1 HSRC)|]. split; [exact (proj1 (proj2 HSRC))|].
    intros _. exact (proj1 (proj2 (proj2 HSRC))).
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - vm_compute. reflexivity.
  - submem_tac.
  - repeat apply Forall_cons; try apply Forall_nil;
      (split; [ intros a Ha; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val] in Ha;
                rewrite ?ew_ewset_other in Ha by lia; rewrite ?E13, ?B2, ?unsigned_lit_small in Ha by lia;
                rewrite Hspc; unfold ESTACK; lia
              | cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; lia ]).
  - intros regs2 mem2 md2 HJ2 HP2 Ha02 Heff Hfr2 Hpres2 HSM2 HS2.
    rewrite Hspc in Hfr2.
    lazymatch type of HS2 with YP0l.st_ok _ _ ?s _ => let v := eval vm_compute in s in change s with v in HS2 end.
    clear HS. rename HS2 into HS.
  (* the kept fact after the call: its window is in [sp - T, sp), its bytes in [out + 4, out + 14) *)
  assert (KE2 : forall a, 0 <= a < 2 ^ 64 -> ~ ((spZ regs - T_counter <= a < spZ regs) \/ (out <= a < out + 14)) ->
    aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memc a).
  { intros a Ha Hz. rewrite T_counter_val in Hz. rewrite (Hfr2 a Ha); [| lia | unfold ESTACK; lia]. apply KE1; [exact Ha|].
    rewrite T_counter_val. lia. }
  (* the ten payload bytes at out + 4, from the save area's chunks before the call *)
  assert (HPL : forall o kk v, (4 <= o < 14) -> (kk < 45)%nat -> In (YP09.mkChunk (o - 54) (CVal 1 (SOff kk 0))) ([
      YP09.mkChunk (-41) (CVal 1 (SOff 37 0)); YP09.mkChunk (-42) (CVal 1 (SOff 38 0));
      YP09.mkChunk (-43) (CVal 1 (SOff 39 0)); YP09.mkChunk (-44) (CVal 1 (SOff 40 0));
      YP09.mkChunk (-45) (CVal 1 (SOff 41 0)); YP09.mkChunk (-46) (CVal 1 (SOff 42 0));
      YP09.mkChunk (-47) (CVal 1 (SOff 43 0)); YP09.mkChunk (-48) (CVal 1 (SOff 44 0));
      YP09.mkChunk (-49) (CVal 1 (SOff 12 0)); YP09.mkChunk (-50) (CVal 1 (SOff 36 0))]) ->
    ew E kk = Z_to_bv 64 v -> 0 <= v < 256 ->
    val_mem tfibsegs (mrestrict (w_H W) mem2) (out + o) 1 v).
  { intros o kk v Ho Hkk Hin Ek Hv. apply (ctr_val1_move (w_H W) (ms_mem msC) mem2 (spZ regs + (o - 54)) (out + o) v).
    - replace (out + o) with (out + 4 + (o - 4)) by lia. replace (spZ regs + (o - 54)) with (spZ regs - 50 + (o - 4)) by lia.
      apply Heff. lia.
    - eapply (field_of_region _ _ 2 (spZ regs) _ (-64) 0 (-64) 0 (o - 54) 1 (SOff kk 0) v HRst).
      + ctr_peel. exact B2.
      + cbn [In]. cbn [In] in Hin. tauto.
      + rewrite sv_denot_SOff0. ctr_peel. exact Ek.
      + change (2 ^ (8 * Z.of_N 1)) with 256. exact Hv.
      + cbn. lia. }
  clear HRst Ra0 Ra1 Ra2 Rsp Rgp Rtp.
  (* the personality bytes again (the call kept them; their region is not one st_ok_after_call keeps), the ten
     payload bytes, and the three windows of out the rest of the walk stores to *)
  assert (HGp3 : garr8 tfibsegs (mrestrict (w_H W) mem2) (p + 16) [d_dev d; d_strips d; d_chars d; d_counter d]).
  { apply (ctr_garr8_kept _ memc); [| exact HGp]. intros a Ha. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in Ha.
    apply KE2; [lia|]. rewrite T_counter_val. lia. }
  ctr_add HS ctr_rpers ltac:(ctr_rok E10 HGp3 EXn 16) ltac:(ctr_dj).
  ctr_add HS ctr_rpl ltac:(ctr_plok HPL E13) ltac:(ctr_dj).
  ctr_add HS ctr_rout14 ltac:(ctr_wok E13 HAR HTDout HTWout KE2) ltac:(ctr_dj).
  ctr_add HS ctr_rout24 ltac:(ctr_wok E13 HAR HTDout HTWout KE2) ltac:(ctr_dj).
  ctr_add HS ctr_rout28 ltac:(ctr_wok E13 HAR HTDout HTWout KE2) ltac:(ctr_dj).
  clear SHOK.
  lazymatch goal with HS : YP0l.st_ok _ ?Ex _ _ |- _ =>
    assert (SHOK : sh_ok tfibsegs CW_Bx [mkSHE 10 16 20; mkSHE 13 0 32] Ex (mrestrict (w_H W) mem2)) end.
  { constructor; [|constructor; [|constructor]].
    - apply (cw_shent_ra_off W mem2 _ 10 p 16 4);
        [ exact (proj1 (HUSp _ _ W mem2 _ (proj1 HJ2))) | exact HAMp | lia | lia | lia | lia
        | ctr_peel; exact E10
        | ctr_peel; exact E32 ].
    - apply (cw_shent_ra W mem2 _ 13 out 32);
        [ | exact HAMout | lia | lia | lia
        | ctr_peel; exact E13
        | ctr_peel; exact E32 ].
      apply (ctr_ra_kept (w_H W) memc mem2 out 32); [ | lia | unfold amem_range in HAMout; lia | exact HRAout ].
      intros a Ha. unfold SHADOW_OFF in Ha. apply KE2; [lia|]. unfold amem_range in HAMout. rewrite T_counter_val. lia. }
  assert (KE3 : forall a, 0 <= a < 2 ^ 64 ->
    ~ ((spZ regs - T_counter <= a < spZ regs) \/ (out <= a < out + 15) \/ (out + 24 <= a < out + 26) \/
       (out + 28 <= a < out + 32)) ->
    aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memc a) by (intros a Ha Hz; apply KE2; [exact Ha | lia]).
  clear KE2 KE1.
  (* 0x86760-0x86810: out[14] = 0xf7, out[24] = 15, out[25] = 1, the 4-byte key at out + 28, a0 = 0, ret *)
  ctr_runo HTWout.
  lazymatch goal with HS : YP0l.st_ok _ _ _ (restrict _ ?msx) |- _ => rename msx into msR end.
  (* the bytes of out at the return: out[0..4), the payload, out[14], out[24], out[25] and the key from the
     final state's regions, the other bytes kept (KE3) *)
  ctr_vb HS 5%nat 0 V0. ctr_vb HS 5%nat 1 V1. ctr_vb HS 5%nat 2 V2. ctr_vb HS 5%nat 3 V3.
  ctr_val V2 ctr_U_sext8_mod 33%nat (d_dev d) E33.
  ctr_vb HS 3%nat 4 V4. ctr_val V4 ctr_U_atom_mod 36%nat (d_counter d) E36.
  ctr_vb HS 3%nat 5 V5. ctr_val V5 ctr_U_atom_mod 12%nat dots E12.
  ctr_vb HS 3%nat 6 V6. ctr_val V6 ctr_U_atom_mod 44%nat (nth 7 seg 0) E44.
  ctr_vb HS 3%nat 7 V7. ctr_val V7 ctr_U_atom_mod 43%nat (nth 6 seg 0) E43.
  ctr_vb HS 3%nat 8 V8. ctr_val V8 ctr_U_atom_mod 42%nat (nth 5 seg 0) E42.
  ctr_vb HS 3%nat 9 V9. ctr_val V9 ctr_U_atom_mod 41%nat (nth 4 seg 0) E41.
  ctr_vb HS 3%nat 10 V10. ctr_val V10 ctr_U_atom_mod 40%nat (nth 3 seg 0) E40.
  ctr_vb HS 3%nat 11 V11. ctr_val V11 ctr_U_atom_mod 39%nat (nth 2 seg 0) E39.
  ctr_vb HS 3%nat 12 V12. ctr_val V12 ctr_U_atom_mod 38%nat (nth 1 seg 0) E38.
  ctr_vb HS 3%nat 13 V13. ctr_val V13 ctr_U_atom_mod 37%nat (nth 0 seg 0) E37.
  ctr_vb HS 2%nat 14 V14. ctr_vb HS 1%nat 24 V24. ctr_vb HS 1%nat 25 V25. ctr_vb HS 0%nat 28 V28.
  lazymatch type of V28 with context [sv_denot ?Ex (SAlu ALU_OR _ _)] =>
    rewrite (ctr_key Ex (d_counter d) ltac:(ctr_peel; exact E36) ltac:(lia)) in V28 end.
  assert (HKr : 0 <= KEY 6 (d_counter d) < 2 ^ 32).
  { unfold KEY. change (6 * 65536) with 393216. replace (Z.land (d_counter d) 65535) with (d_counter d).
    - rewrite Z.lor_comm, ctr_lor_key by lia. lia.
    - symmetry. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
  pose proof (ctr_val4_bytes _ _ _ 0 V28 HKr ltac:(lia)) as V28b. pose proof (ctr_val4_bytes _ _ _ 1 V28 HKr ltac:(lia)) as V29.
  pose proof (ctr_val4_bytes _ _ _ 2 V28 HKr ltac:(lia)) as V30. pose proof (ctr_val4_bytes _ _ _ 3 V28 HKr ltac:(lia)) as V31.
  replace (out + 28 + Z.of_nat 0) with (out + 28) in V28b by lia. replace (out + 28 + Z.of_nat 1) with (out + 29) in V29 by lia.
  replace (out + 28 + Z.of_nat 2) with (out + 30) in V30 by lia. replace (out + 28 + Z.of_nat 3) with (out + 31) in V31 by lia.
  clear V28.
  cbn [nth le4Z] in V28b, V29, V30, V31.
  assert (V15 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msR)) (out + 15) 1 (nth 15 before 0))
    by (apply (ctr_val1_kept (w_H W) memc (ms_mem msR)); [apply KE3; [lia | rewrite T_counter_val; lia] | exact (proj1 (HGout 15%nat ltac:(rewrite Hblen; lia)))]).
  assert (V16 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msR)) (out + 16) 1 (nth 16 before 0))
    by (apply (ctr_val1_kept (w_H W) memc (ms_mem msR)); [apply KE3; [lia | rewrite T_counter_val; lia] | exact (proj1 (HGout 16%nat ltac:(rewrite Hblen; lia)))]).
  assert (V17 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msR)) (out + 17) 1 (nth 17 before 0))
    by (apply (ctr_val1_kept (w_H W) memc (ms_mem msR)); [apply KE3; [lia | rewrite T_counter_val; lia] | exact (proj1 (HGout 17%nat ltac:(rewrite Hblen; lia)))]).
  assert (V18 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msR)) (out + 18) 1 (nth 18 before 0))
    by (apply (ctr_val1_kept (w_H W) memc (ms_mem msR)); [apply KE3; [lia | rewrite T_counter_val; lia] | exact (proj1 (HGout 18%nat ltac:(rewrite Hblen; lia)))]).
  assert (V19 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msR)) (out + 19) 1 (nth 19 before 0))
    by (apply (ctr_val1_kept (w_H W) memc (ms_mem msR)); [apply KE3; [lia | rewrite T_counter_val; lia] | exact (proj1 (HGout 19%nat ltac:(rewrite Hblen; lia)))]).
  assert (V20 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msR)) (out + 20) 1 (nth 20 before 0))
    by (apply (ctr_val1_kept (w_H W) memc (ms_mem msR)); [apply KE3; [lia | rewrite T_counter_val; lia] | exact (proj1 (HGout 20%nat ltac:(rewrite Hblen; lia)))]).
  assert (V21 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msR)) (out + 21) 1 (nth 21 before 0))
    by (apply (ctr_val1_kept (w_H W) memc (ms_mem msR)); [apply KE3; [lia | rewrite T_counter_val; lia] | exact (proj1 (HGout 21%nat ltac:(rewrite Hblen; lia)))]).
  assert (V22 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msR)) (out + 22) 1 (nth 22 before 0))
    by (apply (ctr_val1_kept (w_H W) memc (ms_mem msR)); [apply KE3; [lia | rewrite T_counter_val; lia] | exact (proj1 (HGout 22%nat ltac:(rewrite Hblen; lia)))]).
  assert (V23 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msR)) (out + 23) 1 (nth 23 before 0))
    by (apply (ctr_val1_kept (w_H W) memc (ms_mem msR)); [apply KE3; [lia | rewrite T_counter_val; lia] | exact (proj1 (HGout 23%nat ltac:(rewrite Hblen; lia)))]).
  assert (V26 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msR)) (out + 26) 1 (nth 26 before 0))
    by (apply (ctr_val1_kept (w_H W) memc (ms_mem msR)); [apply KE3; [lia | rewrite T_counter_val; lia] | exact (proj1 (HGout 26%nat ltac:(rewrite Hblen; lia)))]).
  assert (V27 : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msR)) (out + 27) 1 (nth 27 before 0))
    by (apply (ctr_val1_kept (w_H W) memc (ms_mem msR)); [apply KE3; [lia | rewrite T_counter_val; lia] | exact (proj1 (HGout 27%nat ltac:(rewrite Hblen; lia)))]).
  assert (HF : Forall (fun x => 0 <= x < 128) (ctr_pl (d_counter d) dots seg)) by (unfold ctr_pl; repeat constructor; lia).
  cw_leaf
    ltac:(idtac; eapply (cw_tcj_of_zone tfibsegs _ LAWS tfib_segs_low);
      [ exact HJ0 | eassumption | rewrite T_counter_val; lia | lia
      | intros a Ha Himg; exact (cw_tdst_not_img tfibsegs B LAWS tfib_segs_low lyc Sc W memc mdc out 32 a HAR HTDout Ha Himg)
      | exact KE3 | intros a Ha; cbv beta in Ha; unfold cenc_wr; rewrite T_counter_val; lia ])
    ltac:(idtac; unfold cenc_res; rewrite (ctr_spec_ok d seg dots ltac:(lia) Hlen HF); cbn [fst snd]; split;
      [ lazymatch goal with R : getr (ms_regs _) (10%bv : bv 5) = sv_denot _ _ |- _ => rewrite R end;
        apply bv_eq; vm_compute; reflexivity
      | rewrite (ctr_cmd_out before (d_dev d) (d_counter d) dots seg (KEY 6 (d_counter d)) Hblen ltac:(lia) ltac:(lia)
          ltac:(lia) Hs8);
        apply ctr_garr8_of;
        [ intros j Hj; cbn [length app le4Z] in Hj;
          do 32 (destruct j as [|j]; [ cbn [nth app le4Z Z.of_nat Pos.of_succ_nat Pos.succ]; assumption |]);
          exfalso; lia
        | cbn [app le4Z]; repeat apply Forall_cons; try apply Forall_nil;
          first [ lia
                | lazymatch goal with |- 0 <= nth ?j before 0 < 256 => exact (proj2 (HGout j ltac:(rewrite Hblen; lia))) end
                | apply Z.mod_pos_bound; lia ] ] ]).
}
{ (* p = NULL: 0x8662c beqz a0 to 0x867f4, a0 = -1 = E_ARG, out untouched *)
  cbn [pers_argA] in HPA. subst p.
  pose proof (cw_entry_base B TL LAWS A_CTR 64 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs T_counter
    HE ltac:(lia) eq_refl) as HS.
  remember (Ereg regs (cw_extra [])) as E eqn:HEE.
  assert (HAE : env_agree 32 (Ereg regs (cw_extra [])) E) by (subst E; apply env_agree_refl).
  assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
  assert (B2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
  assert (E10 : ew E 10 = Z_to_bv 64 0) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
  assert (E11 : ew E 11 = Z_to_bv 64 sg) by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
  assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
  clear HEE.
  assert (SHOK : sh_ok tfibsegs CW_Bx [] E (mrestrict (w_H W) memc)) by constructor.
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 64 <= a < spZ regs) ->
    aview tfibsegs (w_H W) memc a = aview tfibsegs (w_H W) memc a) by (intros; reflexivity).
  unfold cfg_at. change (w64 0x86608) with (Z_to_bv 64 A_CTR).
  cw_run cw_awr_stk. cw_keep cw_kwr_stk.
  (* 0x86628 beqz a1: seg is not NULL (0 < sg) *)
  cw_branch Hb1.
  { exfalso. rewrite branch_eq_U, (cw_U_atom0 E 11 sg E11), U_lit in Hb1 by lia. apply Z.eqb_eq in Hb1. lia. }
  cw_run cw_awr_stk. cw_keep cw_kwr_stk.
  (* 0x8662c beqz a0: p = NULL, taken *)
  cw_branch Hb2.
  2:{ exfalso. rewrite branch_eq_U, (cw_U_atom0 E 10 0 E10), U_lit in Hb2 by lia. discriminate Hb2. }
  cw_run cw_awr_stk. cw_keep cw_kwr_stk.
  unfold coff_win in HCWout.
  ctr_err (eq_refl : counter_spec None seg dots = (E_ARG, None)).
}
Qed.
End d.
End b.
