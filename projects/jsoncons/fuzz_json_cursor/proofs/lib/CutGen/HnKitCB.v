(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm9L5DefsA PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.PmAsanKit Require Import PtKitA.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutGen Require Import TopKitCB.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module HNK.
Abbreviation mem := (word -> option byte).

Section Stmt.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Variable IC : PMLA.consts.
Definition HARN_SCR : Z := 16384.
Definition EMPTY_A11 : Z := 0x690360.
Definition len_class (lng : bool) (txt : list Z) : Prop := if lng then (23 <= length txt)%nat else (length txt <= 22)%nat.
Definition harness_pre (LB : list (Z * Z)) (cr : credit) (sp ptr : Z) (txt : list Z) (g : PML.ls_state) (R : bvmap 5 word) (M : mem) : Prop :=
  let n := Z.of_nat (length txt) in
  PMSA.a0 R ptr /\ PMSA.a1 R n /\ n < 2 ^ 26 /\ sp mod 16 = 0 /\ PMSA.stksh ar M sp HARN_SCR /\
  ((txt = [] /\ ptr = EMPTY_A11) \/ (0 < n /\ In (ptr, n) LB)) /\ L5.bytes_at (hl_segs L) M ptr txt /\ L5.defined M ptr n /\ (0 < n -> shadow_blk M ptr n) /\
  PMLA.ls_ok (hl_segs L) IC g M /\
  28 * hl_k_per_malloc L <= fst cr /\ hl_b_lin L * (2 * n + 2 ^ 28 + 32768) + 28 * hl_b_overhead L <= snd cr.
Definition harness_post (LB : list (Z * Z)) (cr : credit) (txt : list Z)
           (R : bvmap 5 word) (M : mem) (R' : bvmap 5 word) (M' : mem) (LB' : list (Z * Z)) (cr' : credit) (LBk : list (Z * Z)) (W : list L5.range) : Prop :=
  let n := Z.of_nat (length txt) in
  exists g' : PML.ls_state,
    PMSA.a0 R' 0 /\ PMLA.ls_ok (hl_segs L) IC g' M' /\ g' <> PML.LS0 /\ LB' = LB /\ LBk = LB /\
    fst cr - 28 * hl_k_per_malloc L <= fst cr' /\ snd cr - (hl_b_lin L * (2 * n + 2 ^ 28 + 32768) + 28 * hl_b_overhead L) <= snd cr' /\
    W = PMSA.foot_ranges IC ++ [(hl_tp L - 164, 4)].
Definition harness_chainA (pc aln : Z) (lng : bool) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (sp r ptr : Z) (txt : list Z) (g : PML.ls_state),
    sp mod 32 = aln -> len_class lng txt ->
    PMSA.cps_asan L ar HI pc r sp HARN_SCR LB FF LK cr A PMSA.LIB_FRAMES (harness_pre LB cr sp ptr txt g) (harness_post LB cr txt).
End Stmt.

Lemma wf_ps_init : forall sb bptr, PML.wf_ps (PMSA.ps_init sb bptr).
Proof.
  intros sb bptr. unfold PML.wf_ps, PMSA.ps_init. cbn [PML.ps_sst PML.ps_nst PML.ps_stack PML.ps_scap PML.ps_more PML.ps_level PML.ps_st PML.ps_buf].
  split; [lia|]. split; [lia|]. split; [cbn; lia|]. split; [cbn; tauto|].
  exists [], []. split; [reflexivity|]. split; [constructor|]. intros _.
  split; [reflexivity|]. split; [lia|].
  split; [left; unfold PML.ST_START; lia|].
  split; [left; split; [reflexivity| unfold PML.comment_or_cr, PML.ST_START, PML.ST_CR; lia]|].
  split; [intros [H|[]]; discriminate H | intros H; discriminate H].
Qed.
Lemma kleft_init : forall sb bptr, PML.kleft (PMSA.ps_init sb bptr) = 22.
Proof. intros. reflexivity. Qed.
Lemma bleft_init : forall sb bptr, PML.bleft (PMSA.ps_init sb bptr) = 2 ^ 28 + 1452.
Proof. intros. reflexivity. Qed.
Lemma ps_blocks_init : forall sb bptr, PML.ps_blocks (PMSA.ps_init sb bptr) = [(bptr, 264); (sb, 66)].
Proof. intros. reflexivity. Qed.

Lemma lb_remove_notin : forall ch (LB : list (Z * Z)), (forall b, In b LB -> fst b <> ch) -> lb_remove ch LB = LB.
Proof.
  intros ch LB H. induction LB as [|[b n] LB IH]; [reflexivity|]. cbn [lb_remove fst].
  destruct (Z.eqb_spec b ch) as [E|NE]; [exfalso; exact (H (b, n) (or_introl eq_refl) E)|].
  rewrite IH; [reflexivity|]. intros x Hx. apply H. right. exact Hx.
Qed.

Section Statics.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable IC : PMLA.consts.
Abbreviation segs := (hl_segs L).

Lemma ls12_mid : forall g M, g <> PML.LS0 -> PMLA.ls_ok segs IC g M -> PMSA.statics_mid L IC M.
Proof.
  intros g M Hg (RO & AT & ST).
  assert (ST' : PMLA.loc_done segs IC M /\ PMLA.errcat_guard segs IC M (PML.jbit g) /\ PMLA.convcat_guard segs IC M (PML.cbit g))
    by (destruct g; [exfalso; exact (Hg eq_refl) | exact ST ..]).
  destruct ST' as ((G1 & G2 & SY) & EG & CG).
  split; [exact RO|]. split; [exact (conj G1 G2)|]. split; [right; exact SY|]. exists g. split; [exact Hg|]. split; [exact EG|]. split; [exact CG | exact AT].
Qed.

Lemma mid_syscat_ls : forall M, PMSA.statics_mid L IC M -> PMSA.u8 L M (PMLA.SYSCAT_GUARD IC) 1 ->
  exists g, PMLA.ls_ok segs IC g M /\ g <> PML.LS0.
Proof.
  intros M (RO & (G1 & G2) & _ & EA) SY. destruct EA as (g & Hg & EG & CG & AT).
  exists g. split; [|exact Hg]. split; [exact RO|]. split; [exact AT|].
  destruct g; [exfalso; exact (Hg eq_refl) | exact (conj (conj G1 (conj G2 SY)) (conj EG CG)) ..].
Qed.
Lemma ls_img_ro : forall g M, PMLA.ls_ok segs IC g M -> PMLA.img_ro IC M.
Proof. intros g M (RO & _). exact RO. Qed.

Variables (M M' : mem) (S : Z -> Prop).
Hypothesis AG : forall a, S a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Hypothesis HS : forall a, PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC \/ PMLA.in_foot IC a -> 0 <= a < 2 ^ 63 /\ S a.
Hypothesis HF : forall a, PMLA.GLOC_GUARD IC <= a < PMLA.GLOC_GUARD IC + 1 \/ PMLA.GLOC_PTR IC <= a < PMLA.GLOC_PTR IC + 8 \/ PMLA.SYSCAT_GUARD IC <= a < PMLA.SYSCAT_GUARD IC + 2
             \/ PMLA.ERRCAT_GUARD IC <= a < PMLA.ERRCAT_GUARD IC + 2 \/ PMLA.ATEXIT_TAB IC <= a < PMLA.ATEXIT_TAB IC + 544 \/ a = PMLA.NEED_LOCKS IC
             \/ PMLA.LOCALE_LOCK IC <= a < PMLA.LOCALE_LOCK IC + 4 \/ PMLA.CONVCAT_GUARD IC <= a < PMLA.CONVCAT_GUARD IC + 2 -> PMLA.in_foot IC a.
Lemma loc_done_ag : PMLA.loc_done segs IC M -> PMLA.loc_done segs IC M'.
Proof.
  intros (G1 & G2 & SY). unfold PMLA.u8, PMLA.u64 in *.
  split; [apply (TKA.U8 L IC M M' S AG HS); [intros i Hi; apply HF; left; lia | exact G1]|].
  split; [apply (TKA.U64 L IC M M' S AG HS); [intros i Hi; apply HF; right; left; lia | exact G2]|].
  apply (TKA.U8 L IC M M' S AG HS); [intros i Hi; apply HF; right; right; left; lia | exact SY].
Qed.
Lemma ls_ok_ag : forall g, PMLA.ls_ok segs IC g M -> PMLA.ls_ok segs IC g M'.
Proof.
  intros g H. destruct g; [exact (TKA.ls0_ag L IC M M' S AG HS HF H) | ..]; destruct H as (RO & AT & LD & EG & CG);
    (split; [exact (TKA.img_ro_ag IC M M' S AG HS RO)|]; split; [exact (TKA.atexit_ok_ag L IC M M' S AG HS HF _ AT)|];
     split; [exact (loc_done_ag LD)|]; split; [exact (TKA.errcat_guard_ag L IC M M' S AG HS HF _ EG) | exact (TKA.convcat_guard_ag L IC M M' S AG HS HF _ CG)]).
Qed.
End Statics.

Section Agree.
Variable segs : list Segment.
Variable IC : PMLA.consts.
Variables (M M' : mem) (S : Z -> Prop).
Hypothesis AG : forall a, S a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Abbreviation out := (PTA.out S).

Lemma lstr_short_ag : forall o s, out o 24 -> L5.lstr_short segs M o s -> L5.lstr_short segs M' o s.
Proof.
  intros o s Ho (L0 & L1 & L2 & L3). split; [exact L0|].
  split; [apply (PTA.u8_ag segs M M' S AG); [apply (PTA.out_sub _ _ _ _ _ Ho); lia | exact L1]|].
  split; [apply (PTA.bytes_ag segs M M' S AG); [apply (PTA.out_sub _ _ _ _ _ Ho); lia | exact L2]|].
  apply (PTA.u8_ag segs M M' S AG); [apply (PTA.out_sub _ _ _ _ _ Ho); lia | exact L3].
Qed.
Lemma str_at_w_ag : forall o r, out o 24 -> (forall b, In b (PML.srep_blocks r) -> out (fst b) (Z.of_nat (length (PML.srep_chars r)) + 1)) ->
  PMLA.str_at_w segs M o r -> PMLA.str_at_w segs M' o r.
Proof.
  intros o r Ho Hb H. destruct r as [s|cap p s]; cbn [PMLA.str_at_w] in *; [exact (lstr_short_ag o s Ho H)|].
  destruct H as ((T & W0 & W8 & W16 & BS & NUL) & LT). specialize (Hb (p, cap) (or_introl eq_refl)). cbn [fst PML.srep_chars] in Hb.
  split; [|exact LT]. split; [exact T|].
  split; [apply (PTA.u64_ag segs M M' S AG); [apply (PTA.out_sub _ _ _ _ _ Ho); lia | exact W0]|].
  split; [apply (PTA.u64_ag segs M M' S AG); [apply (PTA.out_sub _ _ _ _ _ Ho); lia | exact W8]|].
  split; [apply (PTA.u64_ag segs M M' S AG); [apply (PTA.out_sub _ _ _ _ _ Ho); lia | exact W16]|].
  split; [apply (PTA.bytes_ag segs M M' S AG); [apply (PTA.out_sub _ _ _ _ _ Hb); lia | exact BS]|].
  apply (PTA.u8_ag segs M M' S AG); [apply (PTA.out_sub _ _ _ _ _ Hb); lia | exact NUL].
Qed.
Lemma iosb_at_ag : forall B rd rb, out B 152 -> PMLA.iosb_at segs IC M B rd rb -> PMLA.iosb_at segs IC M' B rd rb.
Proof.
  intros B rd rb HB (A & Bq & Cq & D & E & F). unfold PMLA.u32, PMLA.u64 in *.
  split; [apply (PTA.u32_ag segs M M' S AG); [apply (PTA.out_sub _ _ _ _ _ HB); lia | exact A]|].
  split; [apply (PTA.u32_ag segs M M' S AG); [apply (PTA.out_sub _ _ _ _ _ HB); lia | exact Bq]|].
  split; [apply (PTA.u64_ag segs M M' S AG); [apply (PTA.out_sub _ _ _ _ _ HB); lia | exact Cq]|].
  split; [apply (PTA.u64_ag segs M M' S AG); [apply (PTA.out_sub _ _ _ _ _ HB); lia | exact D]|].
  split; [intros k Hk; apply (PTA.u64_ag segs M M' S AG); [apply (PTA.out_sub _ _ _ _ _ HB); lia | exact (E k Hk)]|].
  apply (PTA.def_ag M M' S AG); [exact HB | exact F].
Qed.
Lemma source_at_ag : forall R ch, out R 320 -> PMLA.source_at segs IC M R ch -> PMLA.source_at segs IC M' R ch.
Proof.
  intros R ch HR (A & Bq & (st0 & Cq) & D & E). unfold PMLA.u64 in *.
  split; [apply (PTA.u64_ag segs M M' S AG); [apply (PTA.out_sub _ _ _ _ _ HR); lia | exact A]|].
  split; [apply (PTA.u64_ag segs M M' S AG); [apply (PTA.out_sub _ _ _ _ _ HR); lia | exact Bq]|].
  split; [exists st0; apply iosb_at_ag; [apply (PTA.out_sub _ _ _ _ _ HR); lia | exact Cq]|].
  split; [apply (PTA.u64_ag segs M M' S AG); [apply (PTA.out_sub _ _ _ _ _ HR); lia | exact D]|].
  apply (PTA.def_ag M M' S AG); [exact HR | exact E].
Qed.
Lemma parser_at_ag : forall P ps, out P 272 -> out (PML.ps_bptr ps) (PML.ps_bcap ps) -> out (PML.ps_sb ps) (PML.ps_scap ps) ->
  PMLA.parser_at segs IC M P ps -> PMLA.parser_at segs IC M' P ps.
Proof.
  intros P ps HP HB HS H.
  assert (ST : L5.u8_at segs M' (P + 208) (PML.ps_st ps)).
  { pose proof H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & X & _). apply (PTA.u8_ag segs M M' S AG); [apply (PTA.out_sub _ _ _ _ _ HP); lia | exact X]. }
  assert (DF : M' (Z_to_bv 64 (P + 208)) <> None).
  { pose proof H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & D).
    destruct HP as (_ & _ & HPS). rewrite (AG _ (HPS (P + 208) ltac:(lia))). exact (D 208 ltac:(lia)). }
  pose proof (PTA.parser_at_st segs IC M M' S AG P ps (PML.ps_st ps) ltac:(intros k n Hk Hn _; apply (PTA.out_sub _ _ _ _ _ HP); lia) HB HS H ST DF) as G.
  destruct ps; exact G.
Qed.
Lemma reader_at_ag : forall R IS V ch bof ps, out R 592 -> out (PML.ps_bptr ps) (PML.ps_bcap ps) -> out (PML.ps_sb ps) (PML.ps_scap ps) -> PML.ps_win ps = None ->
  PMLA.reader_at segs IC M R IS V ch bof ps -> PMLA.reader_at segs IC M' R IS V ch bof ps.
Proof.
  intros R IS V ch bof ps HR HB HS HW H. unfold PMLA.reader_at, PMLA.u64, PMLA.u8 in *. rewrite HW in *.
  destruct H as (A1 & A2 & A3 & A4 & (de & A5 & A5') & A6 & A7 & A8 & A9 & (st0 & A10) & A11 & A12 & _ & A14).
  assert (U : forall k v, L5.u64_at segs M (R + k) v -> 0 <= k -> k + 8 <= 592 -> L5.u64_at segs M' (R + k) v)
    by (intros k v X K0 K1; apply (PTA.u64_ag segs M M' S AG); [apply (PTA.out_sub _ _ _ _ _ HR); lia | exact X]).
  split; [exact (U _ _ A1 ltac:(lia) ltac:(lia))|]. split; [exact (U _ _ A2 ltac:(lia) ltac:(lia))|]. split; [exact (U _ _ A3 ltac:(lia) ltac:(lia))|]. split; [exact (U _ _ A4 ltac:(lia) ltac:(lia))|].
  split; [exists de; split; [exact (U _ _ A5 ltac:(lia) ltac:(lia)) | exact A5']|]. split; [exact (U _ _ A6 ltac:(lia) ltac:(lia))|].
  split; [apply (PTA.u8_ag segs M M' S AG); [apply (PTA.out_sub _ _ _ _ _ HR); lia | exact A7]|].
  split; [exact (U _ _ A8 ltac:(lia) ltac:(lia))|]. split; [exact (U _ _ A9 ltac:(lia) ltac:(lia))|].
  split; [exists st0; apply iosb_at_ag; [apply (PTA.out_sub _ _ _ _ _ HR); lia | exact A10]|].
  split; [exact (U _ _ A11 ltac:(lia) ltac:(lia))|].
  split; [apply parser_at_ag; [apply (PTA.out_sub _ _ _ _ _ HR); lia | exact HB | exact HS | exact A12]|].
  split; [exact I|]. apply (PTA.def_ag M M' S AG); [exact HR | exact A14].
Qed.
End Agree.

Definition slong (r : PML.srep) : bool := match r with PML.SShort _ => false | PML.SLong _ _ _ => true end.
Section IssX.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Variable IC : PMLA.consts.
Definition iss_ctor_specX (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (IS so sp r : Z) (srep0 : PML.srep),
    PMSA.cps_asan L ar HI pc r sp PMSA.ISS_SCR LB FF LK cr A 0
      (fun R M => PMSA.a0 R IS /\ PMSA.a1 R so /\ PMSA.a2 R 8 /\ PMSA.stksh ar M sp PMSA.ISS_SCR /\
                  PMSA.str_at_w L M so srep0 /\ PMLA.srep_sh M srep0 /\ (forall b, In b (PML.srep_blocks srep0) -> In b LB) /\ Z.of_nat (length (PML.srep_chars srep0)) < 2 ^ 26 /\
                  PMSA.fobj M FF IS 272 /\ PMSA.fobj M FF so 24 /\ PMLA.apart IS 272 so 24 /\ L5.defined M IS 272 /\ L5.defined M so 24 /\
                  (PMSA.ls_ok L IC PML.LS0 M \/ PMSA.statics_mid L IC M) /\
                  acredit_ok L cr (PML.copy_cap (Z.of_nat (length (PML.srep_chars srep0)))) /\
                  match srep0 with PML.SShort _ => True | PML.SLong _ _ s => (23 <= length s)%nat end)
      (fun R M R' M' LB' cr' LBk W => exists rep,
          PML.srep_chars rep = PML.srep_chars srep0 /\ PMSA.isrc_at L IC M' IS rep (PML.srep_data (IS + 80) rep) 0 /\ PMSA.statics_mid L IC M' /\
          LB' = PML.srep_blocks rep ++ LB /\ LBk = LB /\
          (forall b, In b (PML.srep_blocks rep) -> PMSA.afresh L ar LB FF M' (fst b) (snd b) /\ snd b = PML.copy_cap (Z.of_nat (length (PML.srep_chars srep0))) /\ cr' = adebit L cr (snd b)) /\
          (PML.srep_blocks rep = [] -> cr' = cr) /\
          W = (IS, 272) :: PMSA.foot_ranges IC /\ slong rep = slong srep0).
Lemma iss_ctor_specX_weaken : forall pc, iss_ctor_specX pc -> PMSA.iss_ctor_specA L ar HI IC pc.
Proof.
  intros pc H LB FF LK cr A IS so sp r srep0 fx R M model K HH Hmo HK Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs PRE CONT.
  apply (H LB FF LK cr A IS so sp r srep0 fx R M model K HH Hmo HK Hfp Hra Hraok Hsp Htp Hstk Hroom Hffrs PRE).
  intros fx' R' M' model' LB' cr' LBk W LK' A' Hfp' (rep & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & _). apply (CONT fx' R' M' model' LB' cr' LBk W LK' A' Hfp').
  exists rep. repeat (split; [assumption|]). exact P8.
Qed.
End IssX.

Section AgreeSyscat.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable IC : PMLA.consts.
Variables (M M' : mem) (S : Z -> Prop).
Abbreviation segs := (hl_segs L).
Definition sg (a : Z) : Prop := PMLA.SYSCAT_GUARD IC <= a < PMLA.SYSCAT_GUARD IC + 2.
Hypothesis AG : forall a, S a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Hypothesis HS : forall a, PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC \/ PMLA.in_foot IC a -> ~ sg a -> 0 <= a < 2 ^ 63 /\ S a.
Hypothesis HF : forall a, PMLA.GLOC_GUARD IC <= a < PMLA.GLOC_GUARD IC + 1 \/ PMLA.GLOC_PTR IC <= a < PMLA.GLOC_PTR IC + 8 \/ PMLA.SYSCAT_GUARD IC <= a < PMLA.SYSCAT_GUARD IC + 2
             \/ PMLA.ERRCAT_GUARD IC <= a < PMLA.ERRCAT_GUARD IC + 2 \/ PMLA.ATEXIT_TAB IC <= a < PMLA.ATEXIT_TAB IC + 544 \/ a = PMLA.NEED_LOCKS IC
             \/ PMLA.LOCALE_LOCK IC <= a < PMLA.LOCALE_LOCK IC + 4 \/ PMLA.CONVCAT_GUARD IC <= a < PMLA.CONVCAT_GUARD IC + 2 -> PMLA.in_foot IC a.
Hypothesis HD : forall a, PMLA.GLOC_GUARD IC <= a < PMLA.GLOC_GUARD IC + 1 \/ PMLA.GLOC_PTR IC <= a < PMLA.GLOC_PTR IC + 8
             \/ PMLA.ERRCAT_GUARD IC <= a < PMLA.ERRCAT_GUARD IC + 2 \/ PMLA.ATEXIT_TAB IC <= a < PMLA.ATEXIT_TAB IC + 544 \/ a = PMLA.NEED_LOCKS IC
             \/ PMLA.LOCALE_LOCK IC <= a < PMLA.LOCALE_LOCK IC + 4 \/ PMLA.IMG_RO_LO IC <= a < PMLA.IMG_RO_HI IC \/ PMLA.CONVCAT_GUARD IC <= a < PMLA.CONVCAT_GUARD IC + 2 -> ~ sg a.
Lemma OFx : forall a n, 0 < n -> (forall i, a <= i < a + n -> PMLA.in_foot IC i /\ ~ sg i) -> PTA.out S a n.
Proof.
  intros a n Hn Hi. destruct (HS a (or_intror (proj1 (Hi a ltac:(lia)))) (proj2 (Hi a ltac:(lia)))) as ((X0 & _) & _).
  destruct (HS (a + n - 1) (or_intror (proj1 (Hi (a + n - 1) ltac:(lia)))) (proj2 (Hi (a + n - 1) ltac:(lia)))) as ((_ & X1) & _).
  split; [lia|]. split; [lia|]. intros i Hii. exact (proj2 (HS i (or_intror (proj1 (Hi i Hii))) (proj2 (Hi i Hii)))).
Qed.
Lemma CEx : forall a (n : nat) v, (0 < n)%nat -> (forall i, a <= i < a + Z.of_nat n -> PMLA.in_foot IC i /\ ~ sg i) -> cell_is segs M a n v -> cell_is segs M' a n v.
Proof. intros a n v Hn Hf. apply (PTA.cell_ag segs M M' S AG). apply OFx; [lia | exact Hf]. Qed.
Lemma atexit_ok_agx : forall g, PMLA.atexit_ok segs IC M g -> PMLA.atexit_ok segs IC M' g.
Proof.
  intros g ((T1 & T2 & T3) & (Q1 & Q2)).
  assert (TAB : forall i, PMLA.ATEXIT_TAB IC <= i < PMLA.ATEXIT_TAB IC + 544 -> PMLA.in_foot IC i /\ ~ sg i) by (intros i Hi; split; [apply HF | apply HD]; tauto).
  split.
  - split; [apply CEx; [lia | intros ii Hii; apply TAB; lia | exact T1]|]. split; [apply CEx; [lia | intros ii Hii; apply TAB; lia | exact T2]|].
    destruct (PMLA.HS0 IC ++ PMLA.ls_atexit IC g) as [|h0 hs] eqn:EH.
    + destruct T3 as (X & Y). split; [apply CEx; [lia | intros ii Hii; apply TAB; lia | exact X]|].
      destruct Y as [Y|[Y1 Y2]]; [left; apply CEx; [lia | intros ii Hii; apply TAB; lia | exact Y] | right; split; [apply CEx; [lia | intros ii Hii; apply TAB; lia | exact Y1] | apply CEx; [lia | intros ii Hii; apply TAB; lia | exact Y2]]].
    + destruct T3 as (X0 & X1 & X2 & X3 & X4). split; [exact X0|]. split; [apply CEx; [lia | intros ii Hii; apply TAB; lia | exact X1]|]. split; [apply CEx; [lia | intros ii Hii; apply TAB; lia | exact X2]|].
      split; [apply CEx; [lia | intros ii Hii; apply TAB; lia | exact X3]|]. intros i f a Hn. destruct (X4 i f a Hn) as (Y1 & Y2).
      assert (Hi : Z.of_nat i < 32) by (pose proof (nth_error_Some (h0 :: hs) i) as G; rewrite Hn in G; assert ((i < length (h0 :: hs))%nat) by (apply G; discriminate); lia).
      split; [apply CEx; [lia | intros ii Hii; apply TAB; lia | exact Y1] | apply CEx; [lia | intros ii Hii; apply TAB; lia | exact Y2]].
  - split; [apply CEx; [lia | intros i Hi; split; [apply HF | apply HD]; lia | exact Q1] | apply CEx; [lia | intros i Hi; split; [apply HF | apply HD]; lia | exact Q2]].
Qed.
Lemma mid_after_syscat : PMSA.statics_mid L IC M -> PMSA.u8 L M' (PMLA.SYSCAT_GUARD IC) 1 -> exists g, PMLA.ls_ok segs IC g M' /\ g <> PML.LS0.
Proof.
  intros (RO & (G1 & G2) & _ & EA) SY.
  assert (RO' : PMLA.img_ro IC M') by (apply (PTA.clear_ag M M' S AG); [intros i Hi; exact (proj2 (HS i (or_introl Hi) (HD i ltac:(tauto)))) | exact RO]).
  assert (G1' : PMSA.u8 L M' (PMLA.GLOC_GUARD IC) 1) by (apply (PTA.u8_ag segs M M' S AG); [apply OFx; [lia | intros i Hi; split; [apply HF | apply HD]; lia] | exact G1]).
  assert (G2' : PMSA.u64 L M' (PMLA.GLOC_PTR IC) (PMLA.CLASSIC_IMP IC)) by (apply (PTA.u64_ag segs M M' S AG); [apply OFx; [lia | intros i Hi; split; [apply HF | apply HD]; lia] | exact G2]).
  assert (EG' : forall b, PMLA.errcat_guard segs IC M b -> PMLA.errcat_guard segs IC M' b).
  { intros b (X & Y). split; (apply (PTA.u8_ag segs M M' S AG); [apply OFx; [lia | intros i Hi; split; [apply HF | apply HD]; lia] | assumption]). }
  assert (CG' : forall b, PMLA.convcat_guard segs IC M b -> PMLA.convcat_guard segs IC M' b).
  { intros b (X & Y). split; (apply (PTA.u8_ag segs M M' S AG); [apply OFx; [lia | intros i Hi; split; [apply HF | apply HD]; lia] | assumption]). }
  destruct EA as (g & Hg & EG & CG & AT).
  exists g. split; [|exact Hg]. split; [exact RO'|]. split; [exact (atexit_ok_agx _ AT)|].
  destruct g; [exfalso; exact (Hg eq_refl) | exact (conj (conj G1' (conj G2' SY)) (conj (EG' _ EG) (CG' _ CG))) ..].
Qed.
End AgreeSyscat.
End HNK.
