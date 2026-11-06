(* check_no_overread B 0x8124c (fs.c, fs.asan-ubsan), the TAIL CALL STEPS: two of the call-step statements of
   lib/B/FSW_check_no_overread.v's Section I (the CTX-free B interface, a working branch decf0bae273):
     cno_call_bcmp  : cno_call_bcmp_T  (bcmp 0x814a4 / 0x814c0, ra 0x814a8 / 0x814c4)
     cno_call_afree : cno_call_afree_T (__wrap_free 0x814e4 / 0x814ec / 0x814f4, ra 0x814e8 / 0x814f0 / 0x814f8)
   This file proves PART of check_no_overread (rule 24: two of its tail call steps). It states no contract of its own:
   every statement is the interface's Prop, taken by name. The segments that chain the steps are the walk's (_top.v);
   the epilogue and the `ret` are _ret.v's; fuzz_free's step is _ffree.v's. The callees stay Section hypotheses in
   CTX-free form (no call-trace row, no CTX); the allocator's C5 disjunct is closed inside the B kit's free call step
   lib/B/FSW_malloc_free.v fsw_aj_freeU (ALLOC's kit, ea464b7bd5d; used by path) from the event budget
   st_nev S < EV_MAX (`right` of afree_realizesU's last premise).
   TEMPLATE (text only; no byte offset is copied, B's bytes differ): lib/A/FSW_check_no_overread_tail.v at
   a working branch 59f0008819f.
   MEASURED (neutral_dis listing (internal path) on
   the pinned fs.asan-ubsan), the five sites this file walks:
     0x814a4  jal 0x426d8 = PC_bcmp   ra 0x814a8   (0x814a8  bnez a0, 0x815f4)
     0x814c0  jal 0x426d8 = PC_bcmp   ra 0x814c4   (0x814c4  bnez a0, 0x815f4)
     0x814e4 / 0x814ec / 0x814f4  jal 0x530e0 = PC_free   ra 0x814e8 / 0x814f0 / 0x814f8
   GUARDS in these ranges: no UBSan check (U1 / U2 / U3 at 0x813c0 / 0x813e0 / 0x813f8 lie before them) and no inline
   ASan check (0x813c8-0x813d4, 0x81400-0x81410 lie before them). The two branches INSIDE these call ranges, `bnez a0`
   at 0x814a8 and 0x814c4 into the abort block 0x815f4 (before_abort, then abort 0x815f8), are closed by the VALUE the
   callee returns: cno_call_bcmp proves getr regs' 10 = w64 0 from abcmp_realizesU's `v = w64 0 <-> the two ranges
   agree bytewise` (the two reader blocks hold the same bytes l), so neither branch is taken. The other in-edges of
   0x815f4 (0x813a0, 0x81474, 0x81480, 0x81490, 0x814b0, 0x815f0) lie outside this file's ranges.
   LOOKUP (rule 24): proof-index by NAME check_no_overread and by B ADDRESS 0x8124c, unpiped, a Theorem Labs lane
   2026-10-29 05:4xZ (outputs (internal path), r24-cnoB-addr.txt): released plain /
   UBSan templates only, no released lib/A or lib/B walk; 0x8124c: 0 released hits. CONFIRM:
   (internal path). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG08 YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_ret FSW_rres FSW_frame FSW_strkit FSH_Fn_cno FSH_Fn_alloc
FSW_check_no_overread_tbl FSW_check_no_overread.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSH_Fn_writer.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSW_malloc_free.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section T. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* ---- user poison and the raw memory ---- *)
(* unpoison touches shadow bytes only: where U has no shadow byte the view is the machine's own *)
Lemma cno_unp_off : forall (W : world tfibsegs) U mem a, 0 <= a < 2 ^ 64 -> in_ush U a = false ->
  aview tfibsegs (w_H W) (unpoison U mem) a = aview tfibsegs (w_H W) mem a.
Proof.
intros W U mem a Ha Hu. apply (aview_at tfibsegs). apply unpoison_out. rewrite (wz a Ha). exact Hu.
Qed.
(* outside [SHADOW_OFF, kHighMemBeg) no byte is a shadow byte of U at all *)
Lemma cno_unp_out : forall ly S U (W : world tfibsegs) mem md a,
  ARU tfibsegs B ly S U W mem md -> 0 <= a < 2 ^ 64 -> ~ (SHADOW_OFF <= a < kHighMemBeg) ->
  aview tfibsegs (w_H W) (unpoison U mem) a = aview tfibsegs (w_H W) mem a.
Proof.
intros ly S U W mem md a HARU Ha Hns. apply (cno_unp_off W U mem a Ha).
destruct (in_ush U a) eqn:E; [|reflexivity].
exfalso. pose proof (ush_facts tfibsegs B ly S U W mem md a HARU E) as (_ & Hlo & Hhi). lia.
Qed.
(* the same view equality on two memories of ONE world carries to their unpoisoned forms *)
Lemma cno_unp_cong : forall (W : world tfibsegs) U m m' a,
  aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a ->
  aview tfibsegs (w_H W) (unpoison U m') a = aview tfibsegs (w_H W) (unpoison U m) a.
Proof.
intros W U m m' a E. unfold aview, mbyte, mrestrict, unpoison in *.
destruct (w_H W (Z_to_bv 64 a)); [reflexivity|].
destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))); [reflexivity | exact E].
Qed.
Lemma cno_unp_pres : forall (W : world tfibsegs) U m m' a,
  (apresent (w_H W) m a -> apresent (w_H W) m' a) ->
  apresent (w_H W) (unpoison U m) a -> apresent (w_H W) (unpoison U m') a.
Proof.
intros W U m m' a HP (Hh & b & Hb). unfold unpoison in *.
destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:Eu.
- split; [exact Hh|]. exists (Z_to_bv 8 0). rewrite Eu. reflexivity.
- destruct (HP (conj Hh (ex_intro _ b Hb))) as (Hh' & b' & Hb').
  split; [exact Hh'|]. exists b'. rewrite Eu. exact Hb'.
Qed.
(* a byte of the application range has a shadow byte in [SHADOW_OFF, 2 ^ 48) *)
Lemma cno_sh_rng : forall a, 0 <= a <= alloc_ceiling -> SHADOW_OFF <= shadow_addr a < 2 ^ 48.
Proof.
intros a Ha. pose proof asan_consts as (C1 & _). unfold shadow_addr, SHADOW_OFF.
pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)).
assert (a / 8 <= a) by (apply Z.div_le_upper_bound; lia). lia.
Qed.
(* a shadow byte that the unpoisoned view shows is a byte the machine's own memory shows: where U poisons, the
   machine holds the magic 0xf7 (upoisoned), elsewhere the two views agree *)
Lemma cno_raw_vis : forall ly S U (W : world tfibsegs) mem md s,
  ARU tfibsegs B ly S U W mem md -> 0 <= s < 2 ^ 64 ->
  aview tfibsegs (w_H W) (unpoison U mem) s <> None -> aview tfibsegs (w_H W) mem s <> None.
Proof.
intros ly S U W mem md s HARU Hs HV. destruct HARU as (_ & _ & PO).
destruct (in_ush U s) eqn:E.
- rewrite (PO s E). discriminate.
- rewrite <- (cno_unp_off W U mem s Hs E). exact HV.
Qed.
(* the shadow of a block byte at offset 16 or more is no shadow byte of U: every range of U is the 16-byte head of
   a live block (fs_heads), blocks are pairwise disjoint (al_sep) and 16-aligned (al_blocks) *)
Lemma cno_body_not_ush : forall ly S U (W : world tfibsegs) mem md p m a,
  AR tfibsegs B ly S W (unpoison U mem) md -> FSupoisonU.fs_heads B ly S U ->
  In (p, m) (ablocks B ly S) -> p + 16 <= a < p + req_size m -> in_ush U (shadow_addr a) = false.
Proof.
intros ly S U W mem md p m a HAR FH Hin Ha.
destruct (in_ush U (shadow_addr a)) eqn:E; [|reflexivity]. exfalso.
unfold in_ush in E. apply existsb_exists in E as (r & Hr & Hc).
apply andb_prop in Hc as [L1 L2]. apply Z.leb_le in L1. apply Z.ltb_lt in L2.
destruct (FH r Hr) as (E16 & m' & Hm' & M16). destruct r as [h s]. cbn [fst snd] in *. subst s.
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md h m' HAR Hm') as (Hh16 & _ & _ & _ & _ & _ & _).
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md p m HAR Hin) as (Hp16 & _ & _ & _ & _ & _ & _).
change (16 / 8) with 2 in L2.
destruct (Z.eq_dec h p) as [->|Hne].
- unfold shadow_addr in L1, L2. Z.div_mod_to_equations. lia.
- pose proof (sep_blocks tfibsegs B LAWS ly S W (unpoison U mem) md h m' p m HAR Hm' Hin
    ltac:(intros EE; injection EE as EE1 _; exact (Hne EE1))) as D.
  unfold zdisjoint in D. cbn [fst snd] in D.
  unfold shadow_addr in L1, L2. Z.div_mod_to_equations. lia.
Qed.


(* ---- the four allocator statics (FSH_Base.v G_FAIL / G_LIVE / G_PEAK / G_COUNT = the four FS_PSTAT_FP cells) ---- *)
Lemma cno_img_pstat : forall a, 0xa41c0 <= a < 0x5dab08 -> in_img tfibsegs a.
Proof.
intros a Ha.
assert (Hb : existsb (fun s => (Z.of_N (seg_base s) <=? 0xa41c0) &&
  (0x5dab08 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs = true) by (vm_compute; reflexivity).
apply existsb_exists in Hb as (s & Hs & Hss). apply andb_prop in Hss as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. exists s. split; [exact Hs | lia].
Qed.
(* a byte of a static's word is an FP byte, an image byte, no owned static and no errno byte *)
Lemma cno_pstat_byte : forall g a, In (g, g + 8) FS_PSTAT_FP -> g <= a < g + 8 ->
  fs_img_facts tfibsegs B ->
  in_img tfibsegs a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4) /\
  0 <= a < SHADOW_OFF.
Proof.
intros g a Hg Ha IMG. pose proof (inFP_FS_PSTAT_FP g Hg a Ha) as HFP.
assert (Hr : 0xa41c0 <= a < 0x5dab08).
{ unfold FS_PSTAT_FP in Hg. cbn [In] in Hg.
  destruct Hg as [E|[E|[E|[E|[]]]]]; injection E as <- _; lia. }
pose proof (proj1 IMG a HFP) as [H1 H2].
split; [exact (cno_img_pstat a Hr)|]. split; [exact H1|]. split; [exact H2|].
unfold SHADOW_OFF. lia.
Qed.
(* the allocator's four words are kept by any step that keeps the image bytes outside the owned statics *)
Lemma cno_glob_kept : forall ly S U (W : world tfibsegs) mem md ly' S' U' (W' : world tfibsegs) mem' md' live peak cnt fail,
  fs_img_facts tfibsegs B ->
  ARU tfibsegs B ly S U W mem md -> ARU tfibsegs B ly' S' U' W' mem' md' ->
  (forall a, in_img tfibsegs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     aview tfibsegs (w_H W') (unpoison U' mem') a = aview tfibsegs (w_H W) (unpoison U mem) a) ->
  fs_glob tfibsegs W mem live peak cnt fail -> fs_glob tfibsegs W' mem' live peak cnt fail.
Proof.
intros ly S U W mem md ly' S' U' W' mem' md' live peak cnt fail IMG HARU HARU' HK (G1 & G2 & G3 & G4 & R).
assert (K : forall g, In (g, g + 8) FS_PSTAT_FP -> forall v,
  val_mem tfibsegs (mrestrict (w_H W) mem) g 8 v -> val_mem tfibsegs (mrestrict (w_H W') mem') g 8 v).
{ intros g Hg v Hv i Hi.
  destruct (cno_pstat_byte g (g + Z.of_nat i) Hg ltac:(lia) IMG) as (Hi1 & Hi2 & Hi3 & Hi4).
  unfold SHADOW_OFF in Hi4.
  assert (Ha64 : 0 <= g + Z.of_nat i < 2 ^ 64) by lia.
  assert (Hans : ~ (SHADOW_OFF <= g + Z.of_nat i < kHighMemBeg)) by (unfold SHADOW_OFF, kHighMemBeg; lia).
  rewrite <- (Hv i Hi). apply (mbyte_of_aview tfibsegs).
  rewrite <- (cno_unp_out ly' S' U' W' mem' md' _ HARU' Ha64 Hans).
  rewrite <- (cno_unp_out ly S U W mem md _ HARU Ha64 Hans).
  exact (HK _ Hi1 Hi2 Hi3). }
unfold fs_glob, fs_glob_at in *.
split; [exact (K G_LIVE ltac:(unfold FS_PSTAT_FP, G_LIVE; cbn; tauto) live G1)|].
split; [exact (K G_PEAK ltac:(unfold FS_PSTAT_FP, G_PEAK; cbn; tauto) peak G2)|].
split; [exact (K G_COUNT ltac:(unfold FS_PSTAT_FP, G_COUNT; cbn; tauto) cnt G3)|].
split; [exact (K G_FAIL ltac:(unfold FS_PSTAT_FP, G_FAIL; cbn; tauto) fail G4) | exact R].
Qed.

(* ---- the geometry of the walk's windows, read off the walk's journal ---- *)
Lemma cno_geom : forall cx k ly S (W : world tfibsegs) mem md,
  cno_J B cx k ly S W mem md ->
  cno_sp0 cx mod 16 = 0 /\ alloc_ceiling + STK_check_no_overread <= cno_sp0 cx /\ cno_sp0 cx <= 2 ^ 47 /\
  cno_sp0 cx - 176 <= cno_sp1 cx /\ cno_sp1 cx <= cno_sp0 cx - 160 /\ cno_sp1 cx mod 32 = 0 /\
  (cno_sp1 cx - cno_sp0 cx) mod 16 = 0 /\
  ly_stk_lo ly + STK_check_no_overread <= cno_sp0 cx /\ ly_top ly = ly_top (c_ly cx).
Proof.
intros cx k ly S W mem md HJ.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof cno_stk as FS.
pose proof (fsw_realign_facts (cno_sp0 cx - 160) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity))
  as (F1 & F2 & F3).
unfold cno_sp1. rewrite Eslo, Etop.
split; [exact Hal16|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact F2|].
split; [rewrite Zminus_mod, Hal16, F3; reflexivity|]. split; [lia | reflexivity].
Qed.

(* ---- the walk's fake frame, read off the walk's journal ---- *)
Lemma cno_frame : forall cx k ly S U (W : world tfibsegs) mem md,
  AR tfibsegs B (c_ly cx) (c_S cx) (c_W cx) (unpoison (c_U cx) (c_mem cx)) (c_md cx) ->
  cno_J B cx k ly S W (unpoison U mem) md -> ARU tfibsegs B ly S U W mem md ->
  In (1, c_fpos cx) (frames S) /\ cno_F cx = frame_addr ly 1 (c_fpos cx) /\
  4096 <= cno_F cx /\ cno_F cx + 128 <= alloc_ceiling /\ in_app (cno_F cx) 128 /\ cno_F cx mod 32 = 0 /\
  SHADOW_OFF <= cno_SF cx /\ cno_SF cx + 16 <= kHighMemBeg.
Proof.
intros cx k ly S U W mem md HAR0 HJ HARU.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, c_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly HAR0 Hly) as (_ & Efa & _).
assert (EF : cno_F cx = frame_addr ly 1 (c_fpos cx)) by (unfold cno_F; symmetry; apply Efa).
destruct (frames_bounds tfibsegs B LAWS ly S W (unpoison U mem) md 1 (c_fpos cx) HAR Hin) as (H4096 & Hceil & Happ).
destruct (al_frames _ _ LAWS ly S W (unpoison U mem) md 1 (c_fpos cx) HAR Hin) as (Hal32 & _ & _ & _).
change (fs_frame_bytes 1) with 128 in H4096, Hceil, Happ, Hal32.
rewrite <- EF in H4096, Hceil, Happ, Hal32.
pose proof (shadow_addr_bounds (cno_F cx) ltac:(lia)) as (Hs1 & Hs2).
pose proof (shadow_addr_bounds (cno_F cx + 128) ltac:(lia)) as (Hs3 & Hs4).
assert (Hmono : shadow_addr (cno_F cx) + 16 <= shadow_addr (cno_F cx + 128)).
{ unfold shadow_addr. Z.div_mod_to_equations. lia. }
assert (CSO : SHADOW_OFF = 2147450880) by reflexivity.
split; [exact Hin|]. split; [exact EF|]. split; [lia|]. split; [lia|]. split; [exact Happ|].
split; [exact Hal32|]. unfold cno_SF. lia.
Qed.

(* ---- the bytes the walk reads after a call are never shadow bytes of U: the zone's own cells ---- *)
(* the frame's own 16 shadow bytes hold no range of U: a head of U sits in a block, blocks and the frame are
   disjoint (al_sep), and both are 8-granule aligned *)
Lemma cno_sf_not_ush : forall cx k ly S U (W : world tfibsegs) mem md a,
  AR tfibsegs B (c_ly cx) (c_S cx) (c_W cx) (unpoison (c_U cx) (c_mem cx)) (c_md cx) ->
  cno_J B cx k ly S W (unpoison U mem) md -> ARU tfibsegs B ly S U W mem md ->
  FSupoisonU.fs_heads B ly S U -> cno_SF cx <= a < cno_SF cx + 16 -> in_ush U a = false.
Proof.
intros cx k ly S U W mem md a HAR0 HJ HARU FH Ha.
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
destruct (cno_frame cx k ly S U W mem md HAR0 HJ HARU) as (Hin & EF & H4096 & Hceil & Happ & Hal32 & _).
destruct (in_ush U a) eqn:E; [|reflexivity]. exfalso.
unfold in_ush in E. apply existsb_exists in E as (r & Hr & Hcond).
apply andb_prop in Hcond as [L1 L2]. apply Z.leb_le in L1. apply Z.ltb_lt in L2.
destruct (FH r Hr) as (E16 & m & Hm & M16). destruct r as [q s]. cbn [fst snd] in *. subst s.
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md q m HAR Hm) as (Hq16 & _ & _ & _ & _ & _ & _).
pose proof (sep_block_frame tfibsegs B LAWS ly S W (unpoison U mem) md q m 1 (c_fpos cx) HAR Hm Hin) as D.
change (fs_frame_bytes 1) with 128 in D. rewrite <- EF in D.
unfold zdisjoint in D. cbn [fst snd] in D.
unfold cno_SF, shadow_addr in *. change (16 / 8) with 2 in L2.
Z.div_mod_to_equations. lia.
Qed.

(* ================= the call steps ================= *)
Hypothesis ABCMP : FSupoisonU.abcmp_realizesU tfibsegs B PC_bcmp.
Hypothesis IMG : fs_img_facts tfibsegs B.

(* ---- bcmp (x, y, n) at 0x814a4 / 0x814c0 ---- *)
Lemma cno_call_bcmp : cno_call_bcmp_T B.
Proof.
unfold cno_call_bcmp_T.
intros cx k ly S U W regs mem md x y n mx my l HBASE HSITE Hra Hax Hay Han Hnl Hn0 Hrx Hry Hnx Hny Hbx Hby.
destruct HSITE as (HJ & HARU & FH & Hsp & Hs0 & Hgp & Htp & Hret & Hra4 & _ & _).
pose proof HBASE as (HPRE0 & _).
pose proof HPRE0 as (HAPU0 & HRO0).
pose proof HAPU0 as (HAP0 & OK0 & PO0).
pose proof HAP0 as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cno_stk as FS.
assert (CES : ESTACK = 4096) by reflexivity.
assert (CSO : SHADOW_OFF = 2147450880) by reflexivity.
assert (CLSB : kLowShadowBeg = 2147446784) by reflexivity.
assert (CAC : ASAN_CEIL = alloc_ceiling) by reflexivity.
assert (CMM : MALLOC_MAX = 268435456) by reflexivity.
pose proof cno_bcmp_stk as CRTB.
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
destruct (cno_geom cx k ly S W (unpoison U mem) md HJ)
  as (Hal16 & Hceil0 & H47 & Hsp1a & Hsp1b & Hsp1al & Ho16 & Hslo & Etop).
destruct (cno_frame cx k ly S U W mem md HAR0 HJ HARU)
  as (Hinfr & EF & HF4096 & HFceil & HFapp & HFal & HSF1 & HSF2).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (Hspz : spZ regs = cno_sp1 cx)
  by (unfold spZ; rewrite Hsp; unfold w64; apply wz; lia).
(* the two reader blocks *)
destruct Hrx as (Hbkx & Hx16 & Hmx0 & _). destruct Hry as (Hbky & Hy16 & Hmy0 & _).
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md _ _ HAR Hbkx)
  as (_ & Hx4096 & Hxceil & Hxapp & Hxpres & _ & Hxmax).
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md _ _ HAR Hbky)
  as (_ & Hy4096 & Hyceil & Hyapp & Hypres & _ & Hymax).
unfold HEAD in Hbkx, Hbky, Hx4096, Hxceil, Hxapp, Hxpres, Hxmax, Hy4096, Hyceil, Hyapp, Hypres, Hymax.
unfold req_size in Hxceil, Hyceil, Hxpres, Hypres, Hxapp, Hyapp.
assert (Hrq : forall z : Z, 0 < z -> (if z =? 0 then 1 else z) = z)
  by (intros z Hz; destruct (Z.eqb_spec z 0); lia).
rewrite (Hrq (mx + 16) ltac:(lia)) in Hxceil, Hxpres, Hxapp.
rewrite (Hrq (my + 16) ltac:(lia)) in Hyceil, Hypres, Hyapp.
unfold MALLOC_MAX in Hxmax, Hymax.
unfold in_app in Hxapp, Hyapp. destruct Hxapp as (_ & Hxlh). destruct Hyapp as (_ & Hylh).
(* the runtime's premises *)
assert (HE : FSP.ecall_preU tfibsegs B ly S U W regs mem md).
{ exact (fsw_ecall_preU_at B STK_check_no_overread (cno_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(1, c_fpos cx)] ly S U W mem md k regs (cno_sp1 cx - cno_sp0 cx)
    HJ HARU ltac:(lia) Ho16 ltac:(lia) ltac:(unfold ESTACK; lia) Hret
    ltac:(rewrite Hgp; exact Hgp0) ltac:(rewrite Htp; exact Htp0)). }
assert (Hpr : forall a, spZ regs - 2 * ESTACK <= a < spZ regs -> apresent (w_H W) mem a).
{ intros a Ha. apply (fsw_apresent_unpoison B ly S U W mem md a HARU); [lia|].
  apply Hpres. lia. }
assert (Hsrc : forall (p m : Z), 0 < m -> 4096 <= p - 16 ->
  p - 16 + (m + 16) <= alloc_ceiling ->
  (p - 16 + (m + 16) <= kLowShadowBeg \/ (kHighMemBeg <= p - 16 /\ p - 16 + (m + 16) <= ASAN_CEIL)) ->
  n <= m ->
  (forall a, p - 16 <= a < p - 16 + (m + 16) -> apresent (w_H W) (unpoison U mem) a /\ ~ aowned B ly S a) ->
  src_ok tfibsegs W regs mem p n).
{ intros p m Hm0 H4096 Hcl Hlh Hnm Hpp a Ha. split.
  - destruct (Hpp a ltac:(lia)) as (Hp & _).
    destruct Hp as (Hh & b & Hb). unfold aview, mbyte, mrestrict. rewrite Hh.
    unfold unpoison in Hb. destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:Eu.
    + exfalso. rewrite (wz a ltac:(lia)) in Eu.
      pose proof (ush_facts tfibsegs B ly S U W mem md a HARU Eu) as (_ & Hl1 & Hl2). lia.
    + rewrite Hb. discriminate.
  - lia. }
assert (HSx : src_ok tfibsegs W regs mem x n)
  by (apply (Hsrc x mx); [lia | lia | lia | exact Hxlh | lia | exact Hxpres]).
assert (HSy : src_ok tfibsegs W regs mem y n)
  by (apply (Hsrc y my); [lia | lia | lia | exact Hylh | lia | exact Hypres]).
assert (Hagree : forall i, 0 <= i < n -> aview tfibsegs (w_H W) mem (x + i) = aview tfibsegs (w_H W) mem (y + i)).
{ intros i Hi.
  assert (Hj : (Z.to_nat i < length l)%nat) by lia.
  destruct (Hbx (Z.to_nat i) Hj) as (Vx & _). destruct (Hby (Z.to_nat i) Hj) as (Vy & _).
  pose proof (Vx 0%nat ltac:(lia)) as Ex. pose proof (Vy 0%nat ltac:(lia)) as Ey.
  cbn [Z.of_nat] in Ex, Ey. rewrite Z.add_0_r in Ex, Ey.
  rewrite Z2Nat.id in Ex, Ey by lia.
  unfold aview. rewrite Ex, Ey. reflexivity. }
(* the shadow premises of the two ranges, on the MACHINE's memory: the body of a reader block carries no range of
   U (its own head is the 16 bytes below it, every other head sits in another block), so the unpoisoned view and
   the machine's agree on its shadow; in the hull the machine shows 0xf7 where U poisons *)
assert (Hsh : forall (p m : Z), In (p - 16, m + 16) (ablocks B ly S) -> 0 < m -> 4096 <= p - 16 ->
  p - 16 + (m + 16) <= alloc_ceiling -> n <= m ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF p n /\
  shadow_hull_vis (aview tfibsegs (w_H W) mem) p n).
{ intros p m Hbk Hm0 H4096 Hcl Hnm.
  assert (Hrs : req_size (m + 16) = m + 16) by (unfold req_size; destruct (Z.eqb_spec (m + 16) 0); lia).
  split.
  - apply (range_addressable_agree (aview tfibsegs (w_H W) (unpoison U mem))).
    + intros x0 Hx0.
      assert (Hb : SHADOW_OFF <= shadow_addr x0 < 2 ^ 48) by (apply cno_sh_rng; lia).
      replace (shadow_of_addr SHADOW_OFF x0) with (shadow_addr x0)
        by (unfold shadow_of_addr, shadow_addr; lia).
      symmetry. apply (cno_unp_off W U mem (shadow_addr x0) ltac:(lia)).
      exact (cno_body_not_ush ly S U W mem md (p - 16) (m + 16) x0 HAR FH Hbk ltac:(lia)).
    + apply (range_addressable_of_block tfibsegs B LAWS ly S W (unpoison U mem) md (p - 16) (m + 16));
        [exact HAR | exact Hbk | lia | lia].
  - intros s Hs.
    destruct (al_shadow _ _ LAWS ly S W (unpoison U mem) md _ _ HAR Hbk) as (_ & Hhv).
    rewrite Hrs in Hhv.
    assert (Hb1 : SHADOW_OFF <= shadow_addr p < 2 ^ 48) by (apply cno_sh_rng; lia).
    assert (Hb2 : SHADOW_OFF <= shadow_addr (p + n - 1) < 2 ^ 48) by (apply cno_sh_rng; lia).
    assert (Hd1 : 0 <= shadow_addr p / 8 * 8) by (pose proof (Z.div_pos (shadow_addr p) 8 ltac:(lia) ltac:(lia)); lia).
    assert (Hd2 : shadow_addr (p + n - 1) / 8 * 8 <= shadow_addr (p + n - 1))
      by (pose proof (Z.mul_div_le (shadow_addr (p + n - 1)) 8 ltac:(lia)); lia).
    apply (cno_raw_vis ly S U W mem md s HARU ltac:(lia)).
    exact (shadow_hull_vis_sub _ (p - 16) (m + 16) p n Hhv ltac:(lia) ltac:(lia) ltac:(lia) s Hs). }
destruct (Hsh x mx Hbkx Hmx0 ltac:(lia) ltac:(lia) ltac:(lia)) as (HRx & HHx).
destruct (Hsh y my Hbky Hmy0 ltac:(lia) ltac:(lia) ltac:(lia)) as (HRy & HHy).
(* the call, with the caller's journal put back on the memory the runtime leaves *)
eapply SRr_mono.
{ eapply (fsw_intrin_atU B STK_check_no_overread (cno_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(1, c_fpos cx)] ly S U W mem md k U
    (fun a => spZ regs - 2 * ESTACK <= a < spZ regs) (getr regs 1) (cfg_at tfibsegs PC_bcmp regs mem md)
    (fun regs' mem' md' => aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2 * ESTACK <= a < spZ regs) ->
          aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a)) HJ).
  - eapply SRr_mono.
    { exact (ABCMP ly S U W regs mem md x y n HE ltac:(lia) Hpr Hax Hay Han
        ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HSx HSy
        ltac:(intros a Ha; lia) ltac:(intros a Ha; lia)
        ltac:(unfold amem_range; lia) ltac:(unfold amem_range; lia)
        HRx ltac:(intros _; exact HHx) HRy ltac:(intros _; exact HHy)). }
    cbv beta. intros W1 c1 _ (-> & regs1 & mem1 & md1 & v & -> & HARU1 & HP1 & Hmat1 & Hv & Hiff & Hkeep1 & Hpres1).
    split; [reflexivity|]. exists regs1, mem1, md1.
    split; [unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
    split; [exact HARU1|]. split; [exact Hmat1|].
    split; [intros a Ha Hw; exact (cno_unp_cong W U mem mem1 a (Hkeep1 a Ha Hw))|].
    split; [intros a Hp; exact (cno_unp_pres W U mem mem1 a (Hpres1 a) Hp)|].
    split; [exact HP1|]. split; [rewrite Hv; apply (proj2 Hiff); exact Hagree | exact Hkeep1].
  - intros a Ha. left. left. lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HARU2 & HP2 & Hz2 & Hkeep2).
unfold cno_ret. exists ly, S, regs2, mem2, md2.
split; [unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [replace (k + 0) with k by lia; exact HJ2|].
split; [exact HARU2|]. split; [exact FH|]. split; [exact HP2|].
assert (HZ : forall a, cno_zone cx a -> aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) mem a).
{ intros a Ha. unfold cno_zone in Ha. apply Hkeep2; lia. }
split; [intros a Ha _; exact (HZ a Ha)|].
split.
{ intros p0 n0 i Hb0 Hb1 Hi _.
  destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md p0 n0 HAR Hb0) as (_ & Hp4 & Hpc & _ & _ & _ & _).
  apply Hkeep2; lia. }
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact Hz2|]. unfold STK_RT_BCMP. rewrite <- Hspz. exact Hkeep2.
Qed.

(* ---- __wrap_free (p) at 0x814e4 / 0x814ec / 0x814f4 ---- *)
Hypothesis AFREE : FSupoisonU.afree_realizesU tfibsegs B.
Hypothesis HFRE : pc_wrap_free (as_code B) = PC_free.
Hypothesis FS_ENV : api_env tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
(* a block occurs once in ablocks: the mapped ranges are pairwise disjoint (al_sep) and no range is empty *)
Lemma cno_no_dup : forall ly S (W : world tfibsegs) mem md l1 l2 p m,
  AR tfibsegs B ly S W mem md -> ablocks B ly S = l1 ++ (p, m) :: l2 -> ~ In (p, m) (l1 ++ l2).
Proof.
intros ly S W mem md l1 l2 p m HAR E Hin.
assert (Hblk : In (p, m) (ablocks B ly S)) by (rewrite E; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly S W mem md p m HAR Hblk) as (_ & _ & _ & _ & _ & PW & Hmax).
assert (Hrs : 0 < req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
rewrite E in PW.
apply in_app_or in Hin as [Hin | Hin]; apply in_split in Hin as (A & C & EA).
- subst l1. rewrite !map_app in PW. cbn [map app] in PW.
  pose proof (YCbq.pairwise_In2 zdisjoint _ (p, req_size m) (p, req_size m)
    (map (fun b : Z * Z => (fst b, req_size (snd b))) A)
    (map (fun b : Z * Z => (fst b, req_size (snd b))) C)
    (map (fun b : Z * Z => (fst b, req_size (snd b))) l2) PW
    ltac:(rewrite <- app_assoc; reflexivity)) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. lia.
- subst l2. rewrite !map_app in PW. cbn [map app] in PW.
  pose proof (YCbq.pairwise_In2 zdisjoint _ (p, req_size m) (p, req_size m)
    (map (fun b : Z * Z => (fst b, req_size (snd b))) l1)
    (map (fun b : Z * Z => (fst b, req_size (snd b))) A)
    (map (fun b : Z * Z => (fst b, req_size (snd b))) C) PW ltac:(rewrite map_app; reflexivity)) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.

(* the chain the walk hands a callee: check_no_overread's own record (its entry sp, ra and s0, read back from the
   two words the prologue saved at sp0 - 8 and sp0 - 16) on top of the caller chain, by YCbq.achain_push (its room
   premise sp0 < ly_top - 16 is the spec's `spZ regs + 32 <= ly_top ly`) *)
Lemma cno_chain_at : forall cx k ly S U (W : world tfibsegs) regs mem md,
  cno_base B cx -> cno_site B cx k ly S U W regs mem md ->
  chain_pre ly (aview tfibsegs (w_H W) (unpoison U mem)) regs
    ((cno_sp0 cx, raZ (c_regs cx), s0Z (c_regs cx)) :: c_ch cx).
Proof.
intros cx k ly S U W regs mem md HBASE HSITE.
destruct HSITE as (HJ & HARU & FH & Hsp & Hs0 & Hgp & Htp & Hret & Hra4 & Hw8 & Hw16).
pose proof HBASE as (HPRE0 & _).
assert (Hroom0 : spZ (c_regs cx) + 32 <= ly_top (c_ly cx))
  by (pose proof HBASE as HB'; unfold cno_base in HB'; tauto).
pose proof HPRE0 as (HAPU0 & HRO0). pose proof HAPU0 as (HAP0 & OK0 & PO0).
pose proof HAP0 as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cno_stk as FS.
destruct (cno_geom cx k ly S W (unpoison U mem) md HJ)
  as (Hal16 & Hceil0 & H47 & Hsp1a & Hsp1b & Hsp1al & Ho16 & Hslo & Etop).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & Hout & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (_ & _ & _ & _ & Hshi & H47' & _ & Htop & Htop2).
assert (Hspz : spZ regs = cno_sp1 cx) by (unfold spZ; rewrite Hsp; unfold w64; apply wz; lia).
assert (Hs0z : s0Z regs = cno_sp0 cx) by (unfold s0Z; rewrite Hs0; unfold w64; apply wz; lia).
(* the entry chain, at the call's layout *)
assert (HchL : achain ly (aview tfibsegs (w_H (c_W cx)) (unpoison (c_U cx) (c_mem cx)))
  (cno_sp0 cx) (s0Z (c_regs cx)) (c_ch cx))
  by (apply (achain_ly_top (c_ly cx) ly); [exact Etop | exact Hch0]).
(* the call's view agrees with the entry's at and above sp0 *)
assert (Hagree : forall a, cno_sp0 cx <= a < 2 ^ 64 ->
  aview tfibsegs (w_H W) (unpoison U mem) a = aview tfibsegs (w_H (c_W cx)) (unpoison (c_U cx) (c_mem cx)) a)
  by (intros a Ha; apply Hout; lia).
(* the two saved words, carried to the unpoisoned view (the walk's stack is above kHighMemBeg) *)
assert (Hunp : forall a, cno_sp0 cx - 16 <= a < cno_sp0 cx + 8 ->
  aview tfibsegs (w_H W) (unpoison U mem) a = aview tfibsegs (w_H W) mem a)
  by (intros a Ha; apply (cno_unp_out ly S U W mem md a HARU); lia).
assert (Hw8' : rdword (aview tfibsegs (w_H W) (unpoison U mem)) (cno_sp0 cx - 8) = Some (raZ (c_regs cx))).
{ rewrite (rdword_ext (aview tfibsegs (w_H W) mem) (aview tfibsegs (w_H W) (unpoison U mem)) (cno_sp0 cx - 8)
    ltac:(intros j Hj; apply Hunp; lia)). exact Hw8. }
assert (Hw16' : rdword (aview tfibsegs (w_H W) (unpoison U mem)) (cno_sp0 cx - 16) = Some (s0Z (c_regs cx))).
{ rewrite (rdword_ext (aview tfibsegs (w_H W) mem) (aview tfibsegs (w_H W) (unpoison U mem)) (cno_sp0 cx - 16)
    ltac:(intros j Hj; apply Hunp; lia)). exact Hw16. }
apply (achain_chain_pre ly _ (spZ regs) (cno_sp0 cx) _ regs); [|lia|exact Hs0z|exact Hra4].
exact (achain_push ly _ _ (cno_sp0 cx) (s0Z (c_regs cx)) (raZ (c_regs cx)) (c_ch cx) (spZ regs)
  HchL ltac:(lia) Hagree Hw8' Hw16' Hra40 ltac:(lia) ltac:(lia) ltac:(rewrite Etop; unfold cno_sp0; lia) ltac:(lia)).
Qed.

Lemma cno_call_afree : cno_call_afree_T B.
Proof.
unfold cno_call_afree_T.
intros cx k ly S U W regs mem md p m live peak cnt fail HBASE HSITE Hra Hap Hp0 Hblk Hfresh HUout HGL Hk.
pose proof (cno_chain_at cx k ly S U W regs mem md HBASE HSITE) as HCH.
destruct HSITE as (HJ & HARU & FH & Hsp & Hs0 & Hgp & Htp & Hret & Hra4 & Hw8 & Hw16).
pose proof HBASE as (HPRE0 & _).
pose proof HPRE0 as (HAPU0 & HRO0). pose proof HAPU0 as (HAP0 & OK0 & PO0).
pose proof HAP0 as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
assert (Hev0 : st_nev (c_S cx) + EV_check_no_overread <= EV_MAX)
  by (pose proof HBASE as HB'; unfold cno_base in HB'; tauto).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cno_stk as FS.
assert (CES : ESTACK = 4096) by reflexivity.
assert (CAS : ASTACK = 16384) by reflexivity.
assert (CSO : SHADOW_OFF = 2147450880) by reflexivity.
assert (CLSB : kLowShadowBeg = 2147446784) by reflexivity.
assert (CAC : ASAN_CEIL = alloc_ceiling) by reflexivity.
assert (CEV : EV_check_no_overread = 12) by reflexivity.
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
destruct (cno_geom cx k ly S W (unpoison U mem) md HJ)
  as (Hal16 & Hceil0 & H47 & Hsp1a & Hsp1b & Hsp1al & Ho16 & Hslo & Etop).
destruct (cno_frame cx k ly S U W mem md HAR0 HJ HARU)
  as (Hinfr & EF & HF4096 & HFceil & HFapp & HFal & HSF1 & HSF2).
assert (Hspz : spZ regs = cno_sp1 cx) by (unfold spZ; rewrite Hsp; unfold w64; apply wz; lia).
assert (Hs0z : s0Z regs = cno_sp0 cx) by (unfold s0Z; rewrite Hs0; unfold w64; apply wz; lia).
(* the event budget: the walk's journal has used k of check_no_overread's twelve *)
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & Hk0 & _).
assert (Hev : st_nev S < EV_MAX) by lia.
(* the freed block's own bounds *)
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md p m HAR Hblk)
  as (Hp16 & Hp4096 & Hpceil & Hpapp & Hppres & _ & Hpmax).
assert (Hrs : 0 < req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
(* the call, on a CALL-RELATIVE journal (window [sp1 - ASTACK, sp1), footprint the freed block, start = the call):
   fsw_aj_freeU's journal starts on the call's own U, while the walk's starts on the entry's; the callee journal is
   then composed into the walk's by fsw_ajournal_sub4, the freed block being one of the walk's temporary blocks *)
pose proof (ajournal_sub_init tfibsegs B STK_check_no_overread (cno_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx)
  (c_W cx) (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(1, c_fpos cx)] ly S W (unpoison U mem) md k ASTACK
  (cno_sp1 cx) (ablocks_fp [(p, m)]) (cno_sp1 cx - cno_sp0 cx) HJ ltac:(lia) Ho16 ltac:(lia) ltac:(lia)
  ltac:(lia)) as HJ1.
replace (cfg_at tfibsegs PC_free regs mem md)
  with (mkCfg (mkst regs (Z_to_bv 64 (pc_wrap_free (as_code B))) mem (seg_rom tfibsegs)) md)
  by (rewrite HFRE; reflexivity).
eapply SRr_mono.
{ exact (FSW_malloc_free.fsw_aj_freeU B FS_ENV ML AFREE W regs mem ASTACK (cno_sp1 cx) (ablocks_fp [(p, m)])
    ly S W mem md [] ly S U md 0 p m 0 (getr regs 1) _ HJ1 HARU Hblk HUout Hap ltac:(lia) eq_refl ltac:(lia)
    ltac:(lia) ltac:(rewrite Hgp; exact Hgp0) ltac:(rewrite Htp; exact Htp0) eq_refl Hret Hev HCH
    ltac:(intros _ i Hi; exact (inFP_ablocks_fp [(p, m)] p m i (or_introl eq_refl) Hi))). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HARU2 & HJ2c & HP2 & (l1 & l2 & EabC & Eab2)
  & Hfrs2 & HK).
pose proof HK as (HK1 & HK2 & HK3 & HK4 & _ & _).
pose proof (ARU_AR tfibsegs B ly2 S2 U W2 mem2 md2 HARU2) as HAR2.
(* the walk's journal, grown by the callee's one event *)
assert (HJ2 : cno_J B cx (k + 1) ly2 S2 W2 (unpoison U mem2) md2).
{ unfold cno_J. replace (k + 1) with (k + (0 + 1)) by lia.
  change [(1, c_fpos cx)] with ([] ++ [(1, c_fpos cx)]).
  apply (fsw_ajournal_sub4 B STK_check_no_overread (cno_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(1, c_fpos cx)] ly S W (unpoison U mem) md k ASTACK (cno_sp1 cx)
    (ablocks_fp [(p, m)]) [] ly2 S2 W2 (unpoison U mem2) md2 (0 + 1) HJ HJ2c ltac:(lia) ltac:(lia)).
  intros a Ha. right. left.
  destruct (inFP_ablocks_fp_inv [(p, m)] a Ha) as (p' & m' & [E | []] & Ha').
  injection E as <- <-. exists p, m. split; [exact Hblk|]. split; [exact Hfresh | exact Ha']. }
(* the freed block is gone, so every head of U still sits in a live block *)
assert (FH2 : FSupoisonU.fs_heads B ly2 S2 U).
{ intros r Hr. destruct (FH r Hr) as (E16 & m' & Hm' & M16).
  destruct (HUout r Hr) as [Hlt | Hgt].
  - split; [exact E16|]. exists m'. split; [|exact M16].
    rewrite Eab2. rewrite EabC in Hm'. apply in_app_or in Hm' as [Hm' | [Hm' | Hm']].
    + apply in_or_app; left; exact Hm'.
    + exfalso. injection Hm' as E1 _. lia.
    + apply in_or_app; right; exact Hm'.
  - split; [exact E16|]. exists m'. split; [|exact M16].
    rewrite Eab2. rewrite EabC in Hm'. apply in_app_or in Hm' as [Hm' | [Hm' | Hm']].
    + apply in_or_app; left; exact Hm'.
    + exfalso. injection Hm' as E1 _. lia.
    + apply in_or_app; right; exact Hm'. }
unfold cno_ret. exists ly2, S2, regs2, mem2, md2.
split; [unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [exact HJ2|]. split; [exact HARU2|]. split; [exact FH2|]. split; [exact HP2|].
(* the walk's own bytes: the saved words and the slots lie above the callee's window, the frame and its shadow are
   the walk's own frame, and the freed block meets none of them (al_sep) *)
assert (Hfrdisj : forall a, cno_F cx <= a < cno_F cx + 128 \/ cno_SF cx <= a < cno_SF cx + 16 ->
  ~ (p <= a < p + req_size m)).
{ intros a Ha HE.
  pose proof (sep_block_frame tfibsegs B LAWS ly S W (unpoison U mem) md p m 1 (c_fpos cx) HAR Hblk Hinfr) as D.
  change (fs_frame_bytes 1) with 128 in D. rewrite <- EF in D. unfold zdisjoint in D. cbn [fst snd] in D.
  destruct (al_frames _ _ LAWS ly S W (unpoison U mem) md 1 (c_fpos cx) HAR Hinfr) as (_ & _ & _ & Hsp').
  change (fs_frame_bytes 1 / 8) with 16 in Hsp'. rewrite <- EF in Hsp'.
  destruct Ha as [Ha | Ha]; [lia|].
  (* the frame's shadow lies in [SHADOW_OFF, kHighMemBeg), the freed block is application memory *)
  unfold in_app in Hpapp. lia. }
assert (HZ : forall a, cno_zone cx a -> aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W) mem a).
{ intros a Ha.
  assert (Hb : 0 <= a < 2 ^ 64) by (unfold cno_zone in Ha; lia).
  unfold cno_zone in Ha. destruct Ha as [Ha | [Ha | [Ha | Ha]]].
  - rewrite <- (cno_unp_out ly2 S2 U W2 mem2 md2 a HARU2 Hb ltac:(lia)).
    rewrite <- (cno_unp_out ly S U W mem md a HARU Hb ltac:(lia)). apply HK1; lia.
  - rewrite <- (cno_unp_out ly2 S2 U W2 mem2 md2 a HARU2 Hb ltac:(lia)).
    rewrite <- (cno_unp_out ly S U W mem md a HARU Hb ltac:(lia)). apply HK1; lia.
  - unfold in_app, kLowShadowBeg, ASAN_CEIL in HFapp.
    rewrite <- (cno_unp_out ly2 S2 U W2 mem2 md2 a HARU2 Hb ltac:(lia)).
    rewrite <- (cno_unp_out ly S U W mem md a HARU Hb ltac:(lia)).
    apply (HK4 1 (c_fpos cx) a Hinfr); [left; unfold frame_rng, in_zr; cbn [fst snd];
      change (fs_frame_bytes 1) with 128; rewrite <- EF; lia | exact (Hfrdisj a ltac:(left; lia))].
  - unfold cno_SF in Ha.
    rewrite <- (cno_unp_off W2 U mem2 a Hb
      (cno_sf_not_ush cx (k + 1) ly2 S2 U W2 mem2 md2 a HAR0 HJ2 HARU2 FH2 ltac:(unfold cno_SF; lia))).
    rewrite <- (cno_unp_off W U mem a Hb
      (cno_sf_not_ush cx k ly S U W mem md a HAR0 HJ HARU FH ltac:(unfold cno_SF; lia))).
    apply (HK4 1 (c_fpos cx) a Hinfr).
    + right. unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 1 / 8) with 16. rewrite <- EF. lia.
    + exact (Hfrdisj a ltac:(right; unfold cno_SF; lia)). }
split; [intros a Ha _; exact (HZ a Ha)|].
split.
{ intros p0 n0 i Hb0 Hb1 Hi _.
  destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md p0 n0 HAR Hb0) as (_ & Hp04 & Hp0c & Hp0app & _ & _ & _).
  assert (Hrs0 : 0 < req_size n0) by lia.
  assert (Hne : (p0, n0) <> (p, m)).
  { intros E. rewrite E in Hb1. rewrite Eab2 in Hb1.
    exact (cno_no_dup ly S W (unpoison U mem) md l1 l2 p m HAR EabC Hb1). }
  pose proof (sep_blocks tfibsegs B LAWS ly S W (unpoison U mem) md p0 n0 p m HAR Hb0 Hblk Hne) as D.
  unfold zdisjoint in D. cbn [fst snd] in D.
  assert (Hb64 : 0 <= p0 + i < 2 ^ 64) by lia.
  rewrite <- (cno_unp_out ly2 S2 U W2 mem2 md2 (p0 + i) HARU2 Hb64
    ltac:(unfold in_app, kLowShadowBeg, ASAN_CEIL in Hp0app; lia)).
  rewrite <- (cno_unp_out ly S U W mem md (p0 + i) HARU Hb64
    ltac:(unfold in_app, kLowShadowBeg, ASAN_CEIL in Hp0app; lia)).
  apply (HK2 p0 n0 i); [exact Hb0 | lia | cbv beta; lia]. }
split.
- exists l1, l2. split; [exact EabC | exact Eab2].
- exact (cno_glob_kept ly S U W mem md ly2 S2 U W2 mem2 md2 live peak cnt fail IMG HARU HARU2 HK3 HGL).
Qed.

End T.