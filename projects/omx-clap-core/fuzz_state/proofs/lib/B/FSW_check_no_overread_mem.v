(* check_no_overread B 0x8124c (fs.c), fs.asan-ubsan, a Theorem Labs lane: the three runtime call steps of the walk between the
   second past_nul return (0x81394) and the lifetime-start stores (0x81414), proved against the call-step interface of
   lib/B/FSW_check_no_overread.v Section I (cno_base / cno_site / cno_ret; statements cno_call_mal_T, cno_call_mcpy_T,
   cno_call_mset_T of the B INTERFACE commit decf0bae273), exactly as committed there:
   - cno_call_mal   __wrap_malloc (n + 18) at 0x8139c (callee PC_malloc 0x530e4, ra 0x813a0): the B kit's
     lib/B/FSW_malloc_free.v fsw_aj_malloc04U (ALLOC's kit, ea464b7bd5d; used by path) on the call-relative journal
     (YCbq.ajournal_sub_init), composed back into the walk's journal (YCbq.ajournal_sub). The model's malloc answers a
     block at 4096 <= t, so the post carries t <> 0. B-SPECIFIC: the post also carries range_addressable over
     [t, t + n + 18) at the return (B's first inline ASan check, 0x813c8-0x813d4 for the store of t[n] at 0x813dc, comes
     before the memset): the block is new, so it is disjoint from every block live at the call (YCbq.sep_blocks_pos),
     so no range of U shadows it (FSupoison.ARU_shadow_out_block at the call's ARU), and the post's AR makes its shadow
     addressable (YCbq.range_addressable_of_block).
   - cno_call_mcpy  __asan_memcpy (t, d, n) at 0x813b8 (callee PC_memcpy 0x51d90, ra 0x813bc, only when n > 0: n = 0
     skips it at 0x813a8 `beqz s6`): AMEMCPY (aintrin_realizesU OCpy) through FSW_K.fsw_intrin_atU. d's bytes and
     shadow are rebuilt from cno_base (the journal keeps the entry block of d, the entry ARU makes its shadow no head of
     U); t is the walk's last block, after every entry block.
   - cno_call_mset  __asan_memset (t + n + 1, 0, 16) at 0x813f4 (callee PC_memset 0x5222c, ra 0x813f8; A's is
     (t + n, 0, 17)): AMEMSET (OSet), the same way; the post gives range_addressable over [t, t + n + 18) again.
   GUARDS (MEASURED: neutral_dis listing (internal path),
   lines 86-119 and 236-244, re-read by this lane 2026-10-29):
   - 0x813a0 `beqz a0, 0x815f4` (abort block, before_abort 0x815f4 / abort 0x815f8): UNTAKEN. cno_call_mal's post gives
     a0 = t with t <> 0 (4096 <= t: the model's malloc does not answer NULL under blocks_bytes S + (n + 18) <= LIVE_MAX,
     the call's budget premise, FSW_malloc_free.fsw_aj_malloc04U); the top file closes the taken arm at its branch.
   - the straight-line code 0x813bc-0x813f0 and 0x813fc-0x81420 (UBSan U1 0x813c0 `bltu s7,s6`, U2 0x813e0
     `beq a0,a1` with a1 = -1, U3 0x813f8 `bltu s7,s6`, each to unimp 0x815fc; the inline ASan checks 0x813c8-0x813d4
     (slow path 0x81600-0x81604, report 0x81608) and 0x81404-0x81410 (slow path 0x8160c-0x81610, report 0x81614)) runs
     BETWEEN the call steps, in the top file's segment runs (the interface's text: "the top file carries it across
     __asan_memcpy"). This file gives the facts that close those guards there: range_addressable [t, t + n + 18)
     (cno_call_mal's post, and cno_call_mset's post), and cno_ubsan_t: 4096 <= t, t + n + 18 <= alloc_ceiling < 2 ^ 47
     (the block lies in application memory: YCbq.al_blocks under the post's AR) and n <= PRESET_FILE_MAX_BYTES
     = 3 * 2 ^ 20 (cno_base), so t + n + 17 < 2 ^ 64 - 1 and no UBSan guard traps. No new premise.
   Template (text only): lib/A/FSW_check_no_overread_mem.v at a working branch 59f0008819f (another working branch at
   91de3f442c1's text). The walk's own helpers come from lib/B/FSW_check_no_overread.v (core c20439f478a): cno_stk,
   cno_chain, cno_pstat_img, cno_aview_unp. Kit lemmas are used by path (lib/B FSW_K, FSW_rd, FSW_frame, FSW_strkit,
   FSW_malloc_free; lib/A's image-generic FSupoison, FSupoisonU, FSH_Gen; Reusable); none is copied.
   rule 24: proves no function of its own (kind: call-step lemmas of check_no_overread's walk; the lookup line is the
   walk's, lib/B/FSW_check_no_overread.v header). *)
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
YB1v YB1w FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_ret FSW_rres FSW_frame FSW_strkit FSW_rd FSH_Fn_cno FSH_Fn_alloc
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

Section M. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
(* the callee contracts these steps use (CTX-free S0 forms; lib/B/FSH_Rt.v fr_malloc / FsRt's intrinsic fields) *)
Hypothesis FS_ENV : api_env tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis AMALLOC : FSupoisonU.amalloc_realizesU tfibsegs B.
Hypothesis AMEMCPY : FSupoisonU.aintrin_realizesU tfibsegs B OCpy PC_memcpy.
Hypothesis AMEMSET : FSupoisonU.aintrin_realizesU tfibsegs B OSet PC_memset.
Hypothesis IMG : fs_img_facts tfibsegs B.
Hypothesis HMAL : pc_wrap_malloc (as_code B) = PC_malloc.

(* ================= byte-level helpers (lib/A _mem.v text) ================= *)
Lemma cno_ra_raw : forall ly S U (W : world tfibsegs) m md p k a len, ARU tfibsegs B ly S U W m md ->
  In (p, k) (ablocks B ly S) -> p <= a -> a + len <= p + req_size k ->
  (forall x, a <= x < a + len -> in_ush U (bv_unsigned (Z_to_bv 64 (shadow_addr x))) = false) ->
  range_addressable (aview tfibsegs (w_H W) m) SHADOW_OFF a len.
Proof.
intros ly S U W m md p k a len H Hin H1 H2 Hu.
apply (range_addressable_agree (aview tfibsegs (w_H W) (unpoison U m))).
- intros x Hx. change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x).
  symmetry. apply (aview_unpoison_out tfibsegs). exact (Hu x Hx).
- exact (range_addressable_of_block tfibsegs B LAWS ly S W (unpoison U m) md p k a len
    (ARU_AR _ _ _ _ _ _ _ _ H) Hin H1 H2).
Qed.
Lemma cno_hull_raw : forall ly S U (W : world tfibsegs) m md a len, ARU tfibsegs B ly S U W m md ->
  shadow_hull_vis (aview tfibsegs (w_H W) (unpoison U m)) a len -> shadow_hull_vis (aview tfibsegs (w_H W) m) a len.
Proof.
intros ly S U W m md a len (HAR & OK & PO) Hh s Hs.
rewrite aview_mod. destruct (in_ush U (s mod 2 ^ 64)) eqn:Ei.
- rewrite (PO _ Ei). discriminate.
- rewrite <- aview_mod. rewrite <- (aview_unpoison_out tfibsegs (w_H W) U m s); [exact (Hh s Hs)|].
  rewrite Z_to_bv_unsigned. exact Ei.
Qed.
Lemma cno_ush_src : forall (W : world tfibsegs) mem U d n,
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF d n ->
  upoisoned tfibsegs W mem U -> forall x, d <= x < d + n -> 0 <= x < 2 ^ 63 ->
  in_ush U (bv_unsigned (Z_to_bv 64 (shadow_addr x))) = false.
Proof.
intros W mem U d n Hra Hpo x Hx Hx0.
assert (Hs : 0 <= shadow_addr x < 2 ^ 64).
{ unfold shadow_addr, SHADOW_OFF. split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
  pose proof (Z.div_le_mono x (2 ^ 63) 8 ltac:(lia) ltac:(lia)). change (2 ^ 63 / 8) with (2 ^ 60) in H. lia. }
rewrite wz by exact Hs. destruct (in_ush U (shadow_addr x)) eqn:Ei; [|reflexivity].
exfalso. pose proof (Hpo _ Ei) as Hp. destruct (Hra x Hx) as (s & Hsv & Hok).
change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x) in Hsv. rewrite Hp in Hsv. injection Hsv as <-.
unfold saddr_ok in Hok. lia.
Qed.
Lemma cno_garr8 : forall H m base l, Forall (fun z => 0 <= z < 256) l ->
  (forall j, (j < length l)%nat -> aview tfibsegs H m (base + Z.of_nat j) = Some (nth j l 0)) ->
  garr8 tfibsegs (mrestrict H m) base l.
Proof.
intros H m base l Hb Hv j Hj.
assert (Bj : 0 <= nth j l 0 < 256) by (exact (proj1 (Forall_nth _ l) Hb j 0 Hj)).
split; [|exact Bj]. intros k Hk. assert (k = 0%nat) as -> by lia.
destruct (aview_byte tfibsegs H m _ _ (Hv j Hj)) as (b & Hm & Ev & _).
rewrite Z.add_0_r. rewrite Hm. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
unfold YO0f.le_byte. cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.shiftr_0_r. change (2 ^ (8 * 1)) with 256.
rewrite !Z.mod_small by lia. unfold bv_wrap. change (bv_modulus 8) with 256. rewrite Z.mod_small by lia. lia.
Qed.
Lemma cno_aview_of_garr8 : forall H m base l j, garr8 tfibsegs (mrestrict H m) base l -> (j < length l)%nat ->
  aview tfibsegs H m (base + Z.of_nat j) = Some (nth j l 0).
Proof.
intros H m base l j Hg Hj. destruct (Hg j Hj) as [Hv Bj]. specialize (Hv 0%nat ltac:(lia)).
rewrite Z.add_0_r in Hv. unfold aview. rewrite Hv. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold YO0f.le_byte. cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.shiftr_0_r. change (2 ^ (8 * 1)) with 256.
rewrite !Z.mod_small by lia. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. lia.
Qed.
Lemma cno_glob_kept : forall (W W' : world tfibsegs) mem mem' live peak cnt fail,
  fs_glob tfibsegs W mem live peak cnt fail ->
  (forall a, inFP FS_PSTAT_FP a -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) ->
  fs_glob tfibsegs W' mem' live peak cnt fail.
Proof.
intros W W' mem mem' live peak cnt fail (G1 & G2 & G3 & G4 & GR) K.
assert (KV : forall g v, In (g, g + 8) FS_PSTAT_FP -> val_mem tfibsegs (mrestrict (w_H W) mem) g 8 v ->
  val_mem tfibsegs (mrestrict (w_H W') mem') g 8 v).
{ intros g v Hg Hv. apply (val_mem_kept tfibsegs (w_H W) (w_H W') mem mem' g 8 v); [|exact Hv].
  intros k Hk. apply K. apply (inFP_FS_PSTAT_FP g Hg). cbn in Hk. lia. }
unfold fs_glob, fs_glob_at. split; [|split; [|split; [|split]]].
- apply KV; [unfold FS_PSTAT_FP, G_LIVE; cbn; tauto | exact G1].
- apply KV; [unfold FS_PSTAT_FP, G_PEAK; cbn; tauto | exact G2].
- apply KV; [unfold FS_PSTAT_FP, G_COUNT; cbn; tauto | exact G3].
- apply KV; [unfold FS_PSTAT_FP, G_FAIL; cbn; tauto | exact G4].
- exact GR.
Qed.
Lemma cno_rdword_ext : forall (rd rd' : reader) a, (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) ->
  rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. unfold rdword.
assert (H0 : rd' a = rd a) by (rewrite <- (Z.add_0_r a); apply H; lia).
rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.
(* a byte no runtime owns reads the same through U (FSW_frame.fsw_unpoison_notowned, as a view) *)
Lemma cno_view_notowned : forall ly S U (W : world tfibsegs) mem md a, ARU tfibsegs B ly S U W mem md ->
  0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> aview tfibsegs (w_H W) (unpoison U mem) a = aview tfibsegs (w_H W) mem a.
Proof. intros ly S U W mem md a H Ha Hno. apply aview_at. exact (fsw_unpoison_notowned B ly S U W mem md a H Ha Hno). Qed.

(* ================= the facts every call site of the walk gives ================= *)
Lemma cno_site_facts : forall cx k ly S U (W : world tfibsegs) regs mem md,
  cno_base B cx -> cno_site B cx k ly S U W regs mem md ->
  cno_sp0 cx mod 16 = 0 /\ alloc_ceiling + STK_check_no_overread <= cno_sp0 cx /\ cno_sp0 cx <= 2 ^ 47 /\
  cno_sp0 cx - 192 < cno_sp1 cx <= cno_sp0 cx - 160 /\ (cno_sp1 cx - cno_sp0 cx) mod 16 = 0 /\
  spZ regs = cno_sp1 cx /\ s0Z regs = cno_sp0 cx /\
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
  ARU tfibsegs B (c_ly cx) (c_S cx) (c_U cx) (c_W cx) (c_mem cx) (c_md cx) /\
  In (1, c_fpos cx) (frames S) /\ cno_F cx = frame_addr ly 1 (c_fpos cx) /\ ly_top ly = ly_top (c_ly cx).
Proof.
intros cx k ly S U W regs mem md HB HS.
destruct HB as (HPRE & _). destruct HPRE as [HAPU _].
pose proof (fsw_sp B _ _ _ _ _ _ _ _ _ HAPU) as (Hal16 & Hceil & H47 & _).
pose proof (fsw_ARU B _ _ _ _ _ _ _ _ _ HAPU) as HARU0.
pose proof HAPU as ((HAR0 & _ & _ & Hgp & Htp & _) & _).
destruct HS as (HJ & HARU & FH & R2 & R8 & R3 & R4 & Hra & Hra4 & Hw8 & Hw16).
unfold cno_J in HJ.
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
pose proof (u64_range (getr (c_regs cx) 2)) as Hr2.
pose proof asan_consts as (C1 & _). pose proof cno_stk as FS.
assert (Esp0 : cno_sp0 cx = spZ (c_regs cx)) by reflexivity.
assert (Hsp1 : cno_sp0 cx - 192 < cno_sp1 cx <= cno_sp0 cx - 160 /\ cno_sp1 cx mod 32 = 0).
{ unfold cno_sp1. rewrite Esp0. unfold spZ in *. Z.div_mod_to_equations. lia. }
destruct Hsp1 as (Hsp1 & Hal32).
split; [rewrite Esp0; exact Hal16|]. split; [rewrite Esp0; exact Hceil|]. split; [rewrite Esp0; exact H47|].
split; [exact Hsp1|].
split.
{ assert (E : cno_sp1 cx - cno_sp0 cx = 16 * (2 * (cno_sp1 cx / 32) - cno_sp0 cx / 16)).
  { rewrite Esp0 in *. Z.div_mod_to_equations. lia. }
  rewrite E, Z.mul_comm. apply Z_mod_mult. }
split.
{ unfold spZ. rewrite R2. unfold w64. rewrite unsigned_lit_small; [reflexivity|]. rewrite Esp0 in *. unfold spZ in *. lia. }
split.
{ unfold s0Z. rewrite R8. unfold w64. rewrite unsigned_lit_small; [reflexivity|]. rewrite Esp0. unfold spZ. lia. }
split; [rewrite R3; exact Hgp|]. split; [rewrite R4; exact Htp|].
split; [exact HARU0|].
split; [rewrite Hfrs; left; reflexivity|].
destruct (al_layout _ _ LAWS _ _ _ _ _ ly HAR0 Hly) as (_ & Efa & _).
split; [unfold cno_F; symmetry; apply Efa|].
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). exact Etop.
Qed.

(* the walk's last block t, appended after every entry block: live, not an entry block, disjoint from each entry block,
   and (U being the entry's) no head of U shadows it *)
Lemma cno_tblock : forall cx k ly S U (W : world tfibsegs) regs mem md t l,
  cno_base B cx -> cno_site B cx k ly S U W regs mem md -> U = c_U cx ->
  ablocks B ly S = ablocks B (c_ly cx) (c_S cx) ++ l ++ [(t, cno_n cx + 18)] ->
  In (t, cno_n cx + 18) (ablocks B ly S) /\ ~ In (t, cno_n cx + 18) (ablocks B (c_ly cx) (c_S cx)) /\
  req_size (cno_n cx + 18) = cno_n cx + 18 /\
  4096 <= t /\ t + (cno_n cx + 18) <= alloc_ceiling /\ in_app t (cno_n cx + 18) /\
  (forall a, t <= a < t + (cno_n cx + 18) -> apresent (w_H W) (unpoison U mem) a /\ ~ aowned B ly S a) /\
  (forall b m, In (b, m) (ablocks B (c_ly cx) (c_S cx)) ->
     In (b, m) (ablocks B ly S) /\ (b + req_size m <= t \/ t + (cno_n cx + 18) <= b)) /\
  (forall x, t <= x < t + (cno_n cx + 18) -> in_ush U (bv_unsigned (Z_to_bv 64 (shadow_addr x))) = false).
Proof.
intros cx k ly S U W regs mem md t l HB HS HU El.
pose proof (cno_site_facts cx k ly S U W regs mem md HB HS) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HARU0 & _).
destruct HS as (HJ & HARU & _). unfold cno_J in HJ. pose proof HJ as (HAR & _).
assert (Hn0 : 0 <= cno_n cx) by (unfold cno_n; lia).
set (n := cno_n cx) in *.
assert (Hreq : req_size (n + 18) = n + 18)
  by (unfold req_size; destruct (n + 18 =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia | reflexivity]).
assert (Hnew : In (t, n + 18) (ablocks B ly S))
  by (rewrite El; apply in_or_app; right; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md t (n + 18) HAR Hnew)
  as (_ & Ht4096 & Htc & Htapp & Htp & _ & _).
rewrite Hreq in Htc, Htapp, Htp.
assert (Hdis : forall b m, In (b, m) (ablocks B (c_ly cx) (c_S cx)) ->
  In (b, m) (ablocks B ly S) /\ (b + req_size m <= t \/ t + (n + 18) <= b)).
{ intros b m Hb. split; [rewrite El; apply in_or_app; left; exact Hb|].
  apply in_split in Hb as (l1 & l2 & Ebq).
  pose proof (sep_blocks_pos tfibsegs B LAWS ly S W (unpoison U mem) md (b, m) (t, n + 18) l1 (l2 ++ l) [] HAR
    ltac:(rewrite El, Ebq; repeat rewrite <- app_assoc; reflexivity)) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. rewrite Hreq in Hd. lia. }
split; [exact Hnew|].
split.
{ intros Hin. destruct (Hdis t (n + 18) Hin) as (_ & Hd). rewrite Hreq in Hd. lia. }
split; [exact Hreq|]. split; [exact Ht4096|]. split; [lia|]. split; [exact Htapp|]. split; [exact Htp|].
split; [exact Hdis|].
intros x Hx. rewrite HU.
assert (Hx64 : 0 <= x < 2 ^ 64) by (pose proof asan_consts as (C1 & _); lia).
apply (ARU_shadow_out_block tfibsegs B (c_ly cx) (c_S cx) (c_U cx) (c_W cx) (c_mem cx) (c_md cx) x HARU0 Hx64).
intros p m Hp Hin. destruct (Hdis p m Hp) as (_ & Hd). lia.
Qed.

(* the UBSan guards of the straight-line code between the memory calls (U1 0x813c0 `bltu s7,s6` with s7 = ~t, s6 = n;
   U2 0x813e0 `beq a0,a1` with a0 = t + n, a1 = -1; U3 0x813f8 `bltu s7,s6` with s6 = n + 17; each to unimp 0x815fc)
   trap iff t + n, t + n + 1 or t + n + 17 passes 2 ^ 64 - 1. The walk's __wrap_malloc block t lies in application
   memory (YCbq.al_blocks under the journal's AR: 4096 <= t and t + n + 18 <= alloc_ceiling < 2 ^ 47) and
   n <= PRESET_FILE_MAX_BYTES (cno_base), so none traps: the top file's runs from 0x813bc and 0x813f8 take this. *)
Lemma cno_ubsan_t : forall cx k ly S U (W : world tfibsegs) regs mem md t,
  cno_base B cx -> cno_site B cx k ly S U W regs mem md -> In (t, cno_n cx + 18) (ablocks B ly S) ->
  4096 <= t /\ t + cno_n cx + 18 <= alloc_ceiling /\ alloc_ceiling < 2 ^ 47 /\
  cno_n cx <= PRESET_FILE_MAX_BYTES /\ t + cno_n cx + 17 < 2 ^ 64 - 1.
Proof.
intros cx k ly S U W regs mem md t HB HS Hin.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HnMAX & _).
destruct HS as (HJ & _). unfold cno_J in HJ. pose proof HJ as (HAR & _).
assert (Hn0 : 0 <= cno_n cx) by (unfold cno_n; lia).
assert (Hreq : req_size (cno_n cx + 18) = cno_n cx + 18)
  by (unfold req_size; destruct (cno_n cx + 18 =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia | reflexivity]).
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md t (cno_n cx + 18) HAR Hin) as (_ & Ht4096 & Htc & _).
rewrite Hreq in Htc.
pose proof asan_consts as (C1 & _).
split; [exact Ht4096|]. split; [lia|]. split; [lia|]. split; [exact HnMAX|].
unfold PRESET_FILE_MAX_BYTES in HnMAX. lia.
Qed.

(* ================= __wrap_malloc (n + 18) at 0x8139c ================= *)
Lemma cno_call_mal : cno_call_mal_T B.
Proof using FS_ENV ML AMALLOC IMG HMAL.
intros cx k ly S U W regs mem md live peak cnt fail HB HS R1 R10 HG Hk Hbb.
pose proof (cno_site_facts cx k ly S U W regs mem md HB HS)
  as (Hal16 & Hceil0 & H47 & Hsp1 & Hal1 & Rsp & Rs0 & Rgp & Rtp & HARU0 & Hin1 & EF & Etop).
pose proof HB as (HPRE & FH0 & Hfr0 & Htopr & H10 & H11 & HSRC & Hnz & Hblk & HnMAX & HG0 & HQ & Hlv & Hev & Hbb0).
pose proof HS as (HJ & HARU & FH & R2 & R8 & R3 & R4 & Hra & Hra4 & Hw8 & Hw16).
destruct HPRE as [HAPU _]. pose proof HAPU as ((HAR0 & _ & Hra40 & _ & _ & Hstk0 & _ & Hch0 & _) & _ & _).
pose proof Hstk0 as (_ & _ & _ & _ & _ & Hsh47 & _ & _ & Htopst).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cno_stk as FS. assert (HAS : ASTACK = 16384) by reflexivity.
assert (Hn0 : 0 <= cno_n cx) by (unfold cno_n; lia).
unfold cno_J in HJ.
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & Hnev & _ & F1 & _).
set (n := cno_n cx) in *. set (sp0 := cno_sp0 cx) in *. set (sp1 := cno_sp1 cx) in *.
assert (Hal8 : sp0 mod 8 = 0) by (clear -Hal16; Z.div_mod_to_equations; lia).
(* the call-relative journal at the call *)
pose proof (ajournal_sub_init tfibsegs B STK_check_no_overread sp0 FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
  (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(1, c_fpos cx)] ly S W (unpoison U mem) md k ASTACK sp1 [] (sp1 - sp0)
  HJ ltac:(lia) Hal1 ltac:(lia) ltac:(lia) ltac:(lia)) as HJc.
(* the frame chain at the callee's entry: check_no_overread's record (sp0, entry ra, entry s0) on the entry chain *)
set (ch' := (sp0, raZ (c_regs cx), s0Z (c_regs cx)) :: c_ch cx).
assert (Hchain : chain_pre ly (aview tfibsegs (w_H W) (unpoison U mem)) regs ch').
{ apply (achain_chain_pre ly _ sp1 sp0 ch' regs).
  - apply (cno_chain ly (aview tfibsegs (w_H (c_W cx)) (unpoison (c_U cx) (c_mem cx))) _ sp0 (s0Z (c_regs cx))
      (c_ch cx) (raZ (c_regs cx)) sp1).
    + exact (achain_ly_top (c_ly cx) ly _ _ _ _ Etop Hch0).
    + rewrite Etop. exact Htopr.
    + rewrite Etop. lia.
    + intros a Ha. apply F1; lia.
    + rewrite (cno_rdword_ext (aview tfibsegs (w_H W) mem) (aview tfibsegs (w_H W) (unpoison U mem)) (sp0 - 8));
        [exact Hw8|].
      intros i Hi. apply (fsw_aview_unpoison_high B ly S U W mem md); [exact HARU | lia].
    + rewrite (cno_rdword_ext (aview tfibsegs (w_H W) mem) (aview tfibsegs (w_H W) (unpoison U mem)) (sp0 - 16));
        [exact Hw16|].
      intros i Hi. apply (fsw_aview_unpoison_high B ly S U W mem md); [exact HARU | lia].
    + exact Hra40.
    + lia.
    + exact Hal8.
    + lia.
  - lia.
  - exact Rs0.
  - exact Hra4. }
unfold cfg_at. change (w64 PC_malloc) with (Z_to_bv 64 PC_malloc). rewrite <- HMAL.
eapply SRr_mono.
{ exact (FSW_malloc_free.fsw_aj_malloc04U B FS_ENV ML AMALLOC W regs mem ASTACK sp1 [] ly S W mem md [] ly S U md 0
    (n + 18) 0 (getr regs 1) ch' HJc HARU R10 ltac:(unfold MALLOC_MAX, PRESET_FILE_MAX_BYTES in *; lia) Hbb
    ltac:(rewrite Rsp; lia) eq_refl ltac:(lia) ltac:(lia) Rgp Rtp eq_refl Hra
    ltac:(unfold EV_check_no_overread in *; lia) Hchain). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HARU2 & HJ2 & HP2 & H10r & Hfr2 & Hr4 & Hbl2
  & HK2).
pose proof (ARU_AR tfibsegs B ly2 S2 U W2 mem2 md2 HARU2) as HAR2.
pose proof HJ2 as (_ & Hly2 & _).
destruct (al_layout _ _ LAWS _ _ _ _ _ ly2 HAR Hly2) as (_ & Efa2 & _).
destruct HK2 as (K1 & K2 & K3 & K4 & _).
replace (sp1 + 0 - ASTACK) with (sp1 - ASTACK) in K1 by lia. replace (sp1 + 0) with sp1 in K1 by lia.
assert (Hnew2 : In (res, n + 18) (ablocks B ly2 S2)) by (rewrite Hbl2; apply in_or_app; right; left; reflexivity).
assert (Hreq : req_size (n + 18) = n + 18)
  by (unfold req_size; destruct (n + 18 =? 0) eqn:Ez; [apply Z.eqb_eq in Ez; lia | reflexivity]).
destruct (al_blocks _ _ LAWS ly2 S2 W2 (unpoison U mem2) md2 res (n + 18) HAR2 Hnew2)
  as (_ & _ & Hresc & Hresapp & _ & _ & _).
rewrite Hreq in Hresc, Hresapp.
(* the fake frame and its shadow: no runtime-owned byte before or after the call, apart from the new block *)
set (F := cno_F cx) in *.
assert (Hin2 : In (1, c_fpos cx) (frames S2)) by (rewrite Hfr2; exact Hin1).
destruct (frames_bounds tfibsegs B LAWS ly S W (unpoison U mem) md 1 (c_fpos cx) HAR Hin1)
  as (HF4096 & HFceil & HFapp).
destruct (al_frames _ _ LAWS ly S W (unpoison U mem) md 1 (c_fpos cx) HAR Hin1) as (_ & _ & Hfp & Hsp).
destruct (al_frames _ _ LAWS ly2 S2 W2 (unpoison U mem2) md2 1 (c_fpos cx) HAR2 Hin2) as (_ & _ & Hfp2 & Hsp2).
rewrite Efa2 in Hfp2, Hsp2. rewrite <- EF in HF4096, HFceil, HFapp, Hfp, Hsp, Hfp2, Hsp2.
change (fs_frame_bytes 1) with 128 in HF4096, HFceil, HFapp, Hfp, Hsp, Hfp2, Hsp2.
change (128 / 8) with 16 in Hsp, Hsp2.
pose proof (sep_block_frame tfibsegs B LAWS ly2 S2 W2 (unpoison U mem2) md2 res (n + 18) 1 (c_fpos cx) HAR2 Hnew2
  Hin2) as HdF.
rewrite Efa2, <- EF, Hreq in HdF. change (fs_frame_bytes 1) with 128 in HdF. unfold zdisjoint in HdF.
cbn [fst snd] in HdF.
exists res. unfold cno_ret. exists ly2, S2, regs2, mem2, md2.
split; [unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split.
{ unfold cno_J. change [(1, c_fpos cx)] with ([] ++ [(1, c_fpos cx)]).
  replace (k + 1) with (k + (0 + 1)) by lia.
  eapply (ajournal_sub tfibsegs B LAWS fs_segs_low).
  all: first [ solve [exact HJ] | solve [exact HJ2] | solve [lia] | solve [intros a (rg & [] & _)] ]. }
split; [exact HARU2|].
split.
{ intros r Hr. destruct (FH r Hr) as (E16 & m & Hm & Hm16). split; [exact E16|]. exists m.
  split; [rewrite Hbl2; apply in_or_app; left; exact Hm | exact Hm16]. }
split; [exact HP2|].
split.
{ intros a Hz _. unfold cno_zone, cno_SF in Hz. fold sp0 sp1 F in Hz.
  destruct Hz as [Hz | [Hz | [Hz | Hz]]].
  - rewrite <- (fsw_aview_unpoison_high B ly2 S2 U W2 mem2 md2 a HARU2) by lia.
    rewrite <- (fsw_aview_unpoison_high B ly S U W mem md a HARU) by lia.
    apply K1; lia.
  - rewrite <- (fsw_aview_unpoison_high B ly2 S2 U W2 mem2 md2 a HARU2) by lia.
    rewrite <- (fsw_aview_unpoison_high B ly S U W mem md a HARU) by lia.
    apply K1; lia.
  - assert (Ha64 : 0 <= a < 2 ^ 64) by lia.
    rewrite <- (cno_view_notowned ly2 S2 U W2 mem2 md2 a HARU2 Ha64 (proj2 (Hfp2 a Hz))).
    rewrite <- (cno_view_notowned ly S U W mem md a HARU Ha64 (proj2 (Hfp a Hz))).
    apply (K4 1 (c_fpos cx) a Hin1).
    + left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite <- EF. change (fs_frame_bytes 1) with 128. lia.
    + cbv beta. rewrite Hreq. lia.
  - pose proof (shadow_addr_bounds F ltac:(unfold in_app, kLowShadowBeg, ASAN_CEIL in HFapp; lia)) as (Hs1 & Hs2).
    assert (Ha64 : 0 <= a < 2 ^ 64) by lia.
    assert (Ei : a = shadow_addr F + (a - shadow_addr F)) by lia.
    rewrite <- (cno_view_notowned ly2 S2 U W2 mem2 md2 a HARU2 Ha64)
      by (rewrite Ei; exact (proj2 (Hsp2 (a - shadow_addr F) ltac:(lia)))).
    rewrite <- (cno_view_notowned ly S U W mem md a HARU Ha64)
      by (rewrite Ei; exact (proj2 (Hsp (a - shadow_addr F) ltac:(lia)))).
    apply (K4 1 (c_fpos cx) a Hin1).
    + right. unfold in_zr. cbn [fst snd]. rewrite <- EF. change (fs_frame_bytes 1 / 8) with 16. lia.
    + cbv beta. rewrite Hreq. unfold in_app, kLowShadowBeg, ASAN_CEIL, shadow_addr, SHADOW_OFF in *. lia. }
split.
{ intros p n' i Hp Hp2 Hi _.
  destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md p n' HAR Hp) as (_ & Hp4096 & Hpc & Hpapp & _).
  assert (Ha64 : 0 <= p + i < 2 ^ 64) by lia.
  assert (Happ : p + i < SHADOW_OFF \/ kHighMemBeg <= p + i)
    by (unfold in_app, kLowShadowBeg, ASAN_CEIL, SHADOW_OFF in *; lia).
  rewrite <- (cno_aview_unp B ly2 S2 U W2 mem2 md2 (p + i) HARU2 Ha64 Happ).
  rewrite <- (cno_aview_unp B ly S U W mem md (p + i) HARU Ha64 Happ).
  apply (K2 p n' i Hp Hi). cbv beta.
  apply in_split in Hp as (l1 & l2 & Ebq).
  pose proof (sep_blocks_pos tfibsegs B LAWS ly2 S2 W2 (unpoison U mem2) md2 (p, n') (res, n + 18) l1 l2 [] HAR2
    ltac:(rewrite Hbl2, Ebq, <- app_assoc; reflexivity)) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. rewrite Hreq in Hd. lia. }
split; [exact H10r|]. split; [lia|]. split; [exact Hbl2|].
split.
{ (* B: the fresh block's shadow is addressable at the return (the first inline check 0x813c8-0x813d4 reads it) *)
  apply (cno_ra_raw ly2 S2 U W2 mem2 md2 res (n + 18) res (n + 18) HARU2 Hnew2 ltac:(lia) ltac:(rewrite Hreq; lia)).
  intros x Hx.
  apply (ARU_shadow_out_block tfibsegs B ly S U W mem md x HARU ltac:(lia)).
  intros p m Hp Hpx.
  apply in_split in Hp as (l1 & l2 & Ebq).
  pose proof (sep_blocks_pos tfibsegs B LAWS ly2 S2 W2 (unpoison U mem2) md2 (p, m) (res, n + 18) l1 l2 [] HAR2
    ltac:(rewrite Hbl2, Ebq, <- app_assoc; reflexivity)) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. rewrite Hreq in Hd. lia. }
apply (cno_glob_kept W W2 mem mem2 live peak cnt fail HG).
intros a Ha. pose proof (fs_segs_low a (cno_pstat_img a Ha)) as Hai.
destruct (proj1 IMG a Ha) as [Hno Hne].
assert (Ha64 : 0 <= a < 2 ^ 64) by (unfold kLowMemEnd in Hai; lia).
assert (Hlow : a < SHADOW_OFF \/ kHighMemBeg <= a) by (left; unfold SHADOW_OFF, kLowMemEnd in *; lia).
rewrite <- (cno_aview_unp B ly2 S2 U W2 mem2 md2 a HARU2 Ha64 Hlow).
rewrite <- (cno_aview_unp B ly S U W mem md a HARU Ha64 Hlow).
exact (K3 a (cno_pstat_img a Ha) Hno Hne).
Qed.

(* ================= __asan_memcpy (t, d, n) at 0x813b8, n > 0 ================= *)
Lemma cno_call_mcpy : cno_call_mcpy_T B.
Proof using AMEMCPY.
intros cx k ly S U W regs mem md t HB HS HU R1 R10 R11 R12 Hn0 (l & El).
pose proof (cno_site_facts cx k ly S U W regs mem md HB HS)
  as (Hal16 & Hceil0 & H47 & Hsp1 & Hal1 & Rsp & Rs0 & Rgp & Rtp & HARU0 & Hin1 & EF & Etop).
destruct (cno_tblock cx k ly S U W regs mem md t l HB HS HU El)
  as (Hnew & Hnotold & Hreq & Ht4096 & Htc & Htapp & Htp & Hdis & Hush).
pose proof HB as (_ & _ & _ & _ & _ & _ & HSRC & _ & Hblk & HnMAX & _).
pose proof HS as (HJ & HARU & FH & _ & _ & _ & _ & Hra & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cno_stk as FS.
pose proof HARU0 as (HAR0 & _ & PO0).
unfold cno_J in HJ.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
set (n := cno_n cx) in *. set (sp0 := cno_sp0 cx) in *. set (sp1 := cno_sp1 cx) in *.
set (d := c_d cx) in *. set (db := c_db cx) in *.
assert (Hnlen : Z.of_nat (length db) = n) by reflexivity.
destruct (Hblk Hn0) as (b & m & Hbm & Hbd & Hdn).
destruct (Hdis b m Hbm) as (Hbm2 & Hbt).
pose proof HSRC as (HZB & Hd4 & Hdc & Hdam & Hdra & Hdhull).
rewrite Hnlen in Hdc, Hdam, Hdra, Hdhull.
pose proof (garr8_bytes_ok tfibsegs _ _ _ HZB) as Hdb.
destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR0 Hbm) as (_ & Hb4096 & Hbc & Hbapp & _).
assert (Hreqm : m <= req_size m) by (unfold req_size; destruct (m =? 0) eqn:Ez; [apply Z.eqb_eq in Ez|]; lia).
(* d's bytes at the call: the journal keeps the entry block (b, m), which is off FS_PSTAT_FP *)
assert (Hsrc : forall i, 0 <= i < n -> aview tfibsegs (w_H W) mem (d + i) = Some (nth (Z.to_nat i) db 0)).
{ intros i Hi.
  assert (Ha64 : 0 <= d + i < 2 ^ 64) by lia.
  assert (Happ : d + i < SHADOW_OFF \/ kHighMemBeg <= d + i)
    by (unfold in_app, kLowShadowBeg, ASAN_CEIL, SHADOW_OFF in *; lia).
  rewrite <- (cno_aview_unp B ly S U W mem md (d + i) HARU Ha64 Happ).
  replace (d + i) with (b + (d + i - b)) by lia.
  rewrite (F2 b m (d + i - b) Hbm Hbm2 ltac:(lia)).
  2: { intros Hfp. apply (blk_img tfibsegs B LAWS _ _ _ _ _ b m (b + (d + i - b)) HAR0 Hbm ltac:(lia)).
       exact (cno_pstat_img _ Hfp). }
  replace (b + (d + i - b)) with (d + i) by lia.
  rewrite (cno_aview_unp B (c_ly cx) (c_S cx) (c_U cx) (c_W cx) (c_mem cx) (c_md cx) (d + i) HARU0 Ha64 Happ).
  replace (d + i) with (d + Z.of_nat (Z.to_nat i)) by lia.
  apply cno_aview_of_garr8; [exact HZB | lia]. }
assert (Hsp1' : spZ regs = sp0 + (sp1 - sp0)) by lia.
pose proof (fsw_ecall_preU_at B STK_check_no_overread sp0 FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
  (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(1, c_fpos cx)] ly S U W mem md k regs (sp1 - sp0)
  HJ HARU Hsp1' Hal1 ltac:(lia) ltac:(unfold ESTACK; lia) Hra Rgp Rtp) as HPRE'.
assert (Hblkraw : forall a, t <= a < t + (n + 18) ->
  writable_at tfibsegs (mrestrict (w_H W) mem) a /\ ~ aowned B ly S a).
{ intros a Ha. destruct (Htp a Ha) as [(Hh & bb & Hbb) Hno]. split; [|exact Hno].
  apply (apresent_writable tfibsegs). split; [exact Hh|]. exists bb.
  rewrite <- (fsw_unpoison_app B ly S U W mem md a HARU ltac:(lia)
    ltac:(unfold in_app, kLowShadowBeg, ASAN_CEIL, SHADOW_OFF in *; lia)). exact Hbb. }
assert (Hdest : dest_ok tfibsegs B ly S W regs mem t n).
{ intros a Ha. destruct (Hblkraw a ltac:(lia)) as [Hw Hno]. split; [exact Hw|]. split; [exact Hno|].
  rewrite Rsp. unfold ESTACK. lia. }
assert (HMC := AMEMCPY ly S U W regs mem md t d n HPRE' R10 R11 R12
  ltac:(unfold PRESET_FILE_MAX_BYTES in *; lia) ltac:(lia) ltac:(lia) Hdest
  (amem_range_of_block tfibsegs B LAWS ly S W _ md t (n + 18) t n HAR Hnew ltac:(lia) ltac:(rewrite Hreq; lia))
  (cno_ra_raw ly S U W mem md t (n + 18) t n HARU Hnew ltac:(lia) ltac:(rewrite Hreq; lia)
     ltac:(intros x Hx; apply Hush; lia))
  (fun Hn0' => cno_hull_raw ly S U W mem md t n HARU
     (shadow_hull_vis_of_block tfibsegs B LAWS ly S W _ md t (n + 18) t n HAR Hnew ltac:(lia)
        ltac:(rewrite Hreq; lia) Hn0'))).
specialize (HMC ltac:(hnf;
  split; [lia|]; split; [lia|]; split;
  [ intros a Ha; split;
    [ replace a with (d + (a - d)) by lia; rewrite (Hsrc (a - d)) by lia; discriminate
    | rewrite Rsp; unfold ESTACK; lia ]
  | split; [lia|]; split; [exact Hdam|]; split;
    [ apply (cno_ra_raw ly S U W mem md b m d n HARU Hbm2 Hbd ltac:(lia)); intros x Hx; rewrite HU;
      apply (cno_ush_src (c_W cx) (c_mem cx) (c_U cx) d n Hdra PO0 x Hx); lia
    | intros Hn0'; apply (cno_hull_raw ly S U W mem md d n HARU);
      exact (shadow_hull_vis_of_block tfibsegs B LAWS ly S W _ md b m d n HAR Hbm2 Hbd ltac:(lia) Hn0') ] ])).
set (Wr := fun a => (t <= a < t + n) \/ (sp1 - ESTACK <= a < sp1)).
eapply SRr_mono.
{ apply (fsw_intrin_atU B STK_check_no_overread sp0 FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(1, c_fpos cx)] ly S U W mem md k U Wr (getr regs 1) _
    (fun regs' mem' md' => aregs_preserved regs regs' /\ getr regs' 10 = w64 t /\
       (forall i, 0 <= i < n -> aview tfibsegs (w_H W) mem' (t + i) = Some (nth (Z.to_nat i) db 0)) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (t <= a < t + n) -> ~ (sp1 - ESTACK <= a < sp1) ->
          aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a)) HJ).
  - eapply SRr_mono; [exact HMC|].
    intros W' c' _ (-> & regs' & mem' & md' & -> & HARU' & HP' & Hsb & H10' & Hcpy & Hfr & Hgr).
    split; [reflexivity|]. exists regs', mem', md'.
    split; [unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
    assert (HfrW : forall a, 0 <= a < 2 ^ 64 -> ~ (t <= a < t + n) -> ~ (sp1 - ESTACK <= a < sp1) ->
      aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a).
    { intros a Ha H1 H2. apply Hfr; [exact Ha | exact H1 | rewrite Rsp; exact H2]. }
    split; [exact HARU'|]. split; [exact Hsb|].
    split.
    { intros a Ha HnW. destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:Ei; [apply aview_unpoison_in; exact Ei|].
      rewrite !(aview_unpoison_out tfibsegs _ U _ a Ei).
      apply HfrW; [exact Ha | intros X; apply HnW; left; exact X | intros X; apply HnW; right; exact X]. }
    split.
    { intros a (Hh & bb & Hbb). split; [exact Hh|].
      destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:Ei; [rewrite unpoison_in by exact Ei; eexists; reflexivity|].
      rewrite unpoison_out in Hbb |- * by exact Ei. exact (proj2 (Hgr a (conj Hh (ex_intro _ bb Hbb)))). }
    split; [exact HP'|]. split; [exact H10'|]. split; [|exact HfrW].
    intros i Hi. rewrite (Hcpy i Hi). exact (Hsrc i Hi).
  - intros a [Ha|Ha].
    + left. right. right. left. exists t, (n + 18). split; [exact Hnew|]. split; [exact Hnotold|]. rewrite Hreq. lia.
    + left. left. unfold ESTACK in Ha. lia. }
cbv beta. intros W3 c3 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HARU2 & HP2 & H10' & Hcpy2 & Hkept2).
destruct (frames_bounds tfibsegs B LAWS ly S W (unpoison U mem) md 1 (c_fpos cx) HAR Hin1)
  as (HF4096 & HFceil & HFapp).
rewrite <- EF in HF4096, HFceil, HFapp. change (fs_frame_bytes 1) with 128 in HF4096, HFceil, HFapp.
pose proof (shadow_addr_bounds (cno_F cx) ltac:(unfold in_app, kLowShadowBeg, ASAN_CEIL in HFapp; lia)) as (Hs1 & Hs2).
unfold cno_ret. exists ly, S, regs2, mem2, md2.
split; [unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [unfold cno_J; rewrite Z.add_0_r; exact HJ2|].
split; [exact HARU2|]. split; [exact FH|]. split; [exact HP2|].
split.
{ intros a Hz HnK. cbv beta in HnK. unfold cno_zone, cno_SF in Hz. fold sp0 sp1 in Hz.
  apply Hkept2; [| exact HnK |]; unfold ESTACK; destruct Hz as [Hz | [Hz | [Hz | Hz]]]; lia. }
split.
{ intros p n' i Hp _ Hi HnK. cbv beta in HnK.
  destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md p n' HAR Hp) as (_ & Hp4096 & Hpc & _).
  apply Hkept2; [lia | exact HnK | unfold ESTACK; lia]. }
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact H10'|].
split; [|exact Hkept2].
unfold zbytes_at. apply cno_garr8; [exact Hdb|].
intros j Hj. rewrite (Hcpy2 (Z.of_nat j)) by lia. rewrite Nat2Z.id. reflexivity.
Qed.

(* ================= __asan_memset (t + n + 1, 0, 16) at 0x813f4 ================= *)
Lemma cno_call_mset : cno_call_mset_T B.
Proof using AMEMSET.
intros cx k ly S U W regs mem md t HB HS HU R1 R10 R11 R12 (l & El).
pose proof (cno_site_facts cx k ly S U W regs mem md HB HS)
  as (Hal16 & Hceil0 & H47 & Hsp1 & Hal1 & Rsp & Rs0 & Rgp & Rtp & HARU0 & Hin1 & EF & Etop).
destruct (cno_tblock cx k ly S U W regs mem md t l HB HS HU El)
  as (Hnew & Hnotold & Hreq & Ht4096 & Htc & Htapp & Htp & Hdis & Hush).
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HnMAX & _).
pose proof HS as (HJ & HARU & FH & _ & _ & _ & _ & Hra & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof cno_stk as FS.
assert (Hn0 : 0 <= cno_n cx) by (unfold cno_n; lia).
unfold cno_J in HJ.
pose proof HJ as (HAR & _).
set (n := cno_n cx) in *. set (sp0 := cno_sp0 cx) in *. set (sp1 := cno_sp1 cx) in *.
assert (Hsp1' : spZ regs = sp0 + (sp1 - sp0)) by lia.
pose proof (fsw_ecall_preU_at B STK_check_no_overread sp0 FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
  (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(1, c_fpos cx)] ly S U W mem md k regs (sp1 - sp0)
  HJ HARU Hsp1' Hal1 ltac:(lia) ltac:(unfold ESTACK; lia) Hra Rgp Rtp) as HPRE'.
assert (Hblkraw : forall a, t <= a < t + (n + 18) ->
  writable_at tfibsegs (mrestrict (w_H W) mem) a /\ ~ aowned B ly S a).
{ intros a Ha. destruct (Htp a Ha) as [(Hh & bb & Hbb) Hno]. split; [|exact Hno].
  apply (apresent_writable tfibsegs). split; [exact Hh|]. exists bb.
  rewrite <- (fsw_unpoison_app B ly S U W mem md a HARU ltac:(lia)
    ltac:(unfold in_app, kLowShadowBeg, ASAN_CEIL, SHADOW_OFF in *; lia)). exact Hbb. }
assert (Hdest : dest_ok tfibsegs B ly S W regs mem (t + n + 1) 16).
{ intros a Ha. destruct (Hblkraw a ltac:(lia)) as [Hw Hno]. split; [exact Hw|]. split; [exact Hno|].
  rewrite Rsp. unfold ESTACK. lia. }
assert (HMS := AMEMSET ly S U W regs mem md (t + n + 1) 0 16 HPRE' R10 R11 R12 ltac:(lia) ltac:(lia) ltac:(lia)
  Hdest
  (amem_range_of_block tfibsegs B LAWS ly S W _ md t (n + 18) (t + n + 1) 16 HAR Hnew ltac:(lia)
     ltac:(rewrite Hreq; lia))
  (cno_ra_raw ly S U W mem md t (n + 18) (t + n + 1) 16 HARU Hnew ltac:(lia) ltac:(rewrite Hreq; lia)
     ltac:(intros x Hx; apply Hush; lia))
  (fun Hn0' => cno_hull_raw ly S U W mem md (t + n + 1) 16 HARU
     (shadow_hull_vis_of_block tfibsegs B LAWS ly S W _ md t (n + 18) (t + n + 1) 16 HAR Hnew ltac:(lia)
        ltac:(rewrite Hreq; lia) Hn0'))
  I).
set (Wr := fun a => (t + n + 1 <= a < t + n + 17) \/ (sp1 - ESTACK <= a < sp1)).
eapply SRr_mono.
{ apply (fsw_intrin_atU B STK_check_no_overread sp0 FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(1, c_fpos cx)] ly S U W mem md k U Wr (getr regs 1) _
    (fun regs' mem' md' => aregs_preserved regs regs' /\ getr regs' 10 = w64 (t + n + 1) /\
       (forall i, 0 <= i < 16 -> aview tfibsegs (w_H W) mem' (t + n + 1 + i) = Some 0) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (t + n + 1 <= a < t + n + 17) -> ~ (sp1 - ESTACK <= a < sp1) ->
          aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a)) HJ).
  - eapply SRr_mono; [exact HMS|].
    intros W' c' _ (-> & regs' & mem' & md' & -> & HARU' & HP' & Hsb & H10' & Hset & Hfr & Hgr).
    split; [reflexivity|]. exists regs', mem', md'.
    split; [unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
    assert (HfrW : forall a, 0 <= a < 2 ^ 64 -> ~ (t + n + 1 <= a < t + n + 17) -> ~ (sp1 - ESTACK <= a < sp1) ->
      aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a).
    { intros a Ha H1 H2. apply Hfr; [exact Ha | intros X; apply H1; lia | rewrite Rsp; exact H2]. }
    split; [exact HARU'|]. split; [exact Hsb|].
    split.
    { intros a Ha HnW. destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:Ei; [apply aview_unpoison_in; exact Ei|].
      rewrite !(aview_unpoison_out tfibsegs _ U _ a Ei).
      apply HfrW; [exact Ha | intros X; apply HnW; left; exact X | intros X; apply HnW; right; exact X]. }
    split.
    { intros a (Hh & bb & Hbb). split; [exact Hh|].
      destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:Ei; [rewrite unpoison_in by exact Ei; eexists; reflexivity|].
      rewrite unpoison_out in Hbb |- * by exact Ei. exact (proj2 (Hgr a (conj Hh (ex_intro _ bb Hbb)))). }
    split; [exact HP'|]. split; [exact H10'|]. split; [|exact HfrW].
    intros i Hi. rewrite (Hset i Hi). reflexivity.
  - intros a [Ha|Ha].
    + left. right. right. left. exists t, (n + 18). split; [exact Hnew|]. split; [exact Hnotold|]. rewrite Hreq. lia.
    + left. left. unfold ESTACK in Ha. lia. }
cbv beta. intros W3 c3 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HARU2 & HP2 & H10' & Hset2 & Hkept2).
destruct (frames_bounds tfibsegs B LAWS ly S W (unpoison U mem) md 1 (c_fpos cx) HAR Hin1)
  as (HF4096 & HFceil & HFapp).
rewrite <- EF in HF4096, HFceil, HFapp. change (fs_frame_bytes 1) with 128 in HF4096, HFceil, HFapp.
pose proof (shadow_addr_bounds (cno_F cx) ltac:(unfold in_app, kLowShadowBeg, ASAN_CEIL in HFapp; lia)) as (Hs1 & Hs2).
unfold cno_ret. exists ly, S, regs2, mem2, md2.
split; [unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [unfold cno_J; rewrite Z.add_0_r; exact HJ2|].
split; [exact HARU2|]. split; [exact FH|]. split; [exact HP2|].
split.
{ intros a Hz HnK. cbv beta in HnK. unfold cno_zone, cno_SF in Hz. fold sp0 sp1 in Hz.
  apply Hkept2; [| exact HnK |]; unfold ESTACK; destruct Hz as [Hz | [Hz | [Hz | Hz]]]; lia. }
split.
{ intros p n' i Hp _ Hi HnK. cbv beta in HnK.
  destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md p n' HAR Hp) as (_ & Hp4096 & Hpc & _).
  apply Hkept2; [lia | exact HnK | unfold ESTACK; lia]. }
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact H10'|].
split.
{ unfold zbytes_at. apply cno_garr8.
  - apply Forall_forall. intros x Hx. apply repeat_spec in Hx. lia.
  - intros j Hj. rewrite repeat_length in Hj. rewrite nth_repeat. apply (Hset2 (Z.of_nat j)). lia. }
split; [exact Hkept2|].
exact (cno_ra_raw ly S U W mem2 md2 t (n + 18) t (n + 18) HARU2 Hnew ltac:(lia) ltac:(rewrite Hreq; lia)
  ltac:(intros x Hx; apply Hush; lia)).
Qed.

End M.
