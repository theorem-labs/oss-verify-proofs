(* reac_declared_vlan_split on fuzz_segconf image A: facts about the objects of the entry (the segment, parent, the
   vid cell) that every segment of the walk reads at a later state: bounds, the journal's permission to write a
   destination of the footprint, its shadow at a later state, and the frame's saved words across a run. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YG0p YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require reac_declared_vlan_split_lem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import reac_declared_vlan_split_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import reac_declared_vlan_split_k reac_declared_vlan_split_d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the saved words move to any reader that agrees on the frame *)
Lemma vs_slots_kept : forall (rd rd' : reader) sp0 regs,
  vs_slots rd sp0 regs -> (forall a, sp0 - 64 <= a < sp0 -> rd' a = rd a) -> vs_slots rd' sp0 regs.
Proof.
intros rd rd' sp0 regs H HK i r Hr. rewrite <- (H i r Hr). apply rdword_ext. intros k Hk.
assert (Hi : (i < 8)%nat) by (assert (Hl : (i < length vs_saved)%nat) by (apply nth_error_Some; rewrite Hr; discriminate);
  cbn [length vs_saved] in Hl; exact Hl).
apply HK. lia.
Qed.

(* the body's registers survive a call that preserves the callee-saved ones *)
Lemma vs_regs_pres : forall e (regs1 regs2 : bvmap 5 word), vs_regs e regs1 ->
  (forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regs1 (Z_to_bv 5 r)) -> vs_regs e regs2.
Proof.
intros e regs1 regs2 (Hsp & G3 & G4 & G8 & G9 & G18 & G19 & G22 & G27) Q.
unfold vs_regs. split.
{ unfold spZ in Hsp |- *. change (getr regs2 2) with (getr regs2 (Z_to_bv 5 2)).
  rewrite (Q 2 ltac:(unfold acallee_saved; lia)). exact Hsp. }
split; [change (getr regs2 3) with (getr regs2 (Z_to_bv 5 3)); rewrite (Q 3 ltac:(unfold acallee_saved; lia)); exact G3|].
split; [change (getr regs2 4) with (getr regs2 (Z_to_bv 5 4)); rewrite (Q 4 ltac:(unfold acallee_saved; lia)); exact G4|].
split; [change (getr regs2 8) with (getr regs2 (Z_to_bv 5 8)); rewrite (Q 8 ltac:(unfold acallee_saved; lia)); exact G8|].
split; [change (getr regs2 9) with (getr regs2 (Z_to_bv 5 9)); rewrite (Q 9 ltac:(unfold acallee_saved; lia)); exact G9|].
split; [change (getr regs2 18) with (getr regs2 (Z_to_bv 5 18)); rewrite (Q 18 ltac:(unfold acallee_saved; lia)); exact G18|].
split; [change (getr regs2 19) with (getr regs2 (Z_to_bv 5 19)); rewrite (Q 19 ltac:(unfold acallee_saved; lia)); exact G19|].
split; [change (getr regs2 22) with (getr regs2 (Z_to_bv 5 22)); rewrite (Q 22 ltac:(unfold acallee_saved; lia)); exact G22|].
intros r Hr. rewrite (Q r ltac:(unfold acallee_saved; lia)). exact (G27 r Hr).
Qed.

(* the alias the walk gives the engine for an address formed by `add` of two atoms *)
Lemma vs_add_alias : forall E (a b c : nat) (av bv0 : Z),
  ew E a = Z_to_bv 64 av -> 0 <= av -> ew E b = Z_to_bv 64 bv0 -> 0 <= bv0 -> av + bv0 < 2 ^ 64 ->
  ew E c = Z_to_bv 64 (av + bv0) ->
  sv_denot E (SAlu ALU_ADD (SOff a 0) (SOff b 0)) = sv_denot E (SOff c 0).
Proof.
intros E a b c av bv0 Ha Ha0 Hb Hb0 Hab Hc. apply U_inj.
rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, Ha, Hb, Hc, !Z.add_0_r.
rewrite !unsigned_lit_small by lia. unfold zcanon, M64.
rewrite (Z.mod_small av) by lia. rewrite (Z.mod_small bv0) by lia. reflexivity.
Qed.

(* every read-only byte is an image byte (the read-only segments, and .data.rel.ro .. .got through the listing's
   relro range) *)
Lemma vs_ro_img : seg_val_relro -> forall a, in_roP SEGS SEG_RLO SEG_RHI a -> in_img SEGS a.
Proof.
intros [Rlo Rhi] a [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr]|].
apply pa_relro_img. rewrite Rlo, Rhi. unfold SEG_RLO, SEG_RHI in Hr. exact Hr.
Qed.

(* the shadow bytes of an application range lie in [kLowShadowBeg, kHighShadowEnd) *)
Lemma vs_hull_bounds : forall x n s, 0 <= x -> 0 < n -> x + n <= 2 ^ 47 ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> kLowShadowBeg <= s < kHighShadowEnd.
Proof.
intros x n s Hx Hn Hxn Hs. unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighShadowEnd in *.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (x + n - 1) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
pose proof (Z.mul_div_le (2147450880 + x / 8) 8 ltac:(lia)). pose proof (Z.mul_div_le (2147450880 + (x + n - 1) / 8) 8 ltac:(lia)).
pose proof (Z_div_mod_eq_full (2147450880 + x / 8) 8). pose proof (Z.mod_pos_bound (2147450880 + x / 8) 8 ltac:(lia)). lia.
Qed.
Lemma vs_sa_addr_keep : forall (rd rd' : reader) q n, sa_addr rd q n -> q + n <= 2 ^ 47 ->
  (forall y, kLowShadowBeg <= y < kHighShadowEnd -> rd' y = rd y) -> sa_addr rd' q n.
Proof.
intros rd rd' q n (Q0 & Q1 & Q2 & Q3 & Q4) Hqn HK. split; [exact Q0|]. split; [exact Q1|]. split; [exact Q2|]. split.
- intros x Hx. destruct (Q3 x Hx) as (sv & Hsv & Hok). exists sv. split; [|exact Hok].
  unfold shadow_of_addr in *. rewrite HK; [exact Hsv|].
  pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound x 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
  unfold SHADOW_OFF, kLowShadowBeg, kHighShadowEnd. lia.
- intros Hn s Hs. rewrite HK; [exact (Q4 Hn s Hs) | exact (vs_hull_bounds q n s Q0 Hn Hqn Hs)].
Qed.
Lemma vs_sa_addr_sub : forall (rd : reader) q n m, sa_addr rd q n -> 0 < m <= n -> sa_addr rd q m.
Proof.
intros rd q n m (Q0 & Q1 & Q2 & Q3 & Q4) Hm. split; [exact Q0|]. split; [lia|]. split; [unfold amem_range in *; lia|]. split.
- apply (range_addressable_sub _ _ q n); [exact Q3 | lia | lia].
- intros _ s Hs. apply (Q4 ltac:(lia) s). split; [lia|].
  assert (Hd : shadow_addr (q + m - 1) / 8 <= shadow_addr (q + n - 1) / 8).
  { apply Z.div_le_mono; [lia|]. unfold shadow_addr. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
  lia.
Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.

(* where a destination of sa_dst lies: a side-stack frame or a heap block (application memory below the allocator's
   ceiling), or the caller's real stack above sp *)
Lemma vs_dst_facts : forall ly S W mem md regs STK d n,
  AR SEGS B ly S W mem md -> astk_ok STK ly (spZ regs) -> 0 < n ->
  sa_dst SEGS B ly S W mem regs d n ->
  4096 <= d /\ d + n <= 2 ^ 47 /\
  ((in_app d n /\ d + n <= alloc_ceiling) \/ (spZ regs <= d /\ d + n <= ly_top ly)).
Proof using.
intros ly S W mem md regs STK d n HAR Hstk Hn HD.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HD as [((cid & pos & Hin & Hc & H1 & H2) & _) | [((b & m & Hin & H1 & H2) & _) | (H1 & H2 & _)]].
- destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hin) as (F0 & F1 & F2).
  split; [lia|]. split; [lia|]. left. split; [eapply in_app_sub; [exact F2 | lia | lia | lia] | lia].
- destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & B0 & B1 & B2 & _ & _ & Bm).
  pose proof (req_size_pos m ltac:(lia)) as [Q1 Q2].
  split; [lia|]. split; [lia|]. left. split; [eapply in_app_sub; [exact B2 | lia | lia | lia] | lia].
- split; [lia|]. split; [lia|]. right. split; lia.
Qed.

(* the journal may write a byte of such a destination that is in its footprint, at any later state whose layout is
   the entry's and whose blocks are the entry's up to order *)
Lemma vs_dst_awr : forall ly S W mem md regs STK FP lyc Sc own d n a,
  AR SEGS B ly S W mem md -> sa_dst SEGS B ly S W mem regs d n ->
  lyc = ly -> Permutation (ablocks B lyc Sc) (ablocks B ly S) ->
  inFP FP a -> d <= a < d + n ->
  awr_byte SEGS B STK (spZ regs) FP (ablocks B ly S) (ablocks B lyc Sc) (frames S) lyc own a.
Proof using.
intros ly S W mem md regs STK FP lyc Sc own d n a HAR HD -> HP HF Ha.
destruct HD as [((cid & pos & Hin & Hc & H1 & H2) & _) | [((b & m & Hin & H1 & H2) & _) | (H1 & H2 & _)]].
- right; right; right; right. right; right. split; [exact HF|]. exists cid, pos. split; [exact Hin|].
  left. unfold in_zr, frame_rng. cbn [fst snd]. lia.
- right; left. split; [exact HF|]. exists b, m. split; [exact (Permutation_in _ (Permutation_sym HP) Hin)|].
  pose proof (req_size_pos m) as Q.
  destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & _ & _ & _ & _ & _ & Bm). specialize (Q ltac:(lia)). lia.
- right; right; right; right. right; left. split; [exact HF | lia].
Qed.

(* the shadow of such a destination at a later state of a journal from the entry: a frame keeps its shadow
   (range_addressable_entry_frame), a live block and the real stack have theirs from AR *)
Lemma vs_dst_ra : forall ly S W mem md regs STK FP ly' S' W' mem' md' k d n,
  AR SEGS B ly S W mem md -> astk_ok STK ly (spZ regs) ->
  sa_dst SEGS B ly S W mem regs d n -> range_addressable (rdW W mem) SHADOW_OFF d n ->
  ajournal SEGS B STK (spZ regs) FP ly S W mem md [] ly' S' W' mem' md' k ->
  ly' = ly -> Permutation (ablocks B ly' S') (ablocks B ly S) ->
  (forall x, inFP FP x -> x < kLowShadowBeg \/ kHighShadowEnd <= x) ->
  range_addressable (rdW W' mem') SHADOW_OFF d n.
Proof using.
intros ly S W mem md regs STK FP ly' S' W' mem' md' k d n HAR Hstk HD HRA HJ Ely HP HFP.
pose proof (proj1 HJ) as HAR'.
destruct HD as [((cid & pos & Hin & Hc & H1 & H2) & _) | [((b & m & Hin & H1 & H2) & _) | (H1 & H2 & _)]].
- destruct (al_frames _ _ LAWS ly S W mem md cid pos HAR Hin) as (Hal32 & _).
  eapply (range_addressable_entry_frame SEGS B LAWS); [exact HJ | exact Hin | exact Hc | exact H1 | exact H2 | | exact HFP | exact HAR | exact HRA].
  rewrite <- (Z.mod_mod (frame_addr ly cid pos) 8) by lia.
  replace (frame_addr ly cid pos) with (frame_addr ly cid pos / 32 * 32 + frame_addr ly cid pos mod 32) by (pose proof (Z.div_mod (frame_addr ly cid pos) 32); lia).
  rewrite Hal32, Z.add_0_r. replace (frame_addr ly cid pos / 32 * 32) with ((frame_addr ly cid pos / 32 * 4) * 8) by lia.
  rewrite Z_mod_mult. reflexivity.
- assert (Hin' : In (b, m) (ablocks B ly' S')) by exact (Permutation_in _ (Permutation_sym HP) Hin).
  pose proof (req_size_pos m) as Q.
  destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & _ & _ & _ & _ & _ & Bm). specialize (Q ltac:(lia)).
  apply (range_addressable_of_block SEGS B LAWS ly' S' W' mem' md' b m); [exact HAR' | exact Hin' | lia | lia].
- subst ly'. pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (lo_top _ (am_layout _ _ _ _ (proj1 HAR'))) as (_ & _ & _ & _ & L1 & L2 & L3).
  unfold page_aligned in L1, L2.
  assert (Z0 : zero_shadow (rdW W' mem') SHADOW_OFF (ly_stk_lo ly) (ly_stk_hi ly - ly_stk_lo ly)).
  { exact (al_zshadow _ _ LAWS ly S' W' mem' md' _ HAR' (or_introl eq_refl)). }
  apply (range_addressable_sub _ _ (ly_stk_lo ly) (ly_stk_hi ly - ly_stk_lo ly)); [|lia|lia].
  apply zero_shadow_range; [| |exact Z0].
  + rewrite <- (Z.mod_mod (ly_stk_lo ly) 8) by lia.
    replace (ly_stk_lo ly) with (ly_stk_lo ly / 4096 * 4096 + ly_stk_lo ly mod 4096) by (pose proof (Z.div_mod (ly_stk_lo ly) 4096); lia).
    rewrite L1, Z.add_0_r. replace (ly_stk_lo ly / 4096 * 4096) with ((ly_stk_lo ly / 4096 * 512) * 8) by lia.
    rewrite Z_mod_mult. reflexivity.
  + assert (E : ly_stk_hi ly - ly_stk_lo ly = (ly_stk_hi ly / 4096 - ly_stk_lo ly / 4096) * 512 * 8).
    { pose proof (Z.div_mod (ly_stk_lo ly) 4096). pose proof (Z.div_mod (ly_stk_hi ly) 4096). lia. }
    rewrite E. apply Z_mod_mult.
Qed.

(* a register a run left as its atom has the value of the seeded state's register *)
Lemma vs_reg_atom : forall E ss (ms : machine_state) (H : word -> bool) (regs : bvmap 5 word) n (r : bv 5),
  st_ok_pi SEGS (@pa_val _ seg_listing PI) E ss (restrict H ms) -> ew E n = getr regs r ->
  sr_get (ss_regs ss) r = SOff n 0 -> getr (ms_regs ms) r = getr regs r.
Proof using.
intros E ss ms H regs n r HS Hn Hs. rewrite (st_ok_pi_restrict_reg H E ss ms r HS), Hs.
cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

Variables gotw guard : Z.
(* the exit to the epilogue KR from a run that kept sp, gp, tp, s6 .. s11 and the frame *)
Lemma vs_exit_KR : vs_KR_stmt B gotw guard ->
  forall e ly' S' W' regs0 mem0 regs1 mem1 md1 v, vs_entry B gotw guard e -> vs_regs e regs0 ->
  vs_slots (rdW W' mem0) (e_sp e) (e_regs e) ->
  ajournal SEGS B STK_reac_declared_vlan_split (e_sp e) (e_FP e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) [] ly' S' W' mem1 md1 0 ->
  (forall r, r = 2 \/ r = 3 \/ r = 4 \/ 22 <= r <= 27 -> getr regs1 (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r)) ->
  (forall a, e_sp e - 64 <= a < e_sp e -> rdW W' mem1 a = rdW W' mem0 a) ->
  getr regs1 10 = w64 v ->
  (forall regs'' md'', getr regs'' 10 = w64 v -> vs_Q B e ly' S' W' regs'' mem1 md'') ->
  vs_goal B e W' (vs_cfg VS_KR regs1 mem1 md1).
Proof using.
intros HKR e ly' S' W' regs0 mem0 regs1 mem1 md1 v HE HR HSL HJ HK HM H10 HQ.
pose proof HR as (Hsp & G3 & G4 & G8 & G9 & G18 & G19 & G22 & G27).
apply (HKR e ly' S' W' regs1 mem1 md1 v HE HJ).
- unfold spZ. change (getr regs1 2) with (getr regs1 (Z_to_bv 5 2)). rewrite (HK 2 ltac:(lia)). exact Hsp.
- change (getr regs1 3) with (getr regs1 (Z_to_bv 5 3)). rewrite (HK 3 ltac:(lia)). exact G3.
- change (getr regs1 4) with (getr regs1 (Z_to_bv 5 4)). rewrite (HK 4 ltac:(lia)). exact G4.
- intros r Hr. rewrite (HK r ltac:(lia)). exact (G27 r Hr).
- change (getr regs1 22) with (getr regs1 (Z_to_bv 5 22)). rewrite (HK 22 ltac:(lia)). exact G22.
- apply (vs_slots_kept (rdW W' mem0)); [exact HSL | exact HM].
- exact H10.
- exact HQ.
Qed.

(* the keep clause of the post (sa_kept) from a state of the body, and across a stretch that writes nothing outside
   the window and E *)
Lemma vs_kept_ctxW : forall e (Wr E : Z -> Prop) regs' mem' md',
  vs_ctxW B e Wr regs' mem' md' -> (forall a, Wr a -> E a) ->
  sa_kept SEGS (e_W e) (e_mem e) (e_W e) mem' (e_regs e) STK_reac_declared_vlan_split E.
Proof using.
intros e Wr E regs' mem' md' (_ & _ & _ & HK & _) HWE a Ha Hw He. apply HK; [exact Ha | exact Hw | intros H; exact (He (HWE a H))].
Qed.
Lemma vs_kept_step : forall (W : world SEGS) mem (W' : world SEGS) mem0 mem1 regs STK (E : Z -> Prop),
  sa_kept SEGS W mem W' mem0 regs STK E ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK <= a < spZ regs) -> ~ E a -> rdW W' mem1 a = rdW W' mem0 a) ->
  sa_kept SEGS W mem W' mem1 regs STK E.
Proof using. intros W mem W' mem0 mem1 regs STK E H0 H1 a Ha Hw He. rewrite (H1 a Ha Hw He). exact (H0 a Ha Hw He). Qed.
Lemma vs_kept_mono : forall (W : world SEGS) mem (W' : world SEGS) mem' regs STK (E E' : Z -> Prop),
  sa_kept SEGS W mem W' mem' regs STK E -> (forall a, E a -> E' a) -> sa_kept SEGS W mem W' mem' regs STK E'.
Proof using. intros W mem W' mem' regs STK E E' H HE a Ha Hw He. apply H; [exact Ha | exact Hw | intros H'; exact (He (HE a H'))]. Qed.
Lemma vs_kept_stepW : forall (W : world SEGS) mem (W1 : world SEGS) mem1 (W2 : world SEGS) mem2 regs STK (E : Z -> Prop),
  sa_kept SEGS W mem W1 mem1 regs STK E ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK <= a < spZ regs) -> ~ E a -> rdW W2 mem2 a = rdW W1 mem1 a) ->
  sa_kept SEGS W mem W2 mem2 regs STK E.
Proof using. intros W mem W1 mem1 W2 mem2 regs STK E H0 H1 a Ha Hw He. rewrite (H1 a Ha Hw He). exact (H0 a Ha Hw He). Qed.

(* a destination of sa_dst is present at every later AR state with the entry's layout, frames and blocks: a frame or a
   block by AR's laws, the real stack by the caller's presence argument *)
Lemma vs_dst_present : forall ly S (W : world SEGS) mem regs d n ly' S' W' mem' md',
  sa_dst SEGS B ly S W mem regs d n ->
  AR SEGS B ly' S' W' mem' md' -> ly' = ly -> frames S' = frames S -> Permutation (ablocks B ly' S') (ablocks B ly S) ->
  (spZ regs <= d -> forall i, 0 <= i < n -> apresent (w_H W) mem (d + i) -> apresent (w_H W') mem' (d + i)) ->
  forall i, 0 <= i < n -> apresent (w_H W') mem' (d + i).
Proof using.
intros ly S W mem regs d n ly' S' W' mem' md' HD HAR' Ely Efr HP HK i Hi. subst ly'.
destruct HD as [((cid & pos & Hin & Hc & H1 & H2) & _) | [((b & m & Hin & H1 & H2) & _) | (H1 & H2 & H3 & _)]].
- assert (Hin' : In (cid, pos) (frames S')) by (rewrite Efr; exact Hin).
  destruct (al_frames _ _ LAWS ly S' W' mem' md' cid pos HAR' Hin') as (_ & _ & Hpr & _).
  exact (proj1 (Hpr (d + i) ltac:(lia))).
- assert (Hin' : In (b, m) (ablocks B ly S')) by exact (Permutation_in _ (Permutation_sym HP) Hin).
  destruct (al_blocks _ _ LAWS ly S' W' mem' md' b m HAR' Hin') as (_ & _ & _ & _ & Hpr & _ & Bm).
  destruct (req_size_pos m ltac:(lia)) as [Q1 Q2].
  exact (proj1 (Hpr (d + i) ltac:(lia))).
- exact (HK H1 i Hi (H3 i Hi)).
Qed.

(* a destination of sa_dst holds no image byte: a frame or a block is client memory (al_client_img), the real stack
   lies above the image *)
Lemma vs_dst_not_img : forall ly S (W : world SEGS) mem md regs STK d n x,
  AR SEGS B ly S W mem md -> astk_ok STK ly (spZ regs) -> sa_dst SEGS B ly S W mem regs d n -> d <= x < d + n ->
  ~ in_img SEGS x.
Proof using.
intros ly S W mem md regs STK d n x HAR Hstk HD Hx Himg.
pose proof (pa_segs_low x Himg) as Hl.
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HD as [((cid & pos & Hin & Hc & H1 & H2) & _) | [((b & m & Hin & H1 & H2) & _) | (H1 & H2 & _)]].
- exact (frm_img SEGS B LAWS ly S W mem md cid pos x HAR Hin ltac:(lia) Himg).
- destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hin) as (_ & _ & _ & _ & _ & _ & Bm).
  destruct (req_size_pos m ltac:(lia)) as [Q1 Q2].
  exact (blk_img SEGS B LAWS ly S W mem md b m x HAR Hin ltac:(lia) Himg).
- unfold kLowMemEnd in Hl. lia.
Qed.

(* a register a run left as its atom, at a state stopped at a call (st_ok, not st_ok_pi) *)
Lemma vs_reg_atom_c : forall E ss (ms : machine_state) (H : word -> bool) (regs : bvmap 5 word) n (r : bv 5),
  st_ok SEGS E ss (restrict H ms) -> ew E n = getr regs r ->
  sr_get (ss_regs ss) r = SOff n 0 -> getr (ms_regs ms) r = getr regs r.
Proof using.
intros E ss ms H regs n r HS Hn Hs. rewrite (st_ok_restrict_reg SEGS H E ss ms r HS), Hs.
cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
End e.

(* split_copy in the code's order (the contract's split_copy, reac_declared_vlan_split_c.v) *)
Lemma vs_copy_code : forall s, SegModel.nulfree s -> (length s < 16)%nat ->
  split_copy s =
  match SegModel.strrchr s 46 with
  | None => None
  | Some di =>
    if (di =? 0)%nat then None else
    match skipn (S di) s with
    | [] => None
    | _ :: _ =>
      if negb (forallb SegModel.isdigit (skipn (S di) s)) then None else
      if (SegModel.strtol10 (skipn (S di) s) <? 1) || (4094 <? SegModel.strtol10 (skipn (S di) s)) then None else Some di
    end
  end.
Proof using.
intros s Hn Hl. unfold split_copy.
destruct (SegModel.strrchr s 46) as [di|] eqn:Hd; [|reflexivity].
pose proof (reac_declared_vlan_split_lem.vs_di_lt s di Hn Hd) as Hdi.
destruct (Nat.eqb_spec di 0) as [H0|H0]; cbn [orb]; [reflexivity|].
assert (Ht : SegModel.nulfree (skipn (S di) s)) by (apply SegModel.nulfree_skipn, Hn).
rewrite (SegModel.hd0_eq0 _ Ht). rewrite (SegModel.cut_nul_id _ Ht).
destruct (skipn (S di) s) as [|t tl] eqn:Es; [reflexivity|].
destruct (forallb SegModel.isdigit (t :: tl)); cbn [negb]; [|reflexivity].
destruct ((SegModel.strtol10 (t :: tl) <? 1) || (4094 <? SegModel.strtol10 (t :: tl))); [reflexivity|].
destruct (Nat.ltb_spec 16 (di + 1)); [lia|]. cbn [orb].
rewrite (SegModel.strlen_id _ Hn). destruct (Nat.ltb_spec 16 (length s + 1)); [lia|]. reflexivity.
Qed.
Lemma vs_copy_some : forall s di, SegModel.nulfree s -> (length s < 16)%nat ->
  SegModel.strrchr s 46 = Some di -> di <> 0%nat -> skipn (S di) s <> [] ->
  forallb SegModel.isdigit (skipn (S di) s) = true ->
  1 <= SegModel.strtol10 (skipn (S di) s) <= 4094 -> split_copy s = Some di.
Proof using.
intros s di Hn Hl Hd H0 Hne Hdg Hr. rewrite (vs_copy_code s Hn Hl), Hd.
destruct (Nat.eqb_spec di 0) as [E|E]; [contradiction|].
destruct (skipn (S di) s) as [|t tl] eqn:Es; [contradiction|]. rewrite Hdg. cbn [negb].
destruct (Z.ltb_spec (SegModel.strtol10 (t :: tl)) 1); [lia|]. destruct (Z.ltb_spec 4094 (SegModel.strtol10 (t :: tl))); [lia|].
reflexivity.
Qed.
End f.
End d.
