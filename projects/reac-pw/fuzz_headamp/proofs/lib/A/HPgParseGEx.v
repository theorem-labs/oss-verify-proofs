(* reac-pw/fuzz_headamp: the image-independent lemmas of the two exit segments of reac_headamp_prop_parse_result's walks
   (the walk's end EXIT and the epilogue EPI), shared by image A (fuzz_headamp.asan, lib/A/HPgParseEX.v) and image B
   (fuzz_headamp.asan-ubsan, lib/AU/HPgParseX.v). Stated over lib/A/HPgParseBase.v's hp_ctx, hp_call_ok, hp_core,
   hp_fx and hp_post, for every image. Proves no function (kind: segment lemma).

   What both images do there (measured on the pinned images): EXIT writes res's twelve bytes [res, res + 12) when
   res <> 0 (three instrumented `sw`); EPI stores the frame object's first word at spa + 0x40 (`sd a0,64(sp)`), writes
   0 into the hole's eight shadow bytes (eight `sb zero,k(s10)`), sets a0 = s4, `addi sp,s0,-0x100`, reloads ra and
   s0 .. s11 from sp0 - 8 .. sp0 - 104 and fs0 from sp0 - 112 (`fld fs0,0x90(sp)`), `addi sp,sp,0x100`, `ret`.

   - pxg_frame / pxg_hstack / pxg_hole_band: where the parse's frame and the hole lie, from hd_pre at the call
     (HPgHole.hd_parse_frame, lo_top);
   - pxg_out_apart / pxg_res_apart / pxg_errno_apart: out's 3 (cap + 1) bytes, res's twelve bytes and the errno cell
     lie outside the parse's stack window and the hole, and apart from each other (hd_off_stack, hd_wcell, al_blocks,
     frames_bounds, sep_block_frame, al_client_img, api_env);
   - pxg_hole_zero_call: the hole's bytes read 0 at the call (HPgHole.stack_shadow_zero);
   - pxg_fxk_fs0: fs0 back to its entry bits turns hp_fx into the post's hd_fxk [14; 15];
   - pxg_core_step: hp_core again after a run whose writes lie in [sp - T_parse_STK, sp - 112), the hole and res;
   - pxg_epi_post: the call's post hp_post from the state after the epilogue;
   - pxg_sv_chunks_ok / pxg_present / pxg_hole_present: the entry state of the epilogue's run (the saved words as
     chunks at s0 = sp0, the frame object's word at sp = spa, the hole at s10);
   - pxg_ans_exit / pxg_core_rb0 / pxg_le4_chunk / pxg_frame_view: EXIT's answer, res = 0, the `sw` chunks as res's
     bytes, a run's frame rule through the view. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require FP Mem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgHole HPgMem HPgParseBase.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A.Rt Require Import FMupoison.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ======================================= the epilogue's regions ======================================= *)
(* At a cut's env (Ereg regs (pxg_saved x ++ _)): the 13 saved words and fs0's entry bits are the env slots 32 .. 45 and
   lie at sp0 - 8 .. sp0 - 112 (atom 8, s0 = sp0); the frame object's first word at spa + 0x40 (atom 2, sp = spa) is
   written; the hole's eight bytes at s10 (atom 26) are written. *)
Definition pxg_sv_chunks : list YP09.chunk :=
map (fun i => YP09.mkChunk (- 8 * Z.of_nat (S i)) (CVal 8 (SOff (32 + i) 0))) (seq 0 14).
Definition pxg_r_sv : YP09.region := YP09.mkRegion (Some 8%nat) (-112) 0 0 0 pxg_sv_chunks.
Definition pxg_r_fo : YP09.region := YP09.mkRegion (Some 2%nat) 0x40 0x48 0x40 0x48 [].
Definition pxg_r_h : YP09.region := YP09.mkRegion (Some 26%nat) 0 8 0 8 [].

Lemma pxg_same_io_wvb : forall md l X, same_io md (with_vm_backing l X md).
Proof. intros md l X. destruct md as [fd [maps lazy mat] io fs proc lim tm]. repeat split; reflexivity. Qed.

Lemma pxg_sv_denot0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {segs : list Segment}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Variables akey aph apad asens gotw guard : Z.
Variable dcs : list (Z * Z).
Local Notation pctx := (@hp_ctx segs).
Local Notation call_ok := (hp_call_ok B akey aph apad asens gotw guard dcs).
Implicit Types (x : pctx).

(* the env slots 32 .. 45 of a cut's env: the 13 saved words (HP_SAVED's order) and fs0's entry bits *)
Definition pxg_saved (x : pctx) : list word :=
map (fun c => getr (hx_regs x) (Z_to_bv 5 (snd c))) HP_SAVED ++ [Sem.reg_get (@fp_regs fx) (Z_to_bv 5 8)].

(* ======================================= the frame ======================================= *)
Lemma pxg_layout : forall x, call_ok x -> layout_ok (hx_lyc x).
Proof.
intros x ((HJ & _) & _). pose proof HJ as (HAR & _). exact (am_layout B (hx_lyc x) (hx_Sc x) _ (proj1 HAR)).
Qed.

Lemma pxg_frame : forall x, call_ok x ->
hx_spa x mod 32 = 0 /\ hx_sp x - 0x120 < hx_spa x <= hx_sp x - 0x100 /\
hx_sp0 x - hx_STK x <= hx_sp x - T_parse_STK /\ hx_sp x <= hx_sp0 x /\ hx_sp x mod 16 = 0 /\
alloc_ceiling <= ly_stk_lo (hx_lyc x) /\ ly_stk_lo (hx_lyc x) <= hx_sp0 x - hx_STK x /\
hx_sp0 x <= ly_stk_hi (hx_lyc x) /\ ly_stk_hi (hx_lyc x) <= 2 ^ 47 /\
ly_stk_lo (hx_lyc x) + 64 <= hx_fr x /\ hx_fr x + 128 <= ly_stk_hi (hx_lyc x) /\
ly_stk_lo (hx_lyc x) mod 4096 = 0 /\ ly_stk_hi (hx_lyc x) mod 4096 = 0.
Proof.
intros x Hc. pose proof (pxg_layout x Hc) as LO.
destruct Hc as (HP & _).
pose proof (hd_parse_frame segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP) as (F32 & F1 & F2 & F2' & F3 & F4 & F16 & S16).
destruct HP as (HJ & _ & _ & _ & _ & Hal & Hw1 & Hw2 & _).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof (lo_top _ LO) as (_ & _ & _ & _ & T5 & T6 & _). unfold page_aligned in T5, T6.
unfold hx_fr, hx_spa, hx_sp in *. rewrite Eslo, Eshi in *.
repeat split; lia.
Qed.

Lemma pxg_hstack : forall x pat, call_ok x -> length pat = 8%nat -> Forall (fun v => 0 <= v < 256) pat ->
hstack_ok (hx_lyc x) (hx_fr x) pat.
Proof.
intros x pat Hc Hl Hb. pose proof (pxg_frame x Hc) as (F32 & _ & _ & _ & _ & _ & _ & _ & _ & F5 & F6 & _).
unfold hstack_ok. rewrite Hl. change (8 * Z.of_nat 8) with 64.
split; [unfold hx_fr, hd_fr; apply Z.mod_divide in F32 as [m Hm]; [|lia]; rewrite Hm;
        replace (m * 32 + 64) with ((4 * m + 8) * 8) by lia; apply Z.mod_mul; lia|].
split; [lia|]. split; [lia|]. split; [lia | exact Hb].
Qed.

Lemma pxg_PAT_KEY_ok : length PAT_KEY = 8%nat /\ Forall (fun v => 0 <= v < 256) PAT_KEY.
Proof. split; [reflexivity|]. unfold PAT_KEY. repeat apply Forall_cons; try apply Forall_nil; lia. Qed.

Lemma pxg_hole_band : forall x a, call_ok x -> hp_hole x a ->
kHighShadowBeg <= a < kHighShadowEnd /\ a < ly_stk_lo (hx_lyc x) /\ kLowMemEnd <= a /\ 0 <= a < 2 ^ 64.
Proof.
intros x a Hc Ha. pose proof (pxg_layout x Hc) as LO.
pose proof (pxg_hstack x PAT_KEY Hc (proj1 pxg_PAT_KEY_ok) (proj2 pxg_PAT_KEY_ok)) as OK.
unfold hp_hole, hx_shf in Ha.
destruct (hole_band (hx_lyc x) (hx_fr x) PAT_KEY LO OK a ltac:(change (Z.of_nat (length PAT_KEY)) with 8; lia))
  as (H1 & H2 & H3 & _ & H4).
repeat split; lia.
Qed.

(* the hole's bytes read 0 at the call: they are shadow bytes of the stack range *)
Lemma pxg_hole_zero_call : forall x a, call_ok x -> hp_hole x a -> hx_view x (hx_memc x) a = Some 0.
Proof.
intros x a Hc Ha.
pose proof (pxg_frame x Hc) as (F32 & _ & _ & _ & _ & _ & _ & _ & _ & F5 & F6 & F7 & _).
destruct Hc as ((HJ & _) & _). pose proof HJ as (HAR & _).
unfold hx_view. apply (stack_shadow_zero segs B (hx_lyc x) (hx_Sc x) (hx_W x) (hx_memc x) (hx_mdc x) a HAR).
unfold hp_hole, hx_shf, hx_fr, hd_fr, shadow_addr in *.
apply Z.mod_divide in F32 as [q Hq]; [|lia]. apply Z.mod_divide in F7 as [p Hp]; [|lia].
rewrite Hq in Ha. replace (q * 32 + 64) with ((4 * q + 8) * 8) in Ha by lia. rewrite Z.div_mul in Ha by lia.
rewrite Hp. replace (p * 4096) with ((512 * p) * 8) by lia. rewrite Z.div_mul by lia.
unfold hd_fr in F5, F6. rewrite Hq in F5, F6. rewrite Hp in F5.
split; [lia|]. enough (4 * q + 8 + 8 - 512 * p <= (ly_stk_hi (hx_lyc x) - (512 * p) * 8) / 8) by lia.
apply Z.div_le_lower_bound; lia.
Qed.

(* ======================================= the call's ranges, apart ======================================= *)
Lemma pxg_out_apart : forall x j, call_ok x -> 0 <= j < 3 * (hx_cap x + 1) ->
~ (hx_sp x - T_parse_STK <= hx_O x + j < hx_sp x) /\ ~ hp_hole x (hx_O x + j) /\ ~ in_img segs (hx_O x + j) /\
(hx_R x <> 0 -> ~ (hx_R x <= hx_O x + j < hx_R x + 12)) /\ 4096 <= hx_O x + j < alloc_ceiling.
Proof.
intros x j Hc Hj. pose proof (pxg_frame x Hc) as (_ & _ & Fw & Fsp & _ & Fceil & Flo & _).
pose proof Hc as (HP & _ & _ & _ & _ & _ & HA).
pose proof HP as (HJ & _). pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
destruct HA as (_ & Hcap & (HO0 & HOin & _) & _ & Hoff & HR & _).
pose proof (AR_laws_ok segs B) as LAWS.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR HOin) as (_ & H4096 & Hceilb & Happ & _).
assert (Hrq : req_size (3 * (hx_cap x + 1)) = 3 * (hx_cap x + 1)) by (unfold req_size; destruct (_ =? 0) eqn:E; lia).
rewrite Hrq in Hceilb, Happ.
split; [exact (Hoff (hx_O x + j) ltac:(lia))|].
split.
{ intros Hh. pose proof (pxg_hole_band x _ Hc Hh) as (B1 & _).
  destruct Happ as (_ & [HL | [HH1 HH2]]); unfold kLowShadowBeg, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *; lia. }
split.
{ refine (proj2 (al_client_img _ _ LAWS _ _ _ _ _ _ HAR _)). left. exists (hx_O x), (3 * (hx_cap x + 1)).
  rewrite Hrq. split; [exact HOin | lia]. }
split; [|lia].
intros HR0 Hin. destruct HR as [HR|((Hwin & _) & _ & _)]; [exact (HR0 HR)|].
destruct Hwin as [Hw | (cid & pos & Hown & _ & Hf1 & Hf2)].
- lia.
- assert (Hf : In (cid, pos) (frames (hx_Sc x))) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
  pose proof (sep_block_frame segs B LAWS _ _ _ _ _ _ _ _ _ HAR HOin Hf) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hrq in Hd. lia.
Qed.

Lemma pxg_res_apart : forall x j, call_ok x -> hx_R x <> 0 -> 0 <= j < 12 ->
~ (hx_sp x - T_parse_STK <= hx_R x + j < hx_sp x) /\ ~ hp_hole x (hx_R x + j) /\ ~ in_img segs (hx_R x + j).
Proof.
intros x j Hc HR0 Hj. pose proof (pxg_frame x Hc) as (_ & _ & Fw & Fsp & _ & Fceil & Flo & _).
pose proof Hc as (HP & _ & _ & _ & _ & _ & HA).
pose proof HP as (HJ & _). pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
destruct HA as (_ & _ & _ & _ & _ & HR & _).
pose proof (AR_laws_ok segs B) as LAWS.
destruct HR as [HR|((Hwin & Hoff) & _ & _)]; [contradiction |].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [unfold hx_sp; lia|].
destruct Hwin as [Hw | (cid & pos & Hown & _ & Hf1 & Hf2)].
- split.
  + intros Hh. pose proof (pxg_hole_band x _ Hc Hh) as (B1 & B2 & _). lia.
  + intros Hi. pose proof (segs_low _ Hi). lia.
- assert (Hf : In (cid, pos) (frames (hx_Sc x))) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
  destruct (frames_bounds segs B LAWS _ _ _ _ _ _ _ HAR Hf) as (G1 & G2 & Gapp).
  split.
  + intros Hh. pose proof (pxg_hole_band x _ Hc Hh) as (B1 & _).
    destruct Gapp as (_ & [HL | [HH1 HH2]]); unfold kLowShadowBeg, kHighShadowBeg, kHighShadowEnd, kHighMemBeg in *; lia.
  + exact (frm_img segs B LAWS _ _ _ _ _ cid pos (hx_R x + j) HAR Hf ltac:(lia)).
Qed.

Lemma pxg_res_facts : forall x, call_ok x -> hx_R x <> 0 ->
hx_R x mod 4 = 0 /\ 4096 <= hx_R x /\ hx_R x + 12 <= 2 ^ 47 /\
range_addressable (hx_view x (hx_memc x)) SHADOW_OFF (hx_R x) 12.
Proof.
intros x Hc HR0. pose proof (pxg_frame x Hc) as (_ & _ & Fw & Fsp & _ & Fceil & Flo & Fhi & F47 & _).
pose proof Hc as (HP & _ & _ & _ & _ & _ & HA).
pose proof HP as (HJ & _). pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
destruct HA as (_ & _ & _ & _ & _ & HR & _).
pose proof (AR_laws_ok segs B) as LAWS.
destruct HR as [HR|((Hwin & Hoff) & H4 & Hra)]; [contradiction |].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [exact H4|]. split; [|split; [|exact Hra]].
- destruct Hwin as [Hw | (cid & pos & Hown & _ & Hf1 & Hf2)]; [lia|].
  assert (Hf : In (cid, pos) (frames (hx_Sc x))) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
  destruct (frames_bounds segs B LAWS _ _ _ _ _ _ _ HAR Hf) as (G1 & G2 & _). lia.
- destruct Hwin as [Hw | (cid & pos & Hown & _ & Hf1 & Hf2)]; [lia|].
  assert (Hf : In (cid, pos) (frames (hx_Sc x))) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
  destruct (frames_bounds segs B LAWS _ _ _ _ _ _ _ HAR Hf) as (G1 & G2 & _). lia.
Qed.

Section e.
Hypothesis errno_low : api_env segs B.
Lemma pxg_errno_apart : forall x j, call_ok x -> 0 <= j < 4 ->
~ (hx_sp x - T_parse_STK <= as_errno B + j < hx_sp x) /\ ~ hp_hole x (as_errno B + j) /\ in_img segs (as_errno B + j).
Proof.
intros x j Hc Hj. pose proof (pxg_frame x Hc) as (_ & _ & Fw & Fsp & _ & Fceil & Flo & _).
destruct errno_low as ((E0 & E4) & Eimg & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
split; [lia|]. split; [|apply Eimg; lia].
intros Hh. pose proof (pxg_hole_band x _ Hc Hh) as (_ & _ & B3 & _). lia.
Qed.
End e.

Lemma pxg_cells_cap : forall x, call_ok x -> Z.of_nat (length (ans_cells (hx_ans x))) <= hx_cap x.
Proof.
intros x Hc. pose proof Hc as (_ & _ & _ & _ & _ & _ & (_ & Hcap & _)).
pose proof (Headamp.parse_props_total (hd_props (hx_null x) (hx_bs x)) (hx_cap x) ltac:(lia)) as HOK.
unfold hx_ans. destruct (Headamp.parse_props (hd_props (hx_null x) (hx_bs x)) (hx_cap x)) as [[rcc cl] [[n keys] rf]].
cbn [Headamp.answer_ok] in HOK. unfold ans_cells. cbn [fst snd].
destruct HOK as [[(E1 & E2 & _) | (E1 & E2 & _)] _]; [subst cl; cbn; lia | lia].
Qed.

(* ======================================= the float state ======================================= *)
Lemma pxg_fxk_fs0 : forall (F : bvmap 5 word) (fc : bv 32) (r8 : bv 5), hp_fx F fc -> bv_unsigned r8 = 8 ->
hd_fxk [14; 15] fx (mkFP (bvmap_set r8 (Sem.reg_get (@fp_regs fx) (Z_to_bv 5 8)) F) fc).
Proof.
intros F fc r8 (HF & Hz) H8. split; [|exact Hz].
intros k Hk. cbn [fp_regs] in *.
destruct (Z.eq_dec (bv_unsigned k) 8) as [E|E].
- rewrite (FP.freg_get_same F r8 k _ ltac:(lia)). f_equal. apply bv_eq. rewrite E. reflexivity.
- rewrite (FP.freg_get_other F r8 k _ ltac:(unfold bv_eqb; apply Z.eqb_neq; lia)).
  apply HF. cbn [In]. intros [X|[X|[X|X]]]; [lia | apply Hk; cbn [In]; tauto | apply Hk; cbn [In]; tauto | exact X].
Qed.

(* ======================================= reading a cut's memory ======================================= *)
Lemma pxg_aview_present : forall H (mem : word -> option byte) s v, 0 <= s < 2 ^ 64 -> ~ in_img segs s ->
aview segs H mem s = Some v -> apresent H mem s.
Proof.
intros H mem s v Hs Hn E. unfold aview, mbyte, mrestrict in E.
destruct (H (Z_to_bv 64 s)) eqn:EH.
- rewrite (seg_rom_none segs s Hs Hn) in E. discriminate E.
- destruct (mem (Z_to_bv 64 s)) as [b|] eqn:EM.
  + split; [exact EH | exists b; exact EM].
  + rewrite (seg_rom_none segs s Hs Hn) in E. discriminate E.
Qed.

(* the caller's stack window is present at a cut (the hole lies below it) *)
Lemma pxg_present : forall x pat cl rb regs mem md, hp_core B x pat cl rb regs mem md ->
forall a, hx_sp0 x - hx_STK x <= a < hx_sp0 x -> apresent (w_H (hx_W x)) mem a.
Proof.
intros x pat cl rb regs mem md ((HJ & OK & HP) & _) a Ha.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstatic & _).
pose proof (am_layout B (hx_lyc x) (hx_Sc x) _ (proj1 HAR)) as LO.
pose proof Hstatic as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & _).
apply (proj1 (hp_apresent_unp _ (hU (hx_fr x) pat) mem a
  (hole_free_stack (hx_lyc x) (hx_fr x) pat a LO OK ltac:(rewrite Eslo; lia)))).
apply Hpres. exact Ha.
Qed.

(* the hole's bytes are present at a cut *)
Lemma pxg_hole_present : forall x pat cl rb regs mem md, call_ok x -> hp_core B x pat cl rb regs mem md ->
length pat = 8%nat -> forall o, 0 <= o < 8 -> apresent (w_H (hx_W x)) mem (hx_shf x + o).
Proof.
intros x pat cl rb regs mem md Hc ((HJ & OK & HP) & _) Hl o Ho.
pose proof (pxg_hole_band x (hx_shf x + o) Hc ltac:(unfold hp_hole; lia)) as (_ & _ & L & R).
apply (pxg_aview_present _ _ _ (nth (Z.to_nat o) pat 0) R).
- intros Hi. pose proof (segs_low _ Hi). lia.
- exact (HP o ltac:(rewrite Hl; cbn; lia)).
Qed.

(* the 13 saved words and fs0's entry bits at a cut *)
Lemma pxg_saved_vals : forall x mem, hp_saved_ok x mem -> forall i, (i < 14)%nat ->
val_mem segs (hx_rd x mem) (hx_sp x + - 8 * Z.of_nat (S i)) 8 (bv_unsigned (nth i (pxg_saved x) (Z_to_bv 64 0))).
Proof.
intros x mem (HS & Hf) i Hi.
assert (G : forall o r, In (o, r) HP_SAVED -> val_mem segs (hx_rd x mem) (hx_sp x + o) 8 (bv_unsigned (getr (hx_regs x) (Z_to_bv 5 r)))).
{ intros o r Hin. exact (proj1 (Forall_forall _ _) HS (o, r) Hin). }
unfold pxg_saved, HP_SAVED.
do 13 (destruct i as [|i]; [apply G; cbn [HP_SAVED In]; tauto|]).
destruct i as [|i]; [|lia]. exact Hf.
Qed.

Lemma pxg_sv_chunks_ok : forall x mem E, hp_saved_ok x mem ->
(forall i, (i < 14)%nat -> ew E (32 + i) = nth i (pxg_saved x) (Z_to_bv 64 0)) ->
Forall (YP09.chunk_ok segs E (hx_rd x mem) (hx_sp x)) pxg_sv_chunks.
Proof.
intros x mem E HSV HE. unfold pxg_sv_chunks. apply Forall_forall. intros c Hin.
apply in_map_iff in Hin as (i & <- & Hi). apply in_seq in Hi.
apply (chunk_ok_val segs E _ (hx_sp x) _ 8 _ (bv_unsigned (nth i (pxg_saved x) (Z_to_bv 64 0)))).
- rewrite pxg_sv_denot0, (HE i ltac:(lia)). symmetry. apply Z_to_bv_bv_unsigned.
- apply bv_unsigned_in_range.
- lia.
- exact (pxg_saved_vals x mem HSV i ltac:(lia)).
Qed.

(* ======================================= the walk's end ======================================= *)
(* the answer at EXIT: the folded state *)
Lemma pxg_ans_exit : forall x cl keys rf, hp_m_exit x cl keys rf -> hx_ans x = Headamp.ha_result (cl, keys, rf).
Proof. intros x cl keys rf (Hn & _ & Hr). unfold hx_ans. rewrite Hn. exact Hr. Qed.

(* with res = 0 the core does not depend on res's bytes *)
Lemma pxg_core_rb0 : forall x pat cl rb rb' regs mem md, hx_R x = 0 ->
hp_core B x pat cl rb regs mem md -> hp_core B x pat cl rb' regs mem md.
Proof.
intros x pat cl rb rb' regs mem md HR0 (H1 & H2 & H3 & H4 & H5 & _ & H7).
refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj _ H7)))))). intros X. contradiction.
Qed.

(* a 4-byte chunk of the value e holds the low four bytes of e (an `sw`) *)
Lemma pxg_le4_chunk : forall (E : env) H (m : word -> option byte) base off e,
YP09.chunk_ok segs E (mrestrict H m) base (YP09.mkChunk off (CVal 4 e)) ->
hm_bytes segs H m (base + off) (Mem.le4 (sv_denot E e)).
Proof.
intros E H m base off e Hc. apply hm_bytes_aview. intros i Hi. rewrite Mem.length_le4 in Hi.
destruct (Hc (Z.of_nat i) ltac:(cbn; lia)) as (b & Hb & Hm). cbn [YP09.c_off YP09.c_val cbyte] in Hb, Hm.
injection Hb as <-. unfold aview. rewrite Hm. cbn [option_map]. f_equal. f_equal.
unfold Mem.le4. rewrite hm_nth_le_bytes by lia. unfold YP09.byte_of_word. reflexivity.
Qed.

(* a run's frame rule, through the view *)
Lemma pxg_frame_view : forall x E rs (m m' : word -> option byte),
frame_of E rs (hx_rd x m) (hx_rd x m') ->
forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a -> hx_view x m' a = hx_view x m a.
Proof.
intros x E rs m m' HF a Ha Hn. unfold hx_view, aview, mbyte. unfold hx_rd in HF.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by lia. exact Hn.
Qed.

(* ======================================= hp_core after a run ======================================= *)
(* A run whose writes Wr lie in [sp - T_parse_STK, sp - 112) (below the saved words), the hole and res: hp_core again,
   with res's bytes rb' and the journal of the end memory given. *)
Section k.
Hypothesis errno_low : api_env segs B.
Hypothesis MTL : ameter_laws MT.
Lemma pxg_core_step : forall x pat cl rb rb' regs mem md regs' mem' md' (Wr : Z -> Prop),
call_ok x -> Z.of_nat (length cl) <= hx_cap x ->
hp_core B x pat cl rb regs mem md ->
hjournal segs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) mem' md' (hx_k x) (hx_fr x) pat ->
same_io md md' ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> hx_view x mem' a = hx_view x mem a) ->
(forall a, Wr a -> (hx_sp x - T_parse_STK <= a < hx_sp x - 112) \/ hp_hole x a \/
  (hx_R x <> 0 /\ hx_R x <= a < hx_R x + 12)) ->
(hx_R x <> 0 -> garr8 segs (hx_rd x mem') (hx_R x) (hd_zbytes rb')) ->
getr regs' 2 = getr regs 2 -> getr regs' 8 = getr regs 8 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
getr regs' 9 = getr regs 9 -> getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 ->
getr regs' 26 = getr regs 26 -> getr regs' 27 = getr regs 27 ->
hp_core B x pat cl rb' regs' mem' md'.
Proof.
intros x pat cl rb rb' regs mem md regs' mem' md' Wr Hc Hcl HC HJ' Hio' HK HW HR' E2 E8 E3 E4 E9 E18 E19 E26 E27.
destruct HC as (HJ & Hio & Hkeep & (HSV & Hf) & HO & HR & (ev & HE) & R2 & R8 & R3 & R4 & R9 & R18 & R19 & R26 & R27).
assert (Hm4 : 0 <= hx_sp x - T_parse_STK).
{ pose proof (pxg_frame x Hc) as (_ & _ & Fw & _ & _ & Fceil & Flo & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). lia. }
pose proof (pxg_frame x Hc) as (_ & _ & Fw & Fsp & _ & Fceil & Flo & Fhi & F47 & _).
assert (Hsp64 : hx_sp x <= 2 ^ 47) by lia.
assert (HT : T_parse_STK = 0x120 + 3 * 4096) by reflexivity.
(* every byte the walk keeps: outside Wr *)
assert (NW : forall a, ~ (hx_sp x - T_parse_STK <= a < hx_sp x - 112) -> ~ hp_hole x a ->
  ~ (hx_R x <> 0 /\ hx_R x <= a < hx_R x + 12) -> ~ Wr a).
{ intros a H1 H2 H3 Hw. destruct (HW a Hw) as [X|[X|X]]; auto. }
split; [exact HJ'|].
split; [eapply same_io_trans; [exact Hio | exact Hio']|].
split.
{ intros a Ha Hs Hh Hp. rewrite (HK a Ha); [exact (Hkeep a Ha Hs Hh Hp)|].
  apply NW; [lia | exact Hh |]. intros X. apply Hp. unfold hp_pw. right. left. exact X. }
split.
{ split.
  - apply Forall_forall. intros [o r] Hin. pose proof (proj1 (Forall_forall _ _) HSV _ Hin) as Hv.
    cbn [fst snd] in *.
    assert (Ho : -104 <= o <= -8)
      by (cbn [HP_SAVED In] in Hin; repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]); destruct Hin).
    eapply val_mem_kept; [|exact Hv]. intros k Hk.
    apply HK; [lia|]. apply NW.
    + lia.
    + intros Hh. pose proof (pxg_hole_band x _ Hc Hh) as (_ & B2 & _). lia.
    + intros (HR0 & Hr). pose proof (pxg_res_apart x (hx_sp x + o + k - hx_R x) Hc HR0 ltac:(lia)) as (A1 & _).
      apply A1. replace (hx_R x + (hx_sp x + o + k - hx_R x)) with (hx_sp x + o + k) by lia. lia.
  - eapply val_mem_kept; [|exact Hf]. intros k Hk. unfold HP_FS0 in *.
    apply HK; [lia|]. apply NW.
    + lia.
    + intros Hh. pose proof (pxg_hole_band x _ Hc Hh) as (_ & B2 & _). lia.
    + intros (HR0 & Hr). pose proof (pxg_res_apart x (hx_sp x + -112 + k - hx_R x) Hc HR0 ltac:(lia)) as (A1 & _).
      apply A1. replace (hx_R x + (hx_sp x + -112 + k - hx_R x)) with (hx_sp x + -112 + k) by lia. lia. }
split.
{ change (hm_bytes segs (w_H (hx_W x)) mem' (hx_O x) (ha_cells_bytes cl)).
  apply (hm_bytes_kept segs (w_H (hx_W x)) mem); [exact HO|].
  intros a Ha. rewrite length_ha_cells_bytes in Ha.
  pose proof (pxg_out_apart x (a - hx_O x) Hc ltac:(lia)) as (A1 & A2 & A3 & A4 & A5).
  replace (hx_O x + (a - hx_O x)) with a in * by lia.
  apply HK; [pose proof asan_consts as (C1 & _); lia|].
  apply NW; [lia | exact A2 | intros (HR0 & X); exact (A4 HR0 X)]. }
split; [exact HR'|].
split.
{ exists ev. intros k Hk. rewrite <- (HE k Hk). unfold hx_view.
  pose proof (pxg_errno_apart errno_low x (Z.of_nat k) Hc ltac:(lia)) as (A1 & A2 & A3).
  apply HK; [pose proof (segs_low _ A3) as L; unfold kLowMemEnd in L; lia|]. apply NW; [lia | exact A2 |].
  intros (HR0 & X). pose proof (pxg_res_apart x (as_errno B + Z.of_nat k - hx_R x) Hc HR0 ltac:(lia)) as (_ & _ & A4).
  replace (hx_R x + (as_errno B + Z.of_nat k - hx_R x)) with (as_errno B + Z.of_nat k) in A4 by lia. exact (A4 A3). }
rewrite E2, E8, E3, E4, E9, E18, E19, E26, E27. repeat split; assumption.
Qed.

(* The call's post from the state after the epilogue: the journal at the end memory, the registers and float state
   of the return, a0 the answer's rc; the epilogue's writes Wr lie in the parse's stack window and the hole, and the
   hole reads 0 again. *)
Lemma pxg_epi_post : forall x pat regs mem md (F2 : bvmap 5 word) (fc2 : bv 32) regsF memF mdF (Wr : Z -> Prop),
call_ok x ->
hp_core B x pat (ans_cells (hx_ans x)) (ans_res_bytes (hx_ans x)) regs mem md ->
ajournal segs B (hx_STK x) (hx_sp0 x) (hx_FP x) (hx_ly x) (hx_S x) (hx_W0 x) (hx_mem0 x) (hx_md0 x) (hx_own x)
  (hx_lyc x) (hx_Sc x) (hx_W x) memF mdF (hx_k x) ->
same_io md mdF ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> hx_view x memF a = hx_view x mem a) ->
(forall a, Wr a -> (hx_sp x - T_parse_STK <= a < hx_sp x) \/ hp_hole x a) ->
(forall a, hp_hole x a -> hx_view x memF a = Some 0) ->
aregs_preserved (hx_regs x) regsF -> getr regsF 1 = getr (hx_regs x) 1 ->
hd_fxk [14; 15] fx (mkFP F2 fc2) ->
getr regsF 10 = w64 (ans_rc (hx_ans x)) ->
hp_post B MT x (hx_W x) (mkCfg (@mkst (mkFP F2 fc2) regsF (getr (hx_regs x) 1) memF (seg_rom segs)) mdF).
Proof.
intros x pat regs mem md F2 fc2 regsF memF mdF Wr Hc HC HJF HioF HK HW HZ Hpr H1 Hfx H10.
pose proof (pxg_cells_cap x Hc) as Hcl.
destruct HC as (HJ & Hio & Hkeep & _ & HO & HR & (ev & HE) & _).
assert (NW : forall a, ~ (hx_sp x - T_parse_STK <= a < hx_sp x) -> ~ hp_hole x a -> ~ Wr a).
{ intros a H2 H3 Hw. destruct (HW a Hw) as [X|X]; auto. }
unfold hp_post, hd_parse_post, hd_post.
exists (mkFP F2 fc2), (hx_lyc x), (hx_Sc x), regsF, memF, mdF.
split; [reflexivity|]. split; [exact Hfx|]. split; [exact HJF|]. split; [exact Hpr|]. split; [exact H1|].
split; [reflexivity|]. split; [apply Permutation_refl|]. split; [eapply same_io_trans; [exact Hio | exact HioF]|].
split; [exact (mo_le_refl MT MTL (hx_Sc x))|].
split.
{ intros a Ha Hs HEa.
  assert (Hh : hp_hole x a \/ ~ hp_hole x a) by (unfold hp_hole; lia).
  destruct Hh as [Hh|Hh].
  - change (hx_view x memF a = hx_view x (hx_memc x) a). rewrite (HZ a Hh). symmetry.
    exact (pxg_hole_zero_call x a Hc Hh).
  - change (hx_view x memF a = hx_view x (hx_memc x) a). rewrite (HK a Ha (NW a Hs Hh)).
    exact (Hkeep a Ha Hs Hh HEa). }
split; [exact H10|].
split.
{ change (hm_bytes segs (w_H (hx_W x)) memF (hx_O x) (ha_cells_bytes (ans_cells (hx_ans x)))).
  apply (hm_bytes_kept segs (w_H (hx_W x)) mem); [exact HO|].
  intros a Ha. rewrite length_ha_cells_bytes in Ha.
  pose proof (pxg_out_apart x (a - hx_O x) Hc ltac:(lia)) as (A1 & A2 & _ & _ & A5).
  replace (hx_O x + (a - hx_O x)) with a in * by lia.
  apply HK; [pose proof asan_consts as (C1 & _); lia | exact (NW a A1 A2)]. }
split.
{ intros HR0. change (hm_bytes segs (w_H (hx_W x)) memF (hx_R x) (ans_res_bytes (hx_ans x))).
  apply (hm_bytes_kept segs (w_H (hx_W x)) mem); [exact (HR HR0)|].
  intros a Ha. unfold ans_res_bytes, ha_res_bytes in Ha. rewrite !length_app, !Mem.length_le4 in Ha. cbn in Ha.
  pose proof (pxg_res_apart x (a - hx_R x) Hc HR0 ltac:(lia)) as (A1 & A2 & _).
  pose proof (pxg_res_facts x Hc HR0) as (_ & R4 & R47 & _).
  replace (hx_R x + (a - hx_R x)) with a in * by lia.
  apply HK; [lia | exact (NW a A1 A2)]. }
exists ev. intros k Hk. rewrite <- (HE k Hk). unfold hx_view in HK.
pose proof (pxg_errno_apart errno_low x (Z.of_nat k) Hc ltac:(lia)) as (A1 & A2 & A3).
apply HK; [pose proof (segs_low _ A3) as L; unfold kLowMemEnd in L; lia | exact (NW _ A1 A2)].
Qed.
End k.

End g.

Print Assumptions pxg_epi_post.
Print Assumptions pxg_core_step.
Print Assumptions pxg_sv_chunks_ok.
Print Assumptions pxg_fxk_fs0.
