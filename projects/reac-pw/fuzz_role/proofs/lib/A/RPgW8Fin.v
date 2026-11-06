From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgImgA RPgMem RPgSeg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
#[local] Arguments x_STK {segs} r. #[local] Arguments x_sp0 {segs} r. #[local] Arguments x_FP {segs} r.
#[local] Arguments x_ly {segs} r. #[local] Arguments x_S {segs} r. #[local] Arguments x_W0 {segs} r.
#[local] Arguments x_mem0 {segs} r. #[local] Arguments x_md0 {segs} r. #[local] Arguments x_own {segs} r.
#[local] Arguments x_k {segs} r. #[local] Arguments x_regs {segs} r. #[local] Arguments x_lyc {segs} r.
#[local] Arguments x_Sc {segs} r. #[local] Arguments x_W {segs} r. #[local] Arguments x_memc {segs} r.
#[local] Arguments x_mdc {segs} r. #[local] Arguments x_RLO {segs} r. #[local] Arguments x_RHI {segs} r.
#[local] Arguments x_e {segs} r. #[local] Arguments x_pos {segs} r.

(* the registers the piece keeps (sp, gp, tp and the callee-saved registers but s8) *)
Definition wkeepF : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27]%bv.
(* where the piece ends: the pod loop's head C (0x80a80) or, when the count is reached, CL (0x81ccc) *)
Definition w_exitF (last : bool) : Z := if last then RS_CL else RS_C.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.

(* the locations the piece leaves alone: a register it keeps, or a cell of the real frame at R + [0, 0x100) *)
Definition wf_okb (l : rl_loc) : bool :=
  match l with
  | LReg r => existsb (Z.eqb r) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27]
  | LCell XR o => (0 <=? o) && (o <=? 0xf8)
  | _ => false
  end.

Lemma wf_reg_keep : forall r, existsb (Z.eqb r) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27] = true ->
  In (Z_to_bv 5 r) wkeepF.
Proof.
  intros r Hr. apply existsb_exists in Hr. destruct Hr as (x & Hx & Hrx). apply Z.eqb_eq in Hrx. subst x.
  unfold wkeepF. cbn [In] in Hx |- *.
  repeat destruct Hx as [<-|Hx]; try contradiction;
  repeat (first [left; apply bv_eq; reflexivity | right]).
Qed.

Lemma wf_at_move : forall (H : word -> bool) mem2 mem3 regs2 regs3 e L,
  (forall r0, In r0 wkeepF -> getr regs3 r0 = getr regs2 r0) ->
  (forall o j, 0 <= o <= 0xf8 -> 0 <= j < 8 ->
     aview rsegs H mem3 (e_R e + o + j) = aview rsegs H mem2 (e_R e + o + j)) ->
  forallb (fun f => wf_okb (fst f)) L = true ->
  rs_at rsegs H mem2 regs2 e L -> rs_at rsegs H mem3 regs3 e L.
Proof.
  intros H mem2 mem3 regs2 regs3 e L Hk Hc Hb HL. unfold rs_at in *.
  induction L as [|[l v] L IH]; [constructor|].
  cbn [forallb] in Hb. apply andb_prop in Hb. destruct Hb as [Hb1 Hb2].
  apply Forall_cons_iff in HL. destruct HL as [H1 H2].
  constructor; [|exact (IH Hb2 H2)].
  cbn [fst snd] in Hb1, H1 |- *. destruct l as [r|b o].
  - cbn [wf_okb] in Hb1. cbn [rl_at] in H1 |- *. rewrite Hk by (apply wf_reg_keep; exact Hb1). exact H1.
  - destruct b; cbn [wf_okb] in Hb1; try discriminate Hb1.
    apply andb_prop in Hb1. destruct Hb1 as [Ho1 Ho2]. apply Z.leb_le in Ho1. apply Z.leb_le in Ho2.
    cbn [rl_at rl_xv] in H1 |- *. eapply val_mem_kept; [|exact H1]. intros j Hj. apply Hc; lia.
Qed.

Lemma wf_P0_mid : forall j, 30 <= j < 43 -> nth (Z.to_nat j) rs_P0 0 = 248.
Proof.
  intros j Hj.
  assert (C : forallb (fun n => nth n rs_P0 0 =? 248) (seq 30 13) = true) by reflexivity.
  rewrite forallb_forall in C. apply Z.eqb_eq, C, in_seq. lia.
Qed.

Lemma wf_PJ_P0 : forall j, 0 <= j < 52 -> ~ (30 <= j < 43) -> nth (Z.to_nat j) rs_PJ 0 = nth (Z.to_nat j) rs_P0 0.
Proof.
  intros j Hj Hn.
  assert (C : forallb (fun n => (Nat.leb 30 n && Nat.ltb n 43) || (nth n rs_PJ 0 =? nth n rs_P0 0)) (seq 0 52) = true)
    by reflexivity.
  rewrite forallb_forall in C. specialize (C (Z.to_nat j) ltac:(apply in_seq; lia)).
  apply orb_prop in C. destruct C as [C|C].
  - apply andb_prop in C. destruct C as [C1 C2]. apply Nat.leb_le in C1. apply Nat.ltb_lt in C2. exfalso. lia.
  - apply Z.eqb_eq in C. exact C.
Qed.

(* the separation facts of rs_pre: R above the allocator's ceiling, the pp block and the frame's shadow bytes
   below it, and the pp block apart from the frame's shadow bytes (both are application memory) *)
Lemma wf_bounds : forall cx, rs_pre rsegs B cx ->
  spZ (x_regs cx) = e_R (x_e cx) /\
  alloc_ceiling + T_SEG_STK <= e_R (x_e cx) /\ e_R (x_e cx) + 0x1a0 <= 2 ^ 47 /\
  e_pp (x_e cx) + Layout.PP_SIZE <= alloc_ceiling /\
  0 <= shadow_addr (e_F (x_e cx)) /\ shadow_addr (e_F (x_e cx)) + 52 <= alloc_ceiling /\
  (e_pp (x_e cx) + Layout.PP_SIZE <= shadow_addr (e_F (x_e cx)) \/
   shadow_addr (e_F (x_e cx)) + 52 <= e_pp (x_e cx)).
Proof.
  intros cx HP. unfold rs_pre, rl_seg_pre in HP.
  destruct HP as (HJ0 & _ & Hsp & _ & _ & HS & _ & HRsz & HRstk & Hown & HF & _ & _ & Hppin & _).
  destruct HJ0 as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hastk & _ & _).
  destruct Hastk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof (al_blocks rsegs B (YG0q.AR_laws_ok rsegs B) _ _ _ _ _ _ _ HAR Hppin) as (_ & _ & Hpceil & Hpapp & _).
  assert (Hin : In (hi_cid role_himg_A, x_pos cx) (frames (x_Sc cx)))
    by (rewrite Hfrs; apply in_or_app; left; exact Hown).
  pose proof (al_frames rsegs B (YG0q.AR_laws_ok rsegs B) _ _ _ _ _ _ _ HAR Hin) as (_ & Hfapp & _).
  rewrite <- HF in Hfapp. change (fs_frame_bytes (hi_cid role_himg_A)) with 512 in Hfapp.
  change (req_size Layout.PP_SIZE) with 19744 in Hpceil, Hpapp.
  change (hi_rsz role_himg_A) with 0x1a0 in HRsz.
  pose proof YM05.alloc_ceiling_value as [Hc _].
  assert (HT : T_SEG_STK = 16384) by reflexivity.
  split.
  { unfold spZ. rewrite Hsp. unfold w64. apply unsigned_lit_small. lia. }
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpapp, Hfapp. unfold shadow_addr, SHADOW_OFF.
  unfold Layout.PP_SIZE.
  destruct Hpapp as (Hp1 & [Hp2 | (Hp3 & Hp4)]); destruct Hfapp as (Hf1 & [Hf2 | (Hf3 & Hf4)]);
    (split; [lia|]); (split; [lia|]); (split; [lia|]); (split; [lia|]); (split; [lia|]);
    first [left; lia | right; lia].
Qed.

(* the journal-and-frame part at the end, from J's and the piece's facts *)
Lemma wf_core : forall cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3,
  rs_pre rsegs B cx ->
  rs_core rsegs B MT cx (rs_E1 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 mem3 md3 (x_k cx) ->
  same_io md2 md3 ->
  (forall r0, In r0 wkeepF -> getr regs3 r0 = getr regs2 r0) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e cx) - ESTACK <= a < e_R (x_e cx)) ->
     ~ (e_pp (x_e cx) <= a < e_pp (x_e cx) + Layout.PP_SIZE) ->
     ~ (shadow_addr (e_F (x_e cx)) + 30 <= a < shadow_addr (e_F (x_e cx)) + 43) ->
     aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  rs_core rsegs B MT cx (rs_E1 rsegs cx) ly2 S2 W2 regs3 mem3 md3.
Proof.
  intros cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 HP HC HAJ Hio Hkeep Hfr.
  pose proof (wf_bounds cx HP) as (Hsp & _).
  assert (HT : T_SEG_STK = 16384) by reflexivity. assert (HE : ESTACK = 4096) by reflexivity.
  unfold rs_core, rs_mid in HC |- *.
  destruct HC as (_ & Hr234 & Hfrm & Hperm & Hio2 & Hmo & Hmem).
  split; [exact HAJ|]. split.
  { intros r0 Hr0. rewrite <- (Hr234 r0 Hr0). apply Hkeep.
    destruct Hr0 as [ -> | [ -> | -> ] ]; unfold wkeepF; cbn [In];
      repeat (first [left; apply bv_eq; reflexivity | right]). }
  split; [exact Hfrm|]. split; [exact Hperm|]. split; [exact (same_io_trans _ _ _ Hio2 Hio)|].
  split; [exact Hmo|].
  intros a Ha Hstk HE1. rewrite <- (Hmem a Ha Hstk HE1). apply Hfr; [exact Ha | | |].
  - intros Hx. apply Hstk. rewrite Hsp. lia.
  - intros Hx. apply HE1. unfold rs_E1. right. exact Hx.
  - intros Hx. apply HE1. unfold rs_E1. left. unfold rl_inw.
    change (hi_w1 role_himg_A) with [(XF, 0x20, 0x160); (XShF, 0, 52); (XR, 0, 0x138)].
    apply Exists_cons_tl, Exists_cons_hd. cbn. lia.
Qed.

(* the frame's shadow bytes at the end: e's 13 granules closed again (0xf8), the others as at J *)
Lemma wf_fsh : forall cx (W2 : world rsegs) mem2 mem3,
  rs_pre rsegs B cx ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e cx) - ESTACK <= a < e_R (x_e cx)) ->
     ~ (e_pp (x_e cx) <= a < e_pp (x_e cx) + Layout.PP_SIZE) ->
     ~ (shadow_addr (e_F (x_e cx)) + 30 <= a < shadow_addr (e_F (x_e cx)) + 43) ->
     aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  (forall o, 30 <= o < 43 ->
     mbyte rsegs (mrestrict (w_H W2) mem3) (shadow_addr (e_F (x_e cx)) + o) = Some (Z_to_bv 8 248)) ->
  rs_fsh_at rsegs cx W2 mem2 rs_PJ -> rs_fsh_at rsegs cx W2 mem3 rs_P0.
Proof.
  intros cx W2 mem2 mem3 HP Hfr Hsh HJ.
  pose proof (wf_bounds cx HP) as (_ & HB1 & HB2 & HB3 & HB4 & HB5 & HB6).
  unfold rs_fsh_at, rl_fsh in HJ |- *.
  assert (L0 : Z.of_nat (length rs_P0) = 52) by reflexivity.
  assert (LJ : Z.of_nat (length rs_PJ) = 52) by reflexivity.
  assert (HT : T_SEG_STK = 16384) by reflexivity. assert (HE : ESTACK = 4096) by reflexivity.
  intros j Hj. rewrite L0 in Hj.
  assert (D : (30 <= j < 43) \/ ~ (30 <= j < 43)) by lia.
  destruct D as [D|D].
  - unfold aview. rewrite (Hsh j D). cbn [option_map]. rewrite (wf_P0_mid j D). reflexivity.
  - rewrite Hfr.
    + rewrite (HJ j) by (rewrite LJ; exact Hj). f_equal. apply wf_PJ_P0; assumption.
    + lia.
    + lia.
    + destruct HB6; lia.
    + lia.
Qed.

Lemma w_finish : forall cx POST rest i k ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r ed regs3 mem3 md3 (last : bool),
  rs_pre rsegs B cx -> (length ps = i)%nat -> (length es = k)%nat ->
  rs_cut_J rsegs B MT cx sh np ps cnt es rest rr r ed ly2 S2 W2 regs2 mem2 md2 ->
  rs_from_C rsegs B MT cx POST rest i (S k) -> rs_from_CL rsegs B MT cx POST rest i ->
  (Z.of_nat (S k) =? cnt) = last ->
  ajournal rsegs B (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx)
    ly2 S2 W2 mem3 md3 (x_k cx) ->
  same_io md2 md3 ->
  (forall r0, In r0 wkeepF -> getr regs3 r0 = getr regs2 r0) ->
  getr regs3 11 = w64 (Z.of_nat (S k)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (e_R (x_e cx) - ESTACK <= a < e_R (x_e cx)) ->
     ~ (e_pp (x_e cx) <= a < e_pp (x_e cx) + Layout.PP_SIZE) ->
     ~ (shadow_addr (e_F (x_e cx)) + 30 <= a < shadow_addr (e_F (x_e cx)) + 43) ->
     aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a) ->
  (forall o, 30 <= o < 43 ->
     mbyte rsegs (mrestrict (w_H W2) mem3) (shadow_addr (e_F (x_e cx)) + o) = Some (Z_to_bv 8 248)) ->
  rm_bytes rsegs (w_H W2) mem3 (e_pp (x_e cx)) (pc_image (PbCut sh ps (Some (es ++ [ed])))) ->
  SRr rsegs W2 (cfg_at rsegs (w_exitF last) regs3 mem3 md3) POST.
Proof.
  intros cx POST rest i k ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r ed regs3 mem3 md3 last
    HP Hi Hk HJ HC HCL Hlast HAJ Hio Hkeep Ha1 Hfr Hsh Hpp.
  pose proof (wf_bounds cx HP) as (_ & HB1 & HB2 & HB3 & HB4 & HB5 & _).
  destruct HJ as (Hbase & HJat & HJsh & _ & _ & Hed & Hedwf).
  destruct Hbase as (Hcore & Hin & Hsr & _ & Hwf & Hlen & Hps & Htie & Hsh0 & Hnp & Hpsnp & Hnp3 & Hsh7 & Hps2
    & Hcnt & Hes & _ & Hescnt).
  pose proof (wf_core cx ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 HP Hcore HAJ Hio Hkeep Hfr) as Hcore3.
  pose proof (wf_fsh cx W2 mem2 mem3 HP Hfr Hsh HJsh) as Hfsh3.
  assert (HT : T_SEG_STK = 16384) by reflexivity. assert (HE : ESTACK = 4096) by reflexivity.
  assert (Hcell : forall o j, 0 <= o <= 0xf8 -> 0 <= j < 8 ->
    aview rsegs (w_H W2) mem3 (e_R (x_e cx) + o + j) = aview rsegs (w_H W2) mem2 (e_R (x_e cx) + o + j)).
  { intros o j Ho Hj. apply Hfr; lia. }
  unfold rs_at_cx in HJat.
  pose proof (fun Hb => wf_at_move _ _ mem3 _ regs3 _ _ Hkeep Hcell Hb HJat) as Hat3.
  specialize (Hat3 eq_refl).
  assert (Htie' : rs_pod_tie sh ps cnt (es ++ [ed]) rest r).
  { destruct Htie as (sel & c & r1 & r2 & T1 & T2 & T3 & T4 & T5 & T6).
    exists sel, c, r1, r2. refine (conj T1 (conj T2 (conj T3 (conj T4 (conj T5 _))))).
    replace (length (es ++ [ed])) with (S (length es)) by (rewrite length_app; cbn [length]; lia).
    rewrite ents_loop_S_end, T6. cbv beta iota. rewrite <- Hed. reflexivity. }
  assert (Hes' : Forall ent_wf (es ++ [ed]))
    by (apply Forall_app; split; [exact Hes | constructor; [exact Hedwf | constructor]]).
  assert (HL : Z.of_nat (length (es ++ [ed])) = Z.of_nat (S k)) by (rewrite length_app, Hk; cbn [length]; lia).
  destruct last; unfold w_exitF.
  - apply Z.eqb_eq in Hlast.
    apply (HCL ly2 S2 W2 regs3 mem3 md3 sh np ps cnt (es ++ [ed]) r Hi).
    unfold rs_cut_CL.
    split; [exact Hcore3|]. split.
    { unfold rs_at_cx, rs_at in Hat3 |- *. eapply incl_Forall; [|exact Hat3].
      unfold rs_L_Dc, rs_L_Dc0. intros x Hx. rewrite !in_app_iff in Hx. rewrite !in_app_iff. cbn [In] in Hx |- *.
      tauto. }
    split; [exact Hfsh3|]. split; [exact Hpp|].
    split; [exact Hin|]. split; [exact Hsr|]. split; [exact Hwf|]. split; [exact Hlen|]. split; [exact Hps|].
    split; [exact Htie'|]. split; [exact Hsh0|]. split; [exact Hnp|]. split; [exact Hpsnp|]. split; [exact Hnp3|].
    split; [exact Hsh7|]. split; [exact Hps2|]. split; [exact Hcnt|]. split; [exact Hes'|]. lia.
  - apply Z.eqb_neq in Hlast.
    apply (HC ly2 S2 W2 regs3 mem3 md3 sh np ps cnt (es ++ [ed]) r Hi).
    { rewrite length_app, Hk. cbn [length]. lia. }
    unfold rs_cut_C, rs_pod_base.
    split.
    { split; [exact Hcore3|]. split; [exact Hin|]. split; [exact Hsr|]. split; [exact Hsr|]. split; [exact Hwf|].
      split; [exact Hlen|]. split; [exact Hps|]. split; [exact Htie'|]. split; [exact Hsh0|]. split; [exact Hnp|].
      split; [exact Hpsnp|]. split; [exact Hnp3|]. split; [exact Hsh7|]. split; [exact Hps2|].
      split; [exact Hcnt|]. split; [exact Hes'|]. split; lia. }
    split.
    { unfold rs_at_cx, rs_at in Hat3 |- *. apply Forall_app. split.
      - eapply incl_Forall; [|exact Hat3].
        unfold rs_L_pod, rs_L_Dc, rs_L_Dc0. intros x Hx. rewrite !in_app_iff in Hx. rewrite !in_app_iff.
        cbn [In] in Hx |- *. tauto.
      - constructor; [|constructor]. cbn [fst snd rl_at]. rewrite HL. exact Ha1. }
    split; [exact Hfsh3 | exact Hpp].
Qed.
End w.
