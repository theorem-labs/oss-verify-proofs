From Stdlib Require Import ZArith List Bool Lia Permutation.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require RcIdentModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Tac_si.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Exec Step Tac.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0 Contract FrameAPI KindBGlue MemNorm.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import SlotInvU put_dec_c reac_box_family_stem_c reac_box_family_stem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog.Seg Require Import UTac_uhj UTac_uhj_i.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.SlotInv(HWT_ADDR, IN_SLASH, OUT_PAREN, CAT_N,
  CAT_ROW, bsz, z8, zlen, fw_res, id_VER, ver_res, EV1, EV2, EV, wn, s_open, s_in, s_out, dp1, dp2, ld1, ld2,
  dropped, exp_mask).
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.put_dec_c(dec_len).
Import ListNotations.
Open Scope Z_scope.


From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require H01.
Module PH01 := OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg.H01.

Local Ltac OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib.Step.mem_after_store_opt ::= idtac.

Definition WU (S0 : Z) : list ivl :=
  [(S0 + 24, S0 + 32); (S0 + 64, S0 + 65); (S0 + 216, S0 + 224); (S0 + 242, S0 + 243)].
Definition stemA (S0 hmn mn0 fam : Z) : Z :=
  if negb (hmn =? 0) && negb (mn0 =? 0) then S0 + 149 else STEM_Addr fam.
Definition qw (m : word -> option byte) (a v : Z) : Prop := bytes_at rsegs m a (le8 (Z_to_bv 64 v)).

Lemma mfr_write_u : forall W m0 m a bs, mfr W m0 m -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
  inside W a (Z.of_nat (length bs)) -> mfr W m0 (write_to_mem m (wa a) bs).
Proof.
  intros W m0 m a bs (A1 & B1 & C1') Ha Hl Hin. split; [apply munch_write; auto|].
  split; [apply wmono_write; auto|].
  intros x Hx. rewrite write_to_mem_spec by lia.
  destruct (_ && _)%bool eqn:E; [|apply C1'; exact Hx].
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
  destruct (nth_error bs (Z.to_nat (bv_unsigned x - a))) eqn:N; [discriminate|].
  apply nth_error_None in N. lia.
Qed.

Ltac st_ok_u A n :=
  lazymatch goal with
  | WR : wr_at rsegs ?m ?lo ?len |- Exec.evt _ _ (MS _ _ _ _ _ ?m _) =>
      let HS := fresh "HS" in
      pose proof (wr_at_store_ok rsegs m lo len (A - lo) n WR ltac:(lia) ltac:(lia)) as HS;
      replace (lo + (A - lo)) with A in HS by lia
  end.

Ltac after_st_u :=
  try fix_lit_store;
  lazymatch goal with
  | |- Exec.evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?m ?a ?bs) ?ro) =>
    let A := addr_expr a in
    change (write_to_mem m a bs) with (write_to_mem m (wa A) bs);
    repeat match goal with
    | H : bytes_at rsegs m ?A2 ?bs2 |- _ =>
        first [ apply (bytes_at_write_other rsegs m A bs A2 bs2) in H; [ | lia | simpl_sizes; lia | simpl_sizes; lia ]
              | clear H ]
    | H : wr_at rsegs m ?A2 ?n2 |- _ => apply (wr_at_write rsegs m A2 n2 (wa A) bs) in H
    | H : mfr ?W ?m0 m |- _ =>
        apply (mfr_write_u W m0 m A bs) in H; [ | lia | simpl_sizes; lia | try unfold WU; cbn [inside]; simpl_sizes; lia ]
    | H : ov_read_bytes rsegs m _ _ = _ |- _ => clear H
    | H : store_ok rsegs m _ _ = true |- _ => clear H
    end;
    let H := fresh "NW" in
    pose proof (bytes_at_write_same rsegs m A bs ltac:(lia) ltac:(simpl_sizes; lia)) as H;
    let m' := fresh "m" in
    remember (write_to_mem m (wa A) bs) as m' eqn:Heqm; clear Heqm
  end.

Ltac wsolve i o :=
  rewrite ?PH01.land1_mod in *;
  unfold PH01.wokb, okw; rewrite ?(PH01.even_land1 i), ?(PH01.even_land1 o) by lia; rewrite ?PH01.land1_mod;
  repeat match goal with
  | |- context [Z.eqb ?x ?y] => destruct (Z.eqb_spec x y)
  | |- context [Z.leb ?x ?y] => destruct (Z.leb_spec x y)
  end; cbn [andb orb negb]; lia.

Ltac wclose i o :=
  apply evt_done; do 2 eexists; split; [reflexivity|];
  rewrite ?PH01.snez_or by lia; f_equal; wsolve i o.

Lemma h01u_a : forall (x1 x3 x4 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (S0 i o r : Z),
  0 <= S0 -> S0 + 384 <= 2 ^ 64 -> 0 <= i < 256 -> 0 <= o < 256 -> (r = 0 \/ r = -1) ->
  ov_read_bytes rsegs m (wa (S0 + 56)) 8 = Some (le8 (Z_to_bv 64 o)) ->
  Exec.evt rsegs (fun s => exists y10 y11 : word,
    s = MS (mkR x1 (Z_to_bv 64 S0) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 i) y10 y11 (Z_to_bv 64 o) x13 x14 x15 x16 x17
                x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 r) x26 x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x139f8) fc None m (seg_rom rsegs) /\ y10 = Z_to_bv 64 (PH01.wokb i o))
    (MS (mkR x1 (Z_to_bv 64 S0) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 i) (Z_to_bv 64 r) x11 x12 x13 x14 x15
             x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 0x139ac) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x3 x4 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 F fc m S0 i o r Hs0 Hs1 Hi Ho Hr RD.
  step. step. step. step.
  lazymatch goal with |- context [if ?c then _ else _] =>
    replace c with false by (destruct Hr as [-> | ->]; vm_compute; reflexivity) end; cbv iota.
  step.
  step. if_cases Hc1; zify_cond Hc1.
  - step. if_cases Hc2; zify_cond Hc2.
    + step. step. wclose i o.
    + step. step. step. if_cases Hc3; zify_cond Hc3.
      * wclose i o.
      * step. step. if_cases Hc4; zify_cond Hc4.
        -- wclose i o.
        -- step. step. wclose i o.
  - step. step. step. if_cases Hc5; zify_cond Hc5.
    + wclose i o.
    + step. step. if_cases Hc6; zify_cond Hc6.
      * wclose i o.
      * step. if_cases Hc2; zify_cond Hc2.
        -- step. step. wclose i o.
        -- step. step. step. if_cases Hc3; zify_cond Hc3.
           ++ wclose i o.
           ++ step. step. if_cases Hc4; zify_cond Hc4.
              ** wclose i o.
              ** step. step. wclose i o.
Qed.

Lemma rd_all_u : forall m a bs, bytes_at rsegs m a bs -> ov_read_bytes rsegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. rewrite <- (Z.add_0_r a) at 1.
  rewrite (bytes_at_read rsegs m a bs 0 (length bs) H) by lia. cbn [Z.to_nat skipn]. rewrite firstn_all. reflexivity.
Qed.

Ltac stem_fin S0 HSA :=
  apply evt_done; do 4 eexists; split; [reflexivity|]; split; [eassumption|]; split; [eassumption|];
  unfold qw; rewrite HSA;
  match goal with
  | NW : bytes_at rsegs ?mm (S0 + 24) (le8 ?w) |- bytes_at rsegs ?mm (S0 + 24) _ =>
      eapply bytes_at_ext; [exact NW|]; f_equal; apply bv_eq; vm_compute; reflexivity
  end.

Ltac stemof S0 fam HSA :=
  step; step; step;
  let Hc := fresh "Hc" in
  assert (Hc : fam = 1 \/ fam = 2 \/ fam = 3 \/ ~ (1 <= fam <= 3)) by lia;
  let Ef := fresh "Ef" in let Hn := fresh "Hn" in
  destruct Hc as [Ef | [Ef | [Ef | Hn]]];
  [ subst fam; if_false;
    match goal with T : bytes_at rsegs ?mm 0x105cc _ |- _ => pose proof (rd_all_u _ _ _ T) as RT; rewrite length_le4 in RT end;
    step; step; step; step; step; step; step; st_ok_u (S0 + 24) 8%nat; step; after_st_u; stem_fin S0 HSA
  | subst fam; if_false;
    match goal with T : bytes_at rsegs ?mm 0x105d0 _ |- _ => pose proof (rd_all_u _ _ _ T) as RT; rewrite length_le4 in RT end;
    step; step; step; step; step; step; step; st_ok_u (S0 + 24) 8%nat; step; after_st_u; stem_fin S0 HSA
  | subst fam; if_false;
    match goal with T : bytes_at rsegs ?mm 0x105d4 _ |- _ => pose proof (rd_all_u _ _ _ T) as RT; rewrite length_le4 in RT end;
    step; step; step; step; step; step; step; st_ok_u (S0 + 24) 8%nat; step; after_st_u; stem_fin S0 HSA
  | if_true_by (stem_bltu fam ltac:(lia) Hn); step; step; st_ok_u (S0 + 24) 8%nat; step; after_st_u;
    rewrite (STEM_Addr_other fam Hn) in HSA; stem_fin S0 HSA ].

Lemma h01u_run : forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (S0 i o r hmn mn0 fam : Z),
  x2 = Z_to_bv 64 S0 -> x9 = Z_to_bv 64 i -> x10 = Z_to_bv 64 r -> x18 = Z_to_bv 64 hmn -> x26 = Z_to_bv 64 fam ->
  LOWTOP <= S0 -> S0 + 384 <= 2 ^ 64 -> 0 <= i < 256 -> 0 <= o < 256 -> 0 <= hmn < 256 -> 0 <= mn0 < 256 ->
  0 <= fam < 128 -> (r = 0 \/ r = -1) -> (r = 0 -> PH01.wokb i o = 1) ->
  wr_at rsegs m S0 256 -> qw m (S0 + 56) o -> bytes_at rsegs m (S0 + 149) [Z_to_bv 8 mn0] ->
  qw m (S0 + 24) (S0 + 149) ->
  bytes_at rsegs m 0x105cc (le4 (Z_to_bv 64 (-764))) -> bytes_at rsegs m 0x105d0 (le4 (Z_to_bv 64 (-552))) ->
  bytes_at rsegs m 0x105d4 (le4 (Z_to_bv 64 (-227))) ->
  Exec.evt rsegs
    (fun ms' => exists m' (y10 y11 y26 : word), mfr (WU S0) m m' /\
       ((PH01.wokb i o = 0 /\ r = -1 /\
         ms' = MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 y10 y11 (Z_to_bv 64 o) x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 r) x26 x27 x28 x29 x30 x31)
                  F (Z_to_bv 64 0x13d84) fc None m' (seg_rom rsegs)) \/
        (PH01.wokb i o = 1 /\
         ms' = MS (mkR (Z_to_bv 64 0x13a98) x2 x3 x4 x5 x6 x7 (Z_to_bv 64 (S0 + 192)) x9 (Z_to_bv 64 (S0 + 192))
                       (Z_to_bv 64 (S0 + 216)) x9 (Z_to_bv 64 2) x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 (Z_to_bv 64 r) y26 (Z_to_bv 64 o) x28 x29 x30 x31)
                  F (Z_to_bv 64 put_dec_c.PUT_DEC) fc None m' (seg_rom rsegs) /\
         wr_at rsegs m' S0 256 /\ qw m' (S0 + 24) (stemA S0 hmn mn0 fam) /\ qw m' (S0 + 216) 0)))
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28
             x29 x30 x31)
        F (Z_to_bv 64 0x139ac) fc None m (seg_rom rsegs)).
Proof.
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25
    x26 x27 x28 x29 x30 x31 F fc m S0 i o r hmn mn0 fam E2 E9 E10 E18 E26 HS0 HS1 Hi Ho Hh Hmn Hf Hr Hw
    WR HQ56 HM G24 T1 T2 T3.
  subst x2 x9 x10 x18 x26.
  unfold qw in HQ56.
  eapply Exec.evt_cut; [apply h01u_a; [lia | lia | exact Hi | exact Ho | exact Hr | exact (rd8 _ _ _ HQ56)]|].
  intros s (y10 & y11 & -> & ->).
  assert (HW : PH01.wokb i o = 0 \/ PH01.wokb i o = 1) by (unfold PH01.wokb; destruct (_ && _ && _); auto).
  eapply (Exec.evt_cut rsegs (fun s => exists y11 : word,
    s = MS (mkR x1 (Z_to_bv 64 S0) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 i) (Z_to_bv 64 (PH01.wokb i o)) y11
                (Z_to_bv 64 o) x13 x14 x15 x16 x17 (Z_to_bv 64 hmn) x19 x20 x21 x22 x23 x24 (Z_to_bv 64 r)
                (Z_to_bv 64 fam) x27 x28 x29 x30 x31)
           F (Z_to_bv 64 0x13a04) fc None m (seg_rom rsegs))).
  { destruct Hr as [-> | ->].
    - rewrite (Hw eq_refl). step. step. if_false. step. if_false. apply evt_done. eexists. reflexivity.
    - step. step. if_true. apply evt_done. eexists. reflexivity. }
  intros s (y11' & ->).
  unfold qw in G24.
  pose proof (mfr_refl (WU S0) m) as MF.
  st_ok_u (S0 + 64) 1%nat. step. after_st_u.
  st_ok_u (S0 + 242) 1%nat. step. after_st_u.
  step. destruct HW as [HW|HW]; rewrite HW.
  - if_true. apply evt_done. eexists. do 3 eexists. split; [exact MF|].
    left. split; [reflexivity|]. split; [destruct Hr as [->| ->]; [rewrite (Hw eq_refl) in HW; discriminate|reflexivity]|].
    reflexivity.
  - if_false.
    pose proof (rd8 _ _ _ HQ56) as R56. step.
    eapply (Exec.evt_cut rsegs (fun s => exists (y10 y11 y26 : word) m',
       s = MS (mkR x1 (Z_to_bv 64 S0) x3 x4 x5 x6 x7 x8 (Z_to_bv 64 i) y10 y11 (Z_to_bv 64 o) x13 x14 x15 x16 x17
                   (Z_to_bv 64 hmn) x19 x20 x21 x22 x23 x24 (Z_to_bv 64 r) y26 (Z_to_bv 64 o) x28 x29 x30 x31)
              F (Z_to_bv 64 0x13a7c) fc None m' (seg_rom rsegs) /\
       mfr (WU S0) m m' /\ wr_at rsegs m' S0 256 /\ qw m' (S0 + 24) (stemA S0 hmn mn0 fam))).
    { step. if_cases Hd1; zify_cond Hd1.
      - assert (HSA : stemA S0 hmn mn0 fam = STEM_Addr fam) by (unfold stemA; rewrite Hd1; reflexivity).
        stemof S0 fam HSA.
      - pose proof (rd1 _ _ _ HM) as RD. step. step. if_cases Hd2; zify_cond Hd2;
          rewrite (unsigned_lit (bv_unsigned (Z_to_bv 8 mn0))), PH01.u8_lit in Hd2 by (rewrite ?PH01.u8_lit; lia).
        + apply evt_done. do 4 eexists. split; [reflexivity|]. split; [exact MF|]. split; [exact WR|].
          unfold qw, stemA. rewrite (proj2 (Z.eqb_neq hmn 0) Hd1), (proj2 (Z.eqb_neq mn0 0) Hd2). exact G24.
        + assert (HSA : stemA S0 hmn mn0 fam = STEM_Addr fam)
            by (unfold stemA; rewrite Hd2; cbn [Z.eqb negb]; rewrite andb_false_r; reflexivity).
          stemof S0 fam HSA. }
    intros s (z10 & z11 & z26 & m2 & -> & MF2 & WR2 & HQ2). unfold qw in HQ2.
    st_ok_u (S0 + 216) 8%nat. step. after_st_u.
    step. step. step. step. step. step.
    apply evt_done. do 4 eexists. split; [eassumption|]. right. split; [reflexivity|].
    split; [reflexivity|]. split; [eassumption|]. unfold qw. split; eassumption.
Unshelve. all: exact (Z_to_bv 64 0).
Qed.

Section H01.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts_u B APIf LS SH SK ra empty.
Hypothesis PD : put_dec_c.put_dec_contract.

Lemma seg_H01 : Hcut B APIf ra (Inv_U13a98 B APIf ra empty) -> Hcut B APIf ra (Inv_U13d84 B APIf ra empty) ->
  Hcut B APIf ra (Inv_U139ac B APIf ra empty).
Proof.
  intros H98 H84 g c (nm & tk & dp & HC).
  eapply (seg_go2 B APIf ra empty FF); [exact H98 | exact H84 | | | exact HC | ].
  { intros c' HC'. unfold Inv_U13a98. exists nm, tk, dp. exact HC'. }
  { intros c' HC'. unfold Inv_U13d84. exists nm, tk, dp. exact HC'. }
  intros L A regs mem md HFR HPM HP.
  destruct (start_facts B APIf ra empty FF _ _ _ _ _ _ _ _ HFR) as (HRO & E2 & HS0 & HS1 & HS2 & HMI0 & HSTK0 & HWR0).
  destruct HP as ((((HG24 & HID) & E9 & HQ56 & HQ48 & E19 & E18 & E24 & E23 & E25 & E26) & E20 & E21 & E22 & HQ0
    & HQ8) & E10 & HOU).
  pose proof (rec_id_length (g_in g) (NRn g)) as HIL.
  pose proof (inb_range (g_in g) (cT (g_in g) + 1)) as Ri. pose proof (inb_range (g_in g) (cT (g_in g) + 2)) as Ro.
  change (inb (g_in g) (cT (g_in g) + 1)) with (t_in (g_in g)) in Ri.
  change (inb (g_in g) (cT (g_in g) + 2)) with (t_out (g_in g)) in Ro.
  set (hmn := RcIdentModel.has_model_name (idT (g_in g))) in *.
  assert (Hh : 0 <= hmn < 256) by (unfold hmn, RcIdentModel.has_model_name; apply bz_range).
  set (mn0 := RcIdentModel.bz (RcIdentModel.nthb (rec_id (g_in g) (NRn g)) 3)).
  assert (Hmn : 0 <= mn0 < 256) by (unfold mn0; apply bz_range).
  pose proof (Tac_sh1.n_fam_range (g_in g)) as Hf.
  pose proof (Tac_si.n_r_cases (g_in g)) as Hr.
  assert (Hw : n_r (g_in g) = 0 -> PH01.wokb (t_in (g_in g)) (t_out (g_in g)) = 1).
  { intros H0. destruct (Tac_si.n_r0 _ H0) as [Wk _]. unfold PH01.wokb. unfold n_wok in Wk. rewrite Wk. reflexivity. }
  unfold IDb, G24, q64, spk in *.
  set (S0 := g_S g - 384) in *.
  assert (HFS : fsp g = S0) by (unfold fsp, SLOT_FRAME, S0; reflexivity). rewrite HFS in *.
  assert (WR : wr_at rsegs (normalize rsegs mem) S0 256) by (eapply wr_sub; [exact HWR0 | unfold S0; lia | unfold S0; lia | lia]).
  pose proof (bytes_at_normalize rsegs mem _ _ HRO HQ56) as HQ56n.
  pose proof (bytes_at_normalize rsegs mem _ _ HRO HID) as HIDn.
  pose proof (bytes_at_normalize rsegs mem _ _ HRO HG24) as HG24n.
  assert (HM : bytes_at rsegs (normalize rsegs mem) (S0 + 149) [Z_to_bv 8 mn0]).
  { pose proof (bytes_at_one _ _ _ 3 HIDn ltac:(rewrite HIL; unfold RcIdentModel.ID_SIZE; lia)) as X.
    unfold mn0. rewrite Tac_sh1.zb_bz. replace (S0 + 149) with (S0 + 146 + Z.of_nat 3) by lia. exact X. }
  assert (T1 : bytes_at rsegs (normalize rsegs mem) 0x105cc (le4 (Z_to_bv 64 (-764))))
    by (apply bytes_at_ro_agree_u; [apply ro_agree_inv; exact HMI0 | lia | rewrite length_le4; lia |
        apply ro_bytes_b_sound; vm_compute; reflexivity]).
  assert (T2 : bytes_at rsegs (normalize rsegs mem) 0x105d0 (le4 (Z_to_bv 64 (-552))))
    by (apply bytes_at_ro_agree_u; [apply ro_agree_inv; exact HMI0 | lia | rewrite length_le4; lia |
        apply ro_bytes_b_sound; vm_compute; reflexivity]).
  assert (T3 : bytes_at rsegs (normalize rsegs mem) 0x105d4 (le4 (Z_to_bv 64 (-227))))
    by (apply bytes_at_ro_agree_u; [apply ro_agree_inv; exact HMI0 | lia | rewrite length_le4; lia |
        apply ro_bytes_b_sound; vm_compute; reflexivity]).
  assert (HSA : stemA S0 hmn mn0 (n_fam (g_in g)) = stem_addr g).
  { unfold stemA, stem_addr, n_use_said, n_said, spk, mn0, hmn. rewrite HFS.
    rewrite (Tac_sh1.nthb_mn0 (idT (g_in g)) HIL). reflexivity. }
  pose proof (stem_addr_cases g) as HSP. unfold spk in HSP. rewrite HFS in HSP.
  assert (HCS : cstr mem (stem_addr g) (n_stem (g_in g))).
  { unfold stem_addr, n_stem, spk. rewrite HFS. destruct (n_use_said (g_in g)).
    - replace (S0 + 149) with (S0 + 146 + 3) by lia. apply name_cstr_u; [exact HID | exact HIL | apply rec_id_b19].
    - unfold cstr. replace (stem_img (n_fam (g_in g)) ++ [z8]) with (STEM (n_fam (g_in g))) by reflexivity.
      apply bytes_at_ro_agree_u; [exact HRO | | | apply STEM_ro].
      + unfold STEM_Addr. destruct (n_fam (g_in g) =? 1); [|destruct (n_fam (g_in g) =? 2); [|destruct (n_fam (g_in g) =? 3)]]; lia.
      + unfold STEM_Addr, STEM, STEM_cstr. rewrite length_app, length_map.
        destruct (n_fam (g_in g) =? 1); [|destruct (n_fam (g_in g) =? 2); [|destruct (n_fam (g_in g) =? 3)]]; cbn; lia. }
  unfold rmk, Frame.mkR.
  eapply Exec.evt_cut.
  { eapply h01u_run with (S0 := S0) (i := t_in (g_in g)) (o := t_out (g_in g)) (r := n_r (g_in g)) (hmn := hmn)
      (mn0 := mn0) (fam := n_fam (g_in g)).
    all: first [exact E2 | exact E9 | exact E10 | exact E18 | exact E26 | lia | (unfold S0; lia) |
      (unfold S0; lia) | exact Hr | exact Hw | exact WR |
      exact HQ56n | exact HM | exact HG24n | exact T1 | exact T2 | exact T3 | idtac]. }
  intros ms (m' & y10 & y11 & y26 & MF & [(HW0 & Hr1 & ->) | (HW1 & -> & WR' & HQ24 & HQ216)]).
  - pose proof MF as (MU & WM & _).
    assert (FW : Forall (fun iv => g_S g - 65536 <= fst iv /\ snd iv <= g_S g - 104) (WU S0))
      by (unfold WU, S0; repeat (apply Forall_cons; [cbn [fst snd]; split; lia|]); apply Forall_nil).
    apply (fin_r g mem regs _ _ _ _ _ m' (munch_SWIN g _ _ _ MU FW) WM (mfr_stk _ _ _ _ _ MF HSTK0));
      [first [exact E2 | rewrite E2; reflexivity] | reflexivity | reflexivity |].
    intros R' m'' HG HREL. cbv beta.
    assert (KMm : KM (WU S0) mem m'') by exact (KM_of _ mem m' m'' HRO MU HREL).
    assert (HO' : OUTS g nm tk dp m'')
      by exact (OUTS_keep B APIf ra empty FF g _ nm tk dp L A regs mem md m' m'' HFR HPM (munch_SWIN g _ _ _ MU FW)
        HREL HOU).
    unfold IRb, IDb, q64, spk. rewrite ?HFS.
    split; [apply KMm; [rewrite rec_id_length; unfold RcIdentModel.ID_SIZE; unfold WU; cbn; lia | exact HID]|].
    split; [kr HG|].
    split; [apply KMm; [rewrite length_le8; unfold WU; cbn; lia | exact HQ56]|].
    split; [apply KMm; [rewrite length_le8; unfold WU; cbn; lia | exact HQ48]|].
    split; [kr HG|]. split; [kr HG|]. split; [kr HG|]. split; [kr HG|]. split; [kr HG|].
    split; [rewrite HG; greg2; reflexivity|]. split; [kr HG|]. split; [exact HO'|].
    intros H0. lia.
  - assert (Wk : n_wok (g_in g) = true)
      by (unfold PH01.wokb in HW1; unfold n_wok; destruct (_ && _ && _); [reflexivity | discriminate]).
    destruct (wok_chans _ Wk) as [Hi Ho]. pose proof (DEC2_len _ Hi) as Li.
    unfold qw in HQ24, HQ216. rewrite HSA in HQ24.
    pose proof MF as (MU1 & WM1 & _).
    pose proof (mfr_stk _ _ _ _ _ MF HSTK0) as STK1.
    assert (RO1 : ro_agree rsegs m').
    { apply (ro_agree_munch (WU S0) (normalize rsegs mem) m' (ro_agree_inv _ HMI0) MU1).
      unfold WU, S0 in *.
      repeat (apply Forall_cons; [cbn [fst]; lia|]). apply Forall_nil. }
    rewrite E2, E9.
    eapply (pd_call PD) with (lo := g_S g - 16384) (b := S0 + 192) (p := S0 + 216) (v := t_in (g_in g)) (mn := 2)
      (N := Z_to_bv 64 0);
      rewrite ?(MState.unsigned_lit 0), ?(MState.unsigned_lit S0) by (unfold S0; lia);
      unfold put_dec_c.PUT_DEC_FRAME, dec_len in *; rewrite ?Li.
    all: try first
      [ reflexivity
      | exact HQ216
      | exact RO1
      | eapply wr_sub; [exact WR' | unfold S0; lia | unfold S0; lia | lia]
      | rewrite MState.unsigned_lit by lia; apply Z.mod_small; lia
      | left; rewrite MState.unsigned_lit by lia; lia
      | unfold S0; Z.div_mod_to_equations; lia
      | unfold S0; lia
      | right; unfold S0; lia
      | destruct (Frame.stk_split rsegs m' (g_S g - 65536) (g_S g - 384) (g_S g) STK1 ltac:(lia)) as [X _];
        exact (proj2 (Frame.stk_split rsegs m' (g_S g - 65536) (g_S g - 16384) (g_S g - 384) X ltac:(lia))) ].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 MF2 HRO2 HDEC HN.
    unfold put_dec_c.PUT_DEC_FRAME, dec_len in *. rewrite ?Li in *.
    retpc.
    pose proof MF2 as (MU2 & WM2 & _).
    lazymatch type of MU2 with Frame.munch ?W2 _ _ =>
      assert (MUa : Frame.munch (WU S0 ++ W2) (normalize rsegs mem) m2)
        by (apply (Frame.munch_trans _ _ m' m2);
            [ apply (Frame.munch_weaken (WU S0)); [intros x Hx; unfold WU in *; cbn [app outside] in *; tauto | exact MU1]
            | apply (Frame.munch_weaken W2); [intros x Hx; unfold WU in *; cbn [app outside] in *; tauto | exact MU2] ]);
      assert (FW : Forall (fun iv => g_S g - 65536 <= fst iv /\ snd iv <= g_S g - 104) (WU S0 ++ W2))
        by (unfold WU, S0; cbn [app]; repeat (apply Forall_cons; [cbn [fst snd]; split; lia|]); apply Forall_nil)
    end.
    pose proof (mfr_bytes _ _ _ _ _ MF2 HQ24 ltac:(rewrite length_le8; cbn; unfold S0 in *; lia)) as HQ24'.
    apply (fin_l g mem regs _ _ _ _ _ m2 (munch_SWIN g _ _ _ MUa FW) (Frame.wmono_trans _ _ _ _ WM1 WM2)
      (mfr_stk _ _ _ _ _ MF2 STK1)); [first [reflexivity | exact E2 | rewrite E2; reflexivity] | reflexivity | reflexivity |].
    intros R' m'' HG HREL. cbv beta.
    assert (KMm : KM _ mem m'') by exact (KM_of _ mem m2 m'' HRO MUa HREL).
    assert (HO' : OUTS g nm tk dp m'')
      by exact (OUTS_keep B APIf ra empty FF g _ nm tk dp L A regs mem md m2 m'' HFR HPM (munch_SWIN g _ _ _ MUa FW)
        HREL HOU).
    unfold NB, STP, IDb, q64, spk. rewrite ?HFS.
    split; [|split; [|split; [|split; [|split]]]].
    + split; [apply KMm; [rewrite rec_id_length; unfold RcIdentModel.ID_SIZE; unfold WU; cbn; unfold S0 in *; lia | exact HID]|].
      split; [exact Wk|]. split; [kr HG|].
      split; [kr HG|]. split; [kr HG|]. split; [kr HG|]. split; [kr HG|]. split; [kr HG|].
      split; [rewrite HG; greg2; reflexivity|]. split; [kr HG|].
      split; [apply KMm; [rewrite length_le8; unfold WU; cbn; unfold S0 in *; lia | exact HQ56]|].
      split; [apply KMm; [rewrite length_le8; unfold WU; cbn; unfold S0 in *; lia | exact HQ48]|].
      exact HO'.
    + rewrite HG. greg2. reflexivity.
    + rewrite HG. greg2. f_equal. all: unfold S0; lia.
    + split.
      * apply (fin_bytes m'' m2 _ _ HREL). exact HQ24'.
      * apply KMm; [|exact HCS]. rewrite length_app. cbn [length]. unfold WU. cbn.
        destruct HSP as [(HA & HL) | (HA1 & HA2 & HL)]; unfold zlen in HL; [rewrite HA|];
          unfold S0 in *; lia.
    + apply (fin_bytes m'' m2 _ _ HREL). eapply bytes_at_ext; [exact HN|]. f_equal. all: f_equal. all: lia.
    + apply (fin_bytes m'' m2 _ _ HREL). replace (S0 + 192) with (S0 + 192 + 0) by lia. exact HDEC.
Qed.

End H01.
