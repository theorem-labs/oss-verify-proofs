(* Segment G03 of fuzz_ctrl LLVMFuzzerTestOneInput (plain): [0x138f4, 0x1390c], K138f4 -> K13910 (not sum_ok:
   bcmp(sp+192, sp+82, 72) = 0, since not FR(Φ, len) leaves FG_j unchanged); K13914 (sum_ok). rf is 0 or 1, so
   0x138f4 is not taken (P4g).
   libreac v1.9.0 (table 5a S_G03, CHANGED: register): sum_ok is s1 (0x138fc `bnez s1`; v1.8 s0), pcs + 0xc, frag
   sp+82 / before sp+192 (v1.8 66 / 176), the frame 1936 bytes. rule 24: no function proved. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import SlotModel SlotInv RcFrag bcmp_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog.Seg Require Import Tac_slot Tac_b5.
Import ListNotations.
Open Scope Z_scope.

Lemma g03_memcmp : forall l n, (n <= length l)%nat -> StrFun.memcmp_model l l n = Some 0.
Proof.
  induction l as [|x l IH]; intros [|n] Hn; cbn in *; try reflexivity; try lia.
  rewrite Z.eqb_refl. apply IH. lia.
Qed.

Lemma g03_rf : forall inp j, t_rf inp j = 0 \/ t_rf inp j = 1.
Proof.
  intros inp j. unfold t_rf, fg_rf. pose proof (b5_nref (t_len inp j) (t_FG inp j) (t_g inp j)) as NR.
  destruct (fcls (t_len inp j) (t_FG inp j) (t_g inp j)); cbn [fg_ret]; auto.
  exfalso. exact (NR eq_refl).
Qed.

(* Not sum_ok: not FR(Φ, len), so the fragment call keeps FG_j and returns 0 (FRAG C1.3). *)
Lemma g03_fr_false : forall len g, (50 <=? len) && (RcModel.blocksum (skipn 18 g) =? 0) = false ->
  fg_fr len g = false.
Proof.
  intros len g H. apply andb_false_iff in H. unfold fg_fr.
  destruct H as [H | H]; rewrite H; [rewrite !andb_false_l; reflexivity | apply andb_false_r].
Qed.

Lemma g03_fcls_none : forall len st g, fg_fr len g = false -> fcls len st g = FgNone.
Proof. intros len st g H. unfold fcls, fg_class. rewrite H. reflexivity. Qed.

Lemma g03_nsok : forall inp j, t_sum_ok inp j = false -> t_FGf inp j = t_FG inp j /\ t_rf inp j = 0.
Proof.
  intros inp j H. pose proof (g03_fr_false (t_len inp j) (t_g inp j) H) as Hf.
  unfold t_FGf, t_rf, fg_st, fg_rf. rewrite (g03_fcls_none _ (t_FG inp j) _ Hf). split; reflexivity.
Qed.

(* s0, s1, s2-s7, s9-s11 kept (s8 = rf is written at 0x138f8). *)
Definition SKP8 (regs regs' : bvmap 5 word) : Prop :=
  YK11.getr regs' 8 = YK11.getr regs 8 /\ YK11.getr regs' 9 = YK11.getr regs 9 /\
  YK11.getr regs' 18 = YK11.getr regs 18 /\ YK11.getr regs' 19 = YK11.getr regs 19 /\
  YK11.getr regs' 20 = YK11.getr regs 20 /\ YK11.getr regs' 21 = YK11.getr regs 21 /\
  YK11.getr regs' 22 = YK11.getr regs 22 /\ YK11.getr regs' 23 = YK11.getr regs 23 /\
  YK11.getr regs' 25 = YK11.getr regs 25 /\ YK11.getr regs' 26 = YK11.getr regs 26 /\
  YK11.getr regs' 27 = YK11.getr regs 27.

Lemma g03_FB_keep : forall g j phi regs regs' mem m', FB g j phi regs mem -> SKP8 regs regs' ->
  Frame.munch [] mem m' -> FB g j phi regs' m'.
Proof.
  intros g j phi regs regs' mem m'
    ((Hj & H26 & (H27 & H32 & H20) & H21 & Hphi & HOUR & HM7) & (H23 & H25 & H9 & H18 & (H8 & H22 & H24 & HB)))
    (E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E25 & E26 & E27) MU.
  split.
  - split; [exact Hj|]. split; [exact (b5_rg _ _ _ _ E26 H26)|].
    split; [split; [exact (b5_rg _ _ _ _ E27 H27) |
                    split; [exact (b5_q64 [] mem m' _ _ H32 MU I) | exact (b5_rg _ _ _ _ E20 H20)]]|].
    split; [exact (b5_rg _ _ _ _ E21 H21)|].
    split; [exact (b5_phi_keep g j phi mem m' [] Hphi MU I)|].
    split.
    + unfold OURb in *. exact (b5_ba [] mem m' _ _ HOUR MU I).
    + unfold M7 in *. exact (b5_q64 [] mem m' _ _ HM7 MU I).
  - split; [exact (b5_rg _ _ _ _ E23 H23)|]. split; [exact (b5_rg _ _ _ _ E25 H25)|].
    split; [exact (b5_rg _ _ _ _ E9 H9)|]. split; [exact (b5_rg _ _ _ _ E18 H18)|].
    split; [exact (b5_rg _ _ _ _ E8 H8)|]. split; [exact (b5_rg _ _ _ _ E22 H22)|].
    split; [exact (b5_q64 [] mem m' _ _ H24 MU I)|].
    exact (b5_ba [] mem m' _ _ HB MU I).
Qed.

Lemma g03_GF_keep : forall g j phi regs regs' mem m', GF g j phi regs mem -> SKP8 regs regs' ->
  Frame.munch [] mem m' -> GF g j phi regs' m'.
Proof.
  intros g j phi regs regs' mem m' (HFB & HI & HG & HS & H192 & Hcl) HK MU.
  split; [exact (g03_FB_keep g j phi regs regs' mem m' HFB HK MU)|].
  split; [exact (b5_IDb_keep g _ mem m' [] (b5_tIDr_len _ _) HI MU I)|].
  split; [exact (b5_FGb_keep g _ mem m' [] (b5_tFGf_len _ _) HG MU I)|].
  split; [exact (b5_FSb_keep g _ _ regs regs' mem m' [] HS (proj1 (proj2 (proj2 (proj2 HK)))) MU I I)|].
  split; [exact (b5_ba [] mem m' _ _ H192 MU I)|].
  intros Hr. destruct (Hcl Hr) as (C1 & C2 & C3). unfold u16, q64 in *.
  split; [exact (b5_ba [] mem m' _ _ C1 MU I)|].
  split; [exact (b5_ba [] mem m' _ _ C2 MU I) | exact (b5_ba [] mem m' _ _ C3 MU I)].
Qed.

Lemma g03_evt : bcmp_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv rf : Z) (sok : bool) (st : list byte),
    sp = Z_to_bv 64 spv -> a0 = Z_to_bv 64 rf -> s1 = Z_to_bv 64 (b2z sok) -> rf = 0 \/ rf = 1 ->
    0 <= spv -> spv + 1936 <= 2 ^ 64 -> mem_inv rsegs m -> length st = 72%nat ->
    (sok = false -> bytes_at rsegs m (spv + 192) st /\ bytes_at rsegs m (spv + 82) st) ->
    evt rsegs
      (fun ms' =>
         (sok = false /\
          exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
            ms' = MS (mkR (Z_to_bv 64 0x13910) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7'
                          s2 s3 s4 s5 s6 s7 (Z_to_bv 64 rf) s9 s10 s11 t3' t4' t5' t6')
                     F (Z_to_bv 64 0x13910) fc None m' (seg_rom rsegs) /\
            munch [] m m' /\ wmono rsegs m m') \/
         (sok = true /\ exists a0' : word,
            ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 (Z_to_bv 64 rf) s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x13914) fc None m (seg_rom rsegs)))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x138f4) fc None m (seg_rom rsegs)).
Proof.
  intros BC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv rf sok st Hsp Ha0 Hs1 Hrf Hlo Hhi MI Hst Hb.
  subst sp a0 s1.
  destruct Hrf as [-> | ->]; destruct sok; step; b5_br false; step; step.
  1,3: b5_br true; apply evt_done; right; split; [reflexivity|]; eexists; reflexivity.
  all: b5_br false; destruct (Hb eq_refl) as (H192 & H82); step; step; step; step;
    (eapply evt_cut;
     [ eapply BC with (ls := st) (rs := st) (v := 0);
       [ b5_ul; exact H192 | b5_ul; exact H82 | b5_ul; apply g03_memcmp; rewrite Hst; lia | exact MI ]
     | ]);
    intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                E & MUc & WMc & _ & _ & _);
    subst ms';
    replace (ret_pc (Z_to_bv 64 0x13910)) with (Z_to_bv 64 0x13910)
      by (symmetry; apply ret_pc_even; [lia | reflexivity]);
    apply evt_done; left; split; [reflexivity|];
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m';
    split; [reflexivity|]; split; [exact MUc | exact WMc].
Qed.

Section G03.
Context {fx : FPState} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis BC : bcmp_contract.

Lemma seg_G03 : forall j, Hat B APIf ra (Inv_K13910_at B APIf ra empty) j ->
  Hat B APIf ra (Inv_K13914_at B APIf ra empty) j -> Hat B APIf ra (Inv_K138f4_at B APIf ra empty) j.
Proof.
  intros j H4 H8 g c (phi & L & A & regs & mem & md & -> & HFR & HP & HGF & H10).
  destruct (sl_fr_bnd B APIf ra empty FF _ _ _ _ _ _ _ HFR) as (Hsp & H16 & HSK & HS47 & HMI).
  pose proof HGF as (HFB & _ & HG & _ & H192 & _).
  pose proof HFB as (_ & (_ & _ & H9r & _)).
  unfold SLOT_K, SLOT_STACK, SL_TOP, fsp, SLOT_FRAME in *.
  eapply (b5_mid B APIf ra empty FF g _ L A regs mem md _ []);
    [exact HFR | exact HP | intros x Hx O; exfalso; apply O; exact I | | |].
  - rewrite sl_mkR_of.
    apply (g03_evt BC) with (spv := g_S g - 1936) (rf := t_rf (g_in g) j) (sok := t_sum_ok (g_in g) j)
      (st := t_FG (g_in g) j);
      [exact Hsp | exact H10 | exact H9r | apply g03_rf | lia | lia | exact (mem_inv_normalize rsegs mem)
      | apply b5_tFG_len | ].
    intros Hs. destruct (g03_nsok _ _ Hs) as (EF & _). split.
    + unfold spk, fsp, SLOT_FRAME in H192. exact (bytes_at_normalize rsegs mem _ _ HMI H192).
    + pose proof (proj1 HG) as HGb. unfold FGB, spk, fsp, SLOT_FRAME in HGb. rewrite EF in HGb.
      exact (bytes_at_normalize rsegs mem _ _ HMI HGb).
  - intros ms [(_ & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m' & -> & MU & WM) | (_ & ? & ->)].
    + do 3 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|].
      split; [reflexivity|]. split; reflexivity.
    + do 3 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl|].
      split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ Hx Hrel MU' HFR'.
    destruct HQ as [(Hs & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & m'' & HE & _ & _) | (Hs & ? & HE)];
      injection HE; intros; subst;
      (assert (HK8 : SKP8 regs regs') by (repeat split; rewrite (sl_getr_eqv _ _ _ Hx); reflexivity));
      pose proof (g03_GF_keep g j phi regs regs' mem m' HGF HK8 MU') as HGF'.
    + apply H4. exists phi, L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      split; [exact HGF'|]. split; [unfold rg; rewrite (sl_getr_eqv _ _ _ Hx); reflexivity|].
      split; [exact Hs|]. unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
    + apply H8. exists phi, L, A, regs', m', md.
      split; [reflexivity|]. split; [exact HFR'|]. split; [exact HP|].
      split; [exact HGF'|]. unfold rg. rewrite (sl_getr_eqv _ _ _ Hx). reflexivity.
Qed.

End G03.
