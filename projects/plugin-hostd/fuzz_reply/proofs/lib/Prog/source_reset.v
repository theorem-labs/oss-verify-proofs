From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import memset_c.
Import ListNotations.
Open Scope Z_scope.

Lemma sr_seg1 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp -> 0x100000 <= lo -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m',
      ms' = MS (mkR (Z_to_bv 64 0x14614) (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 a0 s1
                    (Z_to_bv 64 (bv_unsigned a0 + 16)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x14b6c) fc None m' (seg_rom rsegs) /\
      munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      rw_cells rsegs m' (bv_unsigned sp + -16) [C8 s0; C8 ra] /\ stk rsegs m' lo (bv_unsigned sp + -16))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x145fc) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    ST LO HI MI.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 16%nat ST.
  do 6 step.
  apply evt_done. eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; eassumption.
Qed.

Lemma sr_seg2 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (k pc' : Z),
  (k = 64 /\ pc' = 0x1461c \/ k = 80 /\ pc' = 0x14624) ->
  evt rsegs (fun ms' => exists a0',
      ms' = MS (mkR (Z_to_bv 64 pc') sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x14b6c) fc None m (seg_rom rsegs) /\ a0' = Z_to_bv 64 (bv_unsigned s0 + k))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 (pc' - 8)) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m k pc'
    [(-> & ->)|(-> & ->)]; cbn [Z.sub].
  - do 2 step. apply evt_done. eexists. split; reflexivity.
  - do 2 step. apply evt_done. eexists. split; reflexivity.
Qed.

Lemma sr_seg4 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (w : word),
  0 <= bv_unsigned s0 + 40 -> bv_unsigned s0 + 48 <= 2 ^ 64 ->
  rw_cells rsegs m (bv_unsigned s0 + 40) [C8 w] ->
  evt rsegs (fun ms' =>
      ms' = MS (mkR (Z_to_bv 64 0x1462c) sp gp tp t0 t1 t2 s0 s1 w a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x15664) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14624) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m w
    H1 H2 B.
  do 2 step. apply evt_done. reflexivity.
Qed.

Lemma sr_tail : memset_contract ->
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (B : Z) (s0v rav : word) (junk : list byte),
  sp = Z_to_bv 64 B -> 0 <= B -> B + 16 < 2 ^ 64 -> mem_inv rsegs m ->
  rw_cells rsegs m B [C8 s0v; C8 rav] ->
  rw_cells rsegs m (bv_unsigned s0) [CB 96 junk] ->
  evt rsegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR rav (Z_to_bv 64 (B + 16)) gp tp t0' t1' t2' s0v s1 s0 a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc rav) fc None m' (seg_rom rsegs) /\
      munch [(bv_unsigned s0, bv_unsigned s0 + 96)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
      rw_cells rsegs m' (bv_unsigned s0) [CB 96 (repeat (Z_to_bv 8 0) 96)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1462c) fc None m (seg_rom rsegs)).
Proof.
  intros MS0 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    B s0v rav junk -> HB0 HB1 MI FR SL.
  do 7 step.
  eapply evt_cut.
  { eapply MS0 with (junk := junk); [|exact MI].
    rewrite (unsigned_lit 96) by lia. exact SL. }
  intros ms' (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m' & -> & MU & WM & MI' & RW).
  rewrite (unsigned_lit 96), (unsigned_lit 0) in * by lia.
  apply evt_done. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. exact RW.
Qed.

From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK14 YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Contract ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import RelayFrame RelayRunT RelayRunF HarnessRep ListRep
  CheckRep ListTr HarnessTr TrModel list_free_c source_reset_c KindB HarnessGlue HarnessFrame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.

Definition sr_S (lp le lh : hlist) (pv : Z) : list Z :=
  list_blocks lp ++ (if pv =? 0 then [] else [pv]) ++ list_blocks le ++ list_blocks lh.

Definition sr_tr (nm : Z -> tad) (lp le lh : hlist) (pv : Z) : list tev :=
  hlist_free_tr nm lp ++ hlist_free_tr nm le ++ hlist_free_tr nm lh ++ (if pv =? 0 then [] else [RFree 6000 (nm pv)]).

Lemma runF_app0 : forall F qs b t1 t2, nretF t1 = 0%nat -> runF F qs b (t1 ++ t2) = runF F qs (runF F qs b t1) t2.
Proof. intros F qs b t1 t2 H. unfold runF, run_tr. rewrite run_from_app, H. reflexivity. Qed.

Lemma nret_hlist_free : forall nm l, nretF (hlist_free_tr nm l) = 0%nat.
Proof. intros nm l. unfold hlist_free_tr. apply nret_list_free. Qed.

Lemma hlist_free_tr_ext : forall nm1 nm2 l, (forall a, In a (list_blocks l) -> nm1 a = nm2 a) ->
  hlist_free_tr nm1 l = hlist_free_tr nm2 l.
Proof.
  intros nm1 nm2 l H. unfold hlist_free_tr, list_free_tr, sh_of. cbn [sh_recs sh_cap sh_v]. f_equal.
  - unfold recs_drop_tr. rewrite <- !map_rev, !map_map. f_equal. apply map_ext_in. intros r Hr.
    unfold shr. rewrite (H (fst r)); [reflexivity|]. unfold list_blocks. apply in_or_app. right.
    apply in_map. apply in_rev. exact Hr.
  - destruct (hl_cap l =? 0) eqn:E; [reflexivity|]. rewrite (H (hl_v l)); [reflexivity|].
    unfold list_blocks. rewrite E. left. reflexivity.
Qed.

Section SRB.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Variable RF : ResFormT.
Hypothesis AX : AllocExtra Bm (aa_MR API).
Hypothesis CTX : ctx_owned Bm API.
Hypothesis BW : blocks_writable Bm API.
Hypothesis HFREE : ms_free Bm = 0x15664.
Hypothesis HERRB : errno_addr Bm + 4 <= alloc_ceiling.
Hypothesis NODUP : forall L A mem md, aa_MR API L A mem md -> NoDup (map fst (blocks L A)).

Lemma sr_sptr_keep : forall K sp E F L A mem md L' A' mem' md' a n,
  rmid Bm API K sp E F L A mem md L' A' mem' md' ->
  NoDup (map fst (blocks L A)) -> NoDup (map fst (blocks L' A')) ->
  In (a, n) (blocks L A) -> 0 < n -> ~ F a -> sptr_of L' A' a = sptr_of L A a.
Proof.
  intros K sp E F L A mem md L' A' mem' md' a n (_ & _ & _ & _ & _ & PA & SV & _) N N' Hin Hn HF.
  destruct (sptr_of_spec L A a n N Hin) as (Hp & Ha).
  assert (HF' : ~ F (ptr_addr L (sptr_of L A a))) by (rewrite Ha; exact HF).
  pose proof (SV _ _ Hp Hn HF') as Hp'.
  pose proof (PA _ _ Hp Hp' HF') as Ea.
  rewrite <- Ha at 1. rewrite <- Ea. exact (sptr_of_eq L' A' _ n N' Hp').
Qed.

Lemma sr_hi : forall K sp E F L A mem md L' A' mem' md' a cs,
  ms_segs Bm = rsegs -> alloc_ceiling <= sp -> aa_MR API L A mem md ->
  rmid Bm API K sp E F L A mem md L' A' mem' md' -> rw_cells rsegs mem a cs -> sp <= a ->
  a + Z.of_nat (cells_size cs) <= 2 ^ 64 -> (forall j, 0 <= j < Z.of_nat (cells_size cs) -> ~ E (a + j)) ->
  rw_cells rsegs mem' a cs.
Proof.
  intros K sp E F L A mem md L' A' mem' md' a cs SEG H1 HM R H Ha Hb D.
  rewrite <- SEG in H |- *. exact (rmid_rw_hi Bm API K sp E F L A mem md L' A' mem' md' a cs H1 ltac:(lia) HM R H Ha Hb D).
Qed.

Lemma sr_img : forall K sp E F L A mem md L' A' mem' md' a cs,
  ms_segs Bm = rsegs -> alloc_ceiling <= sp - K -> aa_MR API L A mem md ->
  rmid Bm API K sp E F L A mem md L' A' mem' md' -> rw_cells rsegs mem a cs ->
  (forall j, 0 <= j < Z.of_nat (cells_size cs) -> img_plain Bm (a + j) /\ ~ E (a + j)) ->
  rw_cells rsegs mem' a cs.
Proof.
  intros K sp E F L A mem md L' A' mem' md' a cs SEG H1 HM R H D.
  rewrite <- SEG in H |- *.
  exact (rmid_rw_img Bm API AX K sp E F L A mem md L' A' mem' md' a cs (hg_img_low Bm SEG) H1 HM R H D).
Qed.

Lemma sr_chain : list_free_contract Bm API RF -> free_contract_rt Bm API RF -> free_null_contract Bm -> memset_contract ->
  forall L A regs mem md (bnd : rt_R RF) (lp le lh : hlist) (pv : Z) (w0 w1 w2 w3 w4 w5 w6 : word)
    (pad : list byte) (j : nat),
  let HA := G_S + SRC_SIZE * Z.of_nat j in
  ms_segs Bm = rsegs ->
  call_pre_k Bm (aa_MR API) SOURCE_RESET_K L A regs mem md ->
  st_init_done A = true -> ro_agree rsegs mem ->
  (forall a, G_S <= a < G_S + SRC_SIZE * SOURCES_MAX -> img_plain Bm a) -> (j < 4)%nat ->
  PropExec.getr regs 10 = Z_to_bv 64 HA ->
  rw_cells rsegs mem HA [C4 w0; C4 w1; C4 w2; C4 w3] ->
  list_at Bm L A mem (HA + 16) lp false ->
  rw_cells rsegs mem (HA + 32) [C8 w4; C8 (Z_to_bv 64 pv); C8 w5; C4 w6] ->
  rw_cells rsegs mem (HA + 60) [CB 4 pad] ->
  list_at Bm L A mem (HA + 64) le true -> list_at Bm L A mem (HA + 80) lh true ->
  List.NoDup (sr_S lp le lh pv) ->
  (pv = 0 \/ In (pv, 6000) (blocks L A)) ->
  rt_ok RF A bnd ->
  SR rsegs (mkCfg (YK11.mkst regs (Z_to_bv 64 SOURCE_RESET) mem (seg_rom rsegs)) md)
    (fun c' => exists L' A' regs' mem' md',
       c' = mkCfg (YK11.mkst regs' (PropExec.getr regs 1) mem' (seg_rom rsegs)) md' /\
       relay_post Bm API SOURCE_RESET_K (fun a => HA <= a < HA + SRC_SIZE) (fun q => In q (sr_S lp le lh pv))
         L A regs mem md L' A' regs' mem' md' /\
       st_init_done A' = true /\ ro_agree rsegs mem' /\
       rw_cells rsegs mem' HA [CB 96%nat (nulbytes 96)] /\
       rt_ok RF A' (runF RF [] bnd (sr_tr (known_at L A) lp le lh pv)) /\
       (forall q m, In (q, m) (blocks L A) -> ~ In q (sr_S lp le lh pv) -> In (q, m) (blocks L' A')) /\
       (forall q m, In (q, m) (blocks L' A') -> In (q, m) (blocks L A) /\ ~ In q (sr_S lp le lh pv)) /\
       (sr_S lp le lh pv = [] -> blocks L' A' = blocks L A)).
Proof.
  intros LF FRc FN MSC L A regs mem md bnd lp le lh pv w0 w1 w2 w3 w4 w5 w6 pad j HA.
  intros SEG PRE INIT RO PLR Hj4 R10 C0 LP C32 PAD LE LH NDS PVC RES.
  pose proof (aa_laws API) as LAWS.
  pose proof (@YM05.alloc_ceiling_value rc) as ACV. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  pose proof PRE as (HMR & HWF & HBD & HRA & HAL & HCEIL & H63 & HWS & HTP & HERR & HAUX).
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  assert (EK : SOURCE_RESET_K = 8240) by reflexivity. rewrite EK in *.
  set (sp := reg_get regs 2) in *.
  assert (SPE : spZ regs = bv_unsigned sp) by reflexivity. rewrite SPE in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. change (bv_modulus 64) with (2 ^ 64) in RSP.
  assert (HAr : 200768 <= HA <= 201056) by (unfold HA, G_S, SRC_SIZE; lia).
  assert (PLR' : forall a, HA <= a < HA + 96 -> img_plain Bm a)
    by (intros a Ha; apply PLR; unfold HA, G_S, SRC_SIZE, SOURCES_MAX in *; lia).
  assert (A0 : bv_unsigned (reg_get regs 10) = HA).
  { transitivity (bv_unsigned (PropExec.getr regs 10)); [reflexivity|]. rewrite R10. apply unsigned_lit. lia. }
  assert (R10' : reg_get regs 10 = Z_to_bv 64 HA) by exact R10.
  rewrite SEG in HWS, HERR.
  assert (ST : stk rsegs mem (bv_unsigned sp - 8240) (bv_unsigned sp)).
  { split; [lia|]. split; [lia|]. intros a Ha. assert (W : writable_at rsegs mem a) by (apply HWS; lia).
    split; [exact W|]. destruct (writable_hi_present mem a ltac:(lia) W) as [bb E]. exists bb.
    unfold mrd, wa. rewrite E. reflexivity. }
  pose proof (stk_normalize mem _ _ ST ltac:(lia)) as ST0.
  pose proof (mem_inv_normalize rsegs mem) as MI0.
  assert (WX : wx_apart rsegs = true) by (vm_compute; reflexivity).
  assert (HK0 : alloc_ceiling <= bv_unsigned sp - 8240) by lia.
  unfold SOURCE_RESET.
  eapply (kseg regs (Z_to_bv 64 0x145fc) mem md); [exact WX | exact RO | exact Hh | exact Hl | | |].
  { unfold Regs6ss.mkR_of. fold sp.
    eapply sr_seg1 with (lo := bv_unsigned sp - 8240); [exact ST0 | lia | lia | exact MI0]. }
  { intros s0 (m' & -> & _). do 3 eexists. reflexivity. }
  intros R pc' m0' regs1 m1 HQ GR1 MREL1 ROS1.
  destruct HQ as (m1n & EQ & MU & WM & MI & FR & STK).
  injection EQ as ER EP EM. subst R pc' m0'.
  destruct (rmid_norm Bm API 8240 (bv_unsigned sp) (fun _ => False) (fun _ => False) L A mem md m1n m1
              [(bv_unsigned sp - 16, bv_unsigned sp)] SEG RO MREL1 ROS1 MU WM HMR HWF HBD HK0)
    as (RM0 & MU0 & WM0).
  { unfold sk. rewrite SEG. intros a [X|X]; [apply HWS; lia | apply HERR; exact X]. }
  { intros x Hx O. destruct (hg_not_out _ _ O) as (lo & hi & [E|[]] & Hlh). injection E as <- <-. left. lia. }
  { intros a Ho. pose proof (mr_owned_low _ _ LAWS _ _ _ _ a HMR Ho). apply hg_out. intros lo hi [E|[]].
    injection E as <- <-. left. lia. }
  { intros p n i Hp Hi O. exfalso. destruct (mr_blocks _ _ LAWS _ _ _ _ p n i HMR Hp Hi) as (_ & B1 & B2 & _).
    destruct (hg_not_out _ _ O) as (lo & hi & [E|[]] & Hlh). injection E as <- <-. lia. }
  pose proof (ro_agree_same rsegs mem m1 RO ROS1) as RO1.
  pose proof (rw_cells_of_rel rsegs m1 m1n _ _ MREL1 FR) as FR1.
  pose proof RM0 as (HM1 & HWF1 & HBD1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC1).
  assert (E1_1 : getr regs1 1 = Z_to_bv 64 0x14614) by (rewrite GR1; reflexivity).
  assert (E1_2 : getr regs1 2 = Z_to_bv 64 (bv_unsigned sp + -16)) by (rewrite GR1; reflexivity).
  assert (E1_4 : getr regs1 4 = getr regs 4) by (rewrite GR1; reflexivity).
  assert (E1_8 : getr regs1 8 = Z_to_bv 64 HA) by (rewrite GR1; exact R10').
  assert (E1_10 : PropExec.getr regs1 10 = Z_to_bv 64 (HA + 16)).
  { change (PropExec.getr regs1 10) with (getr regs1 10). rewrite GR1.
    transitivity (Z_to_bv 64 (bv_unsigned (reg_get regs 10) + 16)); [reflexivity | rewrite A0; reflexivity]. }
  assert (KEEP1 : forall r, (r = 3 \/ r = 4 \/ r = 9 \/ 18 <= r <= 27) ->
            getr regs1 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr. rewrite GR1.
    assert (Hc : r = 3 \/ r = 4 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                 r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    repeat (destruct Hc as [Hc|Hc]; [subst r; reflexivity|]); subst r; reflexivity. }
  assert (SP1 : spZ regs1 = bv_unsigned sp - 16) by (unfold spZ; rewrite E1_2; apply unsigned_lit; lia).
  pose proof LF as LFc. unfold list_free_contract in LFc. rewrite SEG in LFc.
  assert (EKL : LIST_FREE_K = 8224) by reflexivity. rewrite EKL in LFc. unfold LIST_FREE in LFc.
  assert (LAu1 : bv_unsigned (Z_to_bv 64 (HA + 16)) = HA + 16) by (apply unsigned_lit; lia).
  assert (KF0 : forall q, kept_block (fun _ => False) (fun _ => False) L A q)
    by (intros q; split; [intros [] | intros k i _ _ []]).
  assert (LP1 : list_at Bm L A m1 (HA + 16) lp false).
  { apply (list_at_rmid Bm API AX BW 8240 (bv_unsigned sp) _ _ L A mem md L A m1 md _ _ _ SEG HK0 HMR RM0 LP).
    - intros i Hi. split; [apply PLR'; lia | intros []].
    - intros q _. apply KF0. }
  eapply SR_bind.
  { apply (LFc L A regs1 m1 md bnd lp false).
    - reflexivity.
    - eapply cpk_of_rmid; [exact RM0 | exact INIT | rewrite E1_1; apply ret_ok_even; vm_compute; reflexivity
                           | rewrite E1_4; exact HTP | rewrite SP1, Zminus_mod, HAL; reflexivity | rewrite SP1; lia
                           | rewrite SP1; lia | lia | rewrite SP1; lia | rewrite SP1; lia].
    - exact INIT.
    - exact RO1.
    - rewrite E1_10, LAu1. intros a Ha. split; [apply PLR'; lia | apply hf_ro_glob; lia].
    - rewrite E1_10, LAu1. exact LP1.
    - exact RES. }
  intros c2 (L1 & A1 & regs2 & m2 & md1 & -> & RP1 & INIT1 & (qs1 & LQ1 & RES1) & RO2 & LP2 & ZB1 & B1a & B1b).
  rewrite nret_list_free in LQ1. apply length_zero_iff_nil in LQ1. subst qs1.
  rewrite E1_10, LAu1 in RP1, LP2.
  destruct (rp_split Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ RP1) as (RM1 & PR1). rewrite SP1 in RM1.
  assert (NDS1 : List.NoDup ((if pv =? 0 then [] else [pv]) ++ list_blocks le ++ list_blocks lh))
    by exact (NoDup_app_remove_l _ _ NDS).
  assert (NDS2 : List.NoDup (list_blocks le ++ list_blocks lh)) by exact (NoDup_app_remove_l _ _ NDS1).
  assert (D1 : forall q, In q ((if pv =? 0 then [] else [pv]) ++ list_blocks le ++ list_blocks lh) ->
               ~ In q (list_blocks lp)) by (intros q Hq Hp; exact (hf_nodup_disj _ _ q NDS Hp Hq)).
  assert (D2 : forall q, In q ((if pv =? 0 then [] else [pv]) ++ list_blocks lh) -> ~ In q (list_blocks le)).
  { intros q Hq Hp. apply in_app_iff in Hq as [Hq|Hq].
    - exact (hf_nodup_disj _ _ q NDS1 Hq (in_or_app _ _ _ (or_introl Hp))).
    - exact (hf_nodup_disj _ _ q NDS2 Hp Hq). }
  assert (D3 : forall q, In q (if pv =? 0 then [] else [pv]) -> ~ In q (list_blocks lh)).
  { intros q Hq Hp. exact (hf_nodup_disj _ _ q NDS1 Hq (in_or_app _ _ _ (or_intror Hp))). }
  assert (LE1 : list_at Bm L A m1 (HA + 64) le true).
  { apply (list_at_rmid Bm API AX BW 8240 (bv_unsigned sp) _ _ L A mem md L A m1 md _ _ _ SEG HK0 HMR RM0 LE).
    - intros i Hi. split; [apply PLR'; lia | intros []].
    - intros q _. apply KF0. }
  assert (LH1 : list_at Bm L A m1 (HA + 80) lh true).
  { apply (list_at_rmid Bm API AX BW 8240 (bv_unsigned sp) _ _ L A mem md L A m1 md _ _ _ SEG HK0 HMR RM0 LH).
    - intros i Hi. split; [apply PLR'; lia | intros []].
    - intros q _. apply KF0. }
  assert (IMG1 : forall a cs, rw_cells rsegs mem a cs -> HA <= a -> a + Z.of_nat (cells_size cs) <= HA + 96 ->
                 rw_cells rsegs m1 a cs).
  { intros a cs H Ha Hb. apply (sr_img 8240 (bv_unsigned sp) _ _ L A mem md L A m1 md a cs SEG HK0 HMR RM0 H).
    intros i Hi. split; [apply PLR'; lia | intros []]. }
  pose proof (IMG1 _ _ C0 ltac:(lia) ltac:(cbn; lia)) as C0_1.
  pose proof (IMG1 _ _ C32 ltac:(lia) ltac:(cbn; lia)) as C32_1.
  pose proof (IMG1 _ _ PAD ltac:(lia) ltac:(cbn; lia)) as PAD_1.
  pose proof RM1 as (HM2 & HWF2 & HBD2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC2).
  assert (EP1 : forall a, (fun a => HA + 16 <= a < HA + 16 + 16) a -> (HA + 16 <= a < HA + 32) \/
                  (0 < 0 /\ 0 <= a < 0 + 16 * 0)) by (intros a X; left; cbv beta in X; lia).
  assert (KP1 : forall q, ~ In q (list_blocks lp) ->
                kept_block (fun a => HA + 16 <= a < HA + 16 + 16) (fun q => In q (list_blocks lp)) L A q).
  { intros q Hq. apply (hf_kept Bm API AX L A m1 md _ _ (HA + 16) (HA + 32) 0 0 q HM1);
      [intros a Ha; exact (proj1 (PLR' a ltac:(lia))) | exact EP1 | intros X; lia | exact Hq | intros X; lia]. }
  assert (LE2 : list_at Bm L1 A1 m2 (HA + 64) le true).
  { apply (list_at_rmid Bm API AX BW 8224 (bv_unsigned sp - 16) _ _ L A m1 md L1 A1 m2 md1 _ _ _ SEG ltac:(lia)
             HM1 RM1 LE1).
    - intros i Hi. split; [apply PLR'; lia | cbv beta; lia].
    - intros q Hq. apply KP1. apply D1. apply in_or_app. right. apply in_or_app. left. exact Hq. }
  assert (LH2 : list_at Bm L1 A1 m2 (HA + 80) lh true).
  { apply (list_at_rmid Bm API AX BW 8224 (bv_unsigned sp - 16) _ _ L A m1 md L1 A1 m2 md1 _ _ _ SEG ltac:(lia)
             HM1 RM1 LH1).
    - intros i Hi. split; [apply PLR'; lia | cbv beta; lia].
    - intros q Hq. apply KP1. apply D1. apply in_or_app. right. apply in_or_app. right. exact Hq. }
  assert (IMG2 : forall a cs, rw_cells rsegs m1 a cs -> (HA <= a /\ a + Z.of_nat (cells_size cs) <= HA + 16 \/
                    HA + 32 <= a /\ a + Z.of_nat (cells_size cs) <= HA + 96) -> rw_cells rsegs m2 a cs).
  { intros a cs H Ha. apply (sr_img 8224 (bv_unsigned sp - 16) _ _ L A m1 md L1 A1 m2 md1 a cs SEG ltac:(lia) HM1 RM1 H).
    intros i Hi. split; [apply PLR'; lia | cbv beta; lia]. }
  pose proof (IMG2 _ _ C0_1 ltac:(cbn; lia)) as C0_2.
  pose proof (IMG2 _ _ C32_1 ltac:(cbn; lia)) as C32_2.
  pose proof (IMG2 _ _ PAD_1 ltac:(cbn; lia)) as PAD_2.
  pose proof (sr_hi 8224 (bv_unsigned sp - 16) _ _ L A m1 md L1 A1 m2 md1 _ _ SEG ltac:(lia) HM1 RM1 FR1
                ltac:(lia) ltac:(cbn; lia) ltac:(intros i Hi X; cbv beta in X; lia)) as FR2.
  assert (PV2 : pv = 0 \/ In (pv, 6000) (blocks L1 A1)).
  { destruct PVC as [X|X]; [left; exact X|]. destruct (Z.eqb_spec pv 0) as [E|E]; [left; exact E|right].
    apply (B1a pv 6000 X). apply D1. apply in_or_app. left.
    destruct (pv =? 0) eqn:EZ; [apply Z.eqb_eq in EZ; exfalso; exact (E EZ) | left; reflexivity]. }
  assert (WR1 : forall a, bv_unsigned sp - 8240 <= a < bv_unsigned sp -> writable_at (ms_segs Bm) m1 a)
    by (intros a Ha; apply SC1; unfold sk; left; exact Ha).
  pose proof (rmid_widen Bm API 8224 (bv_unsigned sp - 16) 8240 (bv_unsigned sp)
                (fun a => HA + 16 <= a < HA + 16 + 16) (fun q => In q (list_blocks lp)) _ _ _ _ _ _ _ _ HM1
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) WR1 ltac:(intros a Ha X; cbv beta in X; lia) RM1) as RM1w.
  pose proof (rmid_seq Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HWF RM0 RM1w) as RM01.
  pose proof RM01 as (HM2' & HWF2' & HBD2' & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC2').
  destruct (mr_model _ _ LAWS _ _ _ _ HM2) as (Hh2 & Hl2 & _).
  assert (E2_2 : getr regs2 2 = Z_to_bv 64 (bv_unsigned sp + -16))
    by exact (eq_trans (PR1 2 ltac:(unfold callee_saved; lia)) E1_2).
  assert (E2_4 : getr regs2 4 = getr regs 4) by exact (eq_trans (PR1 4 ltac:(unfold callee_saved; lia)) E1_4).
  assert (E2_8 : getr regs2 8 = Z_to_bv 64 HA) by exact (eq_trans (PR1 8 ltac:(unfold callee_saved; lia)) E1_8).
  assert (KEEP2 : forall r, (r = 3 \/ r = 4 \/ r = 9 \/ 18 <= r <= 27) ->
            getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr. rewrite (PR1 r ltac:(unfold callee_saved; lia)). exact (KEEP1 r Hr). }
  change (PropExec.getr regs1 1) with (getr regs1 1). rewrite E1_1.
  eapply (kseg regs2 (Z_to_bv 64 0x14614) m2 md1); [exact WX | exact RO2 | exact Hh2 | exact Hl2 | | |].
  { unfold Regs6ss.mkR_of. eapply sr_seg2 with (k := 64) (pc' := 0x1461c). left. split; reflexivity. }
  { intros s0 (a0' & -> & _). do 3 eexists. reflexivity. }
  intros R pc' m0' regs3 m3 HQ GR3 MREL3 ROS3.
  destruct HQ as (a0' & EQ & Ea0). injection EQ as ER EP EM. subst R pc' m0'.
  destruct (rmid_norm Bm API 8240 (bv_unsigned sp) (fun _ => False) (fun _ => False) L1 A1 m2 md1
              (normalize rsegs m2) m3 [] SEG RO2 MREL3 ROS3 (munch_refl _ _) (wmono_refl _ _) HM2' HWF2' HBD2' HK0)
    as (RM2 & MU3 & WM3).
  { exact SC2'. }
  { intros x Hx O. exfalso. exact (O I). }
  { intros a Ho. exact I. }
  { intros p n i Hp Hi O. exfalso. exact (O I). }
  pose proof (rmid_seq Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HWF RM01 RM2) as RM012.
  pose proof RM012 as (HM3 & HWF3 & HBD3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC3).
  pose proof (ro_agree_same rsegs m2 m3 RO2 ROS3) as RO3.
  assert (KF1 : forall q, kept_block (fun _ => False) (fun _ => False) L1 A1 q)
    by (intros q; split; [intros [] | intros k i _ _ []]).
  assert (IMG3 : forall a cs, rw_cells rsegs m2 a cs -> HA <= a -> a + Z.of_nat (cells_size cs) <= HA + 96 ->
                 rw_cells rsegs m3 a cs).
  { intros a cs H Ha Hb. apply (sr_img 8240 (bv_unsigned sp) _ _ L1 A1 m2 md1 L1 A1 m3 md1 a cs SEG HK0 HM2' RM2 H).
    intros i Hi. split; [apply PLR'; lia | intros []]. }
  assert (LT3 : forall LA l lines, list_at Bm L1 A1 m2 LA l lines -> HA <= LA -> LA + 16 <= HA + 96 ->
                list_at Bm L1 A1 m3 LA l lines).
  { intros LA l lines H Ha Hb. apply (list_at_rmid Bm API AX BW 8240 (bv_unsigned sp) _ _ L1 A1 m2 md1 L1 A1 m3 md1
      _ _ _ SEG HK0 HM2' RM2 H); [intros i Hi; split; [apply PLR'; lia | intros []] | intros q _; apply KF1]. }
  pose proof (LT3 _ _ _ LP2 ltac:(lia) ltac:(lia)) as LP3.
  pose proof (LT3 _ _ _ LE2 ltac:(lia) ltac:(lia)) as LE3.
  pose proof (LT3 _ _ _ LH2 ltac:(lia) ltac:(lia)) as LH3.
  pose proof (IMG3 _ _ C0_2 ltac:(lia) ltac:(cbn; lia)) as C0_3.
  pose proof (IMG3 _ _ C32_2 ltac:(lia) ltac:(cbn; lia)) as C32_3.
  pose proof (IMG3 _ _ PAD_2 ltac:(lia) ltac:(cbn; lia)) as PAD_3.
  pose proof (rw_cells_transport rsegs [] m2 m3 _ _ FR2 MU3 WM3 I) as FR3.
  destruct (mr_model _ _ LAWS _ _ _ _ HM3) as (Hh3 & Hl3 & _).
  assert (E3_1 : getr regs3 1 = Z_to_bv 64 0x1461c) by (rewrite GR3; reflexivity).
  assert (E3_2 : getr regs3 2 = Z_to_bv 64 (bv_unsigned sp + -16)) by (rewrite GR3; exact E2_2).
  assert (E3_4 : getr regs3 4 = getr regs 4) by (rewrite GR3; exact E2_4).
  assert (E3_8 : getr regs3 8 = Z_to_bv 64 HA) by (rewrite GR3; exact E2_8).
  assert (E3_10 : PropExec.getr regs3 10 = Z_to_bv 64 (HA + 64)).
  { change (PropExec.getr regs3 10) with (getr regs3 10). rewrite GR3. cbn. rewrite Ea0.
    change (reg_get regs2 8) with (getr regs2 8). rewrite E2_8, unsigned_lit by lia. reflexivity. }
  assert (KEEP3 : forall r, (r = 3 \/ r = 4 \/ r = 9 \/ 18 <= r <= 27) ->
            getr regs3 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr. rewrite <- (KEEP2 r Hr), GR3.
    assert (Hc : r = 3 \/ r = 4 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                 r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    repeat (destruct Hc as [Hc|Hc]; [subst r; reflexivity|]); subst r; reflexivity. }
  assert (SP3 : spZ regs3 = bv_unsigned sp - 16) by (unfold spZ; rewrite E3_2; apply unsigned_lit; lia).
  assert (LAu3 : bv_unsigned (Z_to_bv 64 (HA + 64)) = HA + 64) by (apply unsigned_lit; lia).
  eapply SR_bind.
  { apply (LFc L1 A1 regs3 m3 md1 (runF RF [] bnd (hlist_free_tr (known_at L A) lp)) le true).
    - reflexivity.
    - eapply cpk_of_rmid; [exact RM012 | exact INIT1 | rewrite E3_1; apply ret_ok_even; vm_compute; reflexivity
                           | rewrite E3_4; exact HTP | rewrite SP3, Zminus_mod, HAL; reflexivity | rewrite SP3; lia
                           | rewrite SP3; lia | lia | rewrite SP3; lia | rewrite SP3; lia].
    - exact INIT1.
    - exact RO3.
    - rewrite E3_10, LAu3. intros a Ha. split; [apply PLR'; lia | apply hf_ro_glob; lia].
    - rewrite E3_10, LAu3. exact LE3.
    - exact RES1. }
  intros c4 (L2 & A2 & regs4 & m4 & md2 & -> & RP2 & INIT2 & (qs2 & LQ2 & RES2) & RO4 & LE4 & ZB2 & B2a & B2b).
  rewrite nret_list_free in LQ2. apply length_zero_iff_nil in LQ2. subst qs2.
  rewrite E3_10, LAu3 in RP2, LE4.
  destruct (rp_split Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ RP2) as (RM3 & PR3). rewrite SP3 in RM3.
  pose proof RM3 as (HM4 & HWF4 & HBD4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC4).
  assert (NM2 : hlist_free_tr (known_at L1 A1) le = hlist_free_tr (known_at L A) le).
  { apply hlist_free_tr_ext. intros a Ha. unfold known_at. f_equal.
    destruct (hf_list_pos Bm L A m1 (HA + 64) le true a LE1 Ha) as (k & Hk & Hin).
    apply (sr_sptr_keep _ _ _ _ _ _ _ _ _ _ _ _ a k RM1 (NODUP _ _ _ _ HM1) (NODUP _ _ _ _ HM2) Hin Hk).
    intros X. refine (D1 a _ X). apply in_or_app. right. apply in_or_app. left. exact Ha. }
  change (rt_ok RF A2 (runF RF [] (runF RF [] bnd (hlist_free_tr (known_at L A) lp)) (hlist_free_tr (known_at L1 A1) le)))
    in RES2.
  rewrite NM2 in RES2.
  assert (EP3 : forall a, (fun a => HA + 64 <= a < HA + 64 + 16) a -> (HA + 64 <= a < HA + 80) \/
                  (0 < 0 /\ 0 <= a < 0 + 16 * 0)) by (intros a X; left; cbv beta in X; lia).
  assert (KP3 : forall q, ~ In q (list_blocks le) ->
                kept_block (fun a => HA + 64 <= a < HA + 64 + 16) (fun q => In q (list_blocks le)) L1 A1 q).
  { intros q Hq. apply (hf_kept Bm API AX L1 A1 m3 md1 _ _ (HA + 64) (HA + 80) 0 0 q HM3);
      [intros a Ha; exact (proj1 (PLR' a ltac:(lia))) | exact EP3 | intros X; lia | exact Hq | intros X; lia]. }
  assert (LT4 : forall LA l lines, list_at Bm L1 A1 m3 LA l lines -> HA <= LA -> LA + 16 <= HA + 96 ->
                (LA + 16 <= HA + 64 \/ HA + 80 <= LA) -> (forall q, In q (list_blocks l) -> ~ In q (list_blocks le)) ->
                list_at Bm L2 A2 m4 LA l lines).
  { intros LA l lines H Ha Hb Hc Hd. apply (list_at_rmid Bm API AX BW 8224 (bv_unsigned sp - 16) _ _ L1 A1 m3 md1
      L2 A2 m4 md2 _ _ _ SEG ltac:(lia) HM3 RM3 H).
    - intros i Hi. split; [apply PLR'; lia | cbv beta; lia].
    - intros q Hq. apply KP3. exact (Hd q Hq). }
  pose proof (LT4 _ _ _ LP3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros q [])) as LP4.
  pose proof (LT4 _ _ _ LH3 ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(intros q Hq; apply D2; apply in_or_app; right; exact Hq)) as LH4.
  assert (IMG4 : forall a cs, rw_cells rsegs m3 a cs -> (HA <= a /\ a + Z.of_nat (cells_size cs) <= HA + 64) ->
                 rw_cells rsegs m4 a cs).
  { intros a cs H Ha. apply (sr_img 8224 (bv_unsigned sp - 16) _ _ L1 A1 m3 md1 L2 A2 m4 md2 a cs SEG ltac:(lia) HM3 RM3 H).
    intros i Hi. split; [apply PLR'; lia | cbv beta; lia]. }
  pose proof (IMG4 _ _ C0_3 ltac:(cbn; lia)) as C0_4.
  pose proof (IMG4 _ _ C32_3 ltac:(cbn; lia)) as C32_4.
  pose proof (IMG4 _ _ PAD_3 ltac:(cbn; lia)) as PAD_4.
  pose proof (sr_hi 8224 (bv_unsigned sp - 16) _ _ L1 A1 m3 md1 L2 A2 m4 md2 _ _ SEG ltac:(lia) HM3 RM3 FR3
                ltac:(lia) ltac:(cbn; lia) ltac:(intros i Hi X; cbv beta in X; lia)) as FR4.
  assert (PV4 : pv = 0 \/ In (pv, 6000) (blocks L2 A2)).
  { destruct PV2 as [X|X]; [left; exact X|]. destruct (Z.eqb_spec pv 0) as [E|E]; [left; exact E|right].
    apply (B2a pv 6000 X). apply D2. apply in_or_app. left.
    destruct (pv =? 0) eqn:EZ; [apply Z.eqb_eq in EZ; exfalso; exact (E EZ) | left; reflexivity]. }
  assert (WR3 : forall a, bv_unsigned sp - 8240 <= a < bv_unsigned sp -> writable_at (ms_segs Bm) m3 a)
    by (intros a Ha; apply SC3; unfold sk; left; exact Ha).
  pose proof (rmid_widen Bm API 8224 (bv_unsigned sp - 16) 8240 (bv_unsigned sp)
                (fun a => HA + 64 <= a < HA + 64 + 16) (fun q => In q (list_blocks le)) _ _ _ _ _ _ _ _ HM3
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) WR3 ltac:(intros a Ha X; cbv beta in X; lia) RM3) as RM3w.
  pose proof (rmid_seq Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HWF RM012 RM3w) as RM0123.
  pose proof RM0123 as (HM4' & HWF4' & HBD4' & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC4').
  destruct (mr_model _ _ LAWS _ _ _ _ HM4) as (Hh4 & Hl4 & _).
  assert (E4_2 : getr regs4 2 = Z_to_bv 64 (bv_unsigned sp + -16))
    by exact (eq_trans (PR3 2 ltac:(unfold callee_saved; lia)) E3_2).
  assert (E4_4 : getr regs4 4 = getr regs 4) by exact (eq_trans (PR3 4 ltac:(unfold callee_saved; lia)) E3_4).
  assert (E4_8 : getr regs4 8 = Z_to_bv 64 HA) by exact (eq_trans (PR3 8 ltac:(unfold callee_saved; lia)) E3_8).
  assert (KEEP4 : forall r, (r = 3 \/ r = 4 \/ r = 9 \/ 18 <= r <= 27) ->
            getr regs4 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr. rewrite (PR3 r ltac:(unfold callee_saved; lia)). exact (KEEP3 r Hr). }
  change (PropExec.getr regs3 1) with (getr regs3 1). rewrite E3_1.
  eapply (kseg regs4 (Z_to_bv 64 0x1461c) m4 md2); [exact WX | exact RO4 | exact Hh4 | exact Hl4 | | |].
  { unfold Regs6ss.mkR_of. eapply sr_seg2 with (k := 80) (pc' := 0x14624). right. split; reflexivity. }
  { intros s0 (b0 & -> & _). do 3 eexists. reflexivity. }
  intros R pc' m0' regs5 m5 HQ GR5 MREL5 ROS5.
  destruct HQ as (a0'' & EQ & Ea0'). injection EQ as ER EP EM. subst R pc' m0'.
  destruct (rmid_norm Bm API 8240 (bv_unsigned sp) (fun _ => False) (fun _ => False) L2 A2 m4 md2
              (normalize rsegs m4) m5 [] SEG RO4 MREL5 ROS5 (munch_refl _ _) (wmono_refl _ _) HM4' HWF4' HBD4' HK0)
    as (RM4 & MU5 & WM5).
  { exact SC4'. }
  { intros x Hx O. exfalso. exact (O I). }
  { intros a Ho. exact I. }
  { intros p n i Hp Hi O. exfalso. exact (O I). }
  pose proof (rmid_seq Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HWF RM0123 RM4) as RM01234.
  pose proof RM01234 as (HM5 & HWF5 & HBD5 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC5).
  pose proof (ro_agree_same rsegs m4 m5 RO4 ROS5) as RO5.
  assert (KF2 : forall q, kept_block (fun _ => False) (fun _ => False) L2 A2 q)
    by (intros q; split; [intros [] | intros k i _ _ []]).
  assert (IMG5 : forall a cs, rw_cells rsegs m4 a cs -> HA <= a -> a + Z.of_nat (cells_size cs) <= HA + 96 ->
                 rw_cells rsegs m5 a cs).
  { intros a cs H Ha Hb. apply (sr_img 8240 (bv_unsigned sp) _ _ L2 A2 m4 md2 L2 A2 m5 md2 a cs SEG HK0 HM4' RM4 H).
    intros i Hi. split; [apply PLR'; lia | intros []]. }
  assert (LT5 : forall LA l lines, list_at Bm L2 A2 m4 LA l lines -> HA <= LA -> LA + 16 <= HA + 96 ->
                list_at Bm L2 A2 m5 LA l lines).
  { intros LA l lines H Ha Hb. apply (list_at_rmid Bm API AX BW 8240 (bv_unsigned sp) _ _ L2 A2 m4 md2 L2 A2 m5 md2
      _ _ _ SEG HK0 HM4' RM4 H); [intros i Hi; split; [apply PLR'; lia | intros []] | intros q _; apply KF2]. }
  pose proof (LT5 _ _ _ LP4 ltac:(lia) ltac:(lia)) as LP5.
  pose proof (LT5 _ _ _ LE4 ltac:(lia) ltac:(lia)) as LE5.
  pose proof (LT5 _ _ _ LH4 ltac:(lia) ltac:(lia)) as LH5.
  pose proof (IMG5 _ _ C0_4 ltac:(lia) ltac:(cbn; lia)) as C0_5.
  pose proof (IMG5 _ _ C32_4 ltac:(lia) ltac:(cbn; lia)) as C32_5.
  pose proof (IMG5 _ _ PAD_4 ltac:(lia) ltac:(cbn; lia)) as PAD_5.
  pose proof (rw_cells_transport rsegs [] m4 m5 _ _ FR4 MU5 WM5 I) as FR5.
  destruct (mr_model _ _ LAWS _ _ _ _ HM5) as (Hh5 & Hl5 & _).
  assert (E5_1 : getr regs5 1 = Z_to_bv 64 0x14624) by (rewrite GR5; reflexivity).
  assert (E5_2 : getr regs5 2 = Z_to_bv 64 (bv_unsigned sp + -16)) by (rewrite GR5; exact E4_2).
  assert (E5_4 : getr regs5 4 = getr regs 4) by (rewrite GR5; exact E4_4).
  assert (E5_8 : getr regs5 8 = Z_to_bv 64 HA) by (rewrite GR5; exact E4_8).
  assert (E5_10 : PropExec.getr regs5 10 = Z_to_bv 64 (HA + 80)).
  { change (PropExec.getr regs5 10) with (getr regs5 10). rewrite GR5. cbn. rewrite Ea0'.
    change (reg_get regs4 8) with (getr regs4 8). rewrite E4_8, unsigned_lit by lia. reflexivity. }
  assert (KEEP5 : forall r, (r = 3 \/ r = 4 \/ r = 9 \/ 18 <= r <= 27) ->
            getr regs5 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr. rewrite <- (KEEP4 r Hr), GR5.
    assert (Hc : r = 3 \/ r = 4 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                 r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    repeat (destruct Hc as [Hc|Hc]; [subst r; reflexivity|]); subst r; reflexivity. }
  assert (SP5 : spZ regs5 = bv_unsigned sp - 16) by (unfold spZ; rewrite E5_2; apply unsigned_lit; lia).
  assert (LAu5 : bv_unsigned (Z_to_bv 64 (HA + 80)) = HA + 80) by (apply unsigned_lit; lia).
  eapply SR_bind.
  { apply (LFc L2 A2 regs5 m5 md2 (runF RF [] (runF RF [] bnd (hlist_free_tr (known_at L A) lp)) (hlist_free_tr (known_at L A) le)) lh true).
    - reflexivity.
    - eapply cpk_of_rmid; [exact RM01234 | exact INIT2 | rewrite E5_1; apply ret_ok_even; vm_compute; reflexivity
                           | rewrite E5_4; exact HTP | rewrite SP5, Zminus_mod, HAL; reflexivity | rewrite SP5; lia
                           | rewrite SP5; lia | lia | rewrite SP5; lia | rewrite SP5; lia].
    - exact INIT2.
    - exact RO5.
    - rewrite E5_10, LAu5. intros a Ha. split; [apply PLR'; lia | apply hf_ro_glob; lia].
    - rewrite E5_10, LAu5. exact LH5.
    - exact RES2. }
  intros c6 (L3 & A3 & regs6 & m6 & md3 & -> & RP3 & INIT3 & (qs3 & LQ3 & RES3) & RO6 & LH6 & ZB3 & B3a & B3b).
  rewrite nret_list_free in LQ3. apply length_zero_iff_nil in LQ3. subst qs3.
  rewrite E5_10, LAu5 in RP3, LH6.
  destruct (rp_split Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ RP3) as (RM5 & PR5). rewrite SP5 in RM5.
  pose proof RM5 as (HM6 & HWF6 & HBD6 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC6).
  assert (NM3 : hlist_free_tr (known_at L2 A2) lh = hlist_free_tr (known_at L A) lh).
  { apply hlist_free_tr_ext. intros a Ha. unfold known_at. f_equal.
    destruct (hf_list_pos Bm L A m1 (HA + 80) lh true a LH1 Ha) as (k & Hk & Hin).
    assert (N1 : ~ In a (list_blocks lp)).
    { apply D1. apply in_or_app. right. apply in_or_app. right. exact Ha. }
    assert (N2 : ~ In a (list_blocks le)) by (apply D2; apply in_or_app; right; exact Ha).
    rewrite (sr_sptr_keep _ _ _ _ _ _ _ _ _ _ _ _ a k RM3 (NODUP _ _ _ _ HM3) (NODUP _ _ _ _ HM4) (B1a a k Hin N1) Hk N2).
    exact (sr_sptr_keep _ _ _ _ _ _ _ _ _ _ _ _ a k RM1 (NODUP _ _ _ _ HM1) (NODUP _ _ _ _ HM2) Hin Hk N1). }
  change (rt_ok RF A3 (runF RF [] (runF RF [] (runF RF [] bnd (hlist_free_tr (known_at L A) lp)) (hlist_free_tr (known_at L A) le))
    (hlist_free_tr (known_at L2 A2) lh))) in RES3.
  rewrite NM3 in RES3.
  assert (EP5 : forall a, (fun a => HA + 80 <= a < HA + 80 + 16) a -> (HA + 80 <= a < HA + 96) \/
                  (0 < 0 /\ 0 <= a < 0 + 16 * 0)) by (intros a X; left; cbv beta in X; lia).
  assert (KP5 : forall q, ~ In q (list_blocks lh) ->
                kept_block (fun a => HA + 80 <= a < HA + 80 + 16) (fun q => In q (list_blocks lh)) L2 A2 q).
  { intros q Hq. apply (hf_kept Bm API AX L2 A2 m5 md2 _ _ (HA + 80) (HA + 96) 0 0 q HM5);
      [intros a Ha; exact (proj1 (PLR' a ltac:(lia))) | exact EP5 | intros X; lia | exact Hq | intros X; lia]. }
  assert (LT6 : forall LA l lines, list_at Bm L2 A2 m5 LA l lines -> HA <= LA -> LA + 16 <= HA + 80 ->
                (forall q, In q (list_blocks l) -> ~ In q (list_blocks lh)) ->
                list_at Bm L3 A3 m6 LA l lines).
  { intros LA l lines H Ha Hb Hd. apply (list_at_rmid Bm API AX BW 8224 (bv_unsigned sp - 16) _ _ L2 A2 m5 md2
      L3 A3 m6 md3 _ _ _ SEG ltac:(lia) HM5 RM5 H).
    - intros i Hi. split; [apply PLR'; lia | cbv beta; lia].
    - intros q Hq. apply KP5. exact (Hd q Hq). }
  pose proof (LT6 _ _ _ LP5 ltac:(lia) ltac:(lia) ltac:(intros q [])) as LP6.
  pose proof (LT6 _ _ _ LE5 ltac:(lia) ltac:(lia) ltac:(intros q [])) as LE6.
  assert (IMG6 : forall a cs, rw_cells rsegs m5 a cs -> (HA <= a /\ a + Z.of_nat (cells_size cs) <= HA + 80) ->
                 rw_cells rsegs m6 a cs).
  { intros a cs H Ha. apply (sr_img 8224 (bv_unsigned sp - 16) _ _ L2 A2 m5 md2 L3 A3 m6 md3 a cs SEG ltac:(lia) HM5 RM5 H).
    intros i Hi. split; [apply PLR'; lia | cbv beta; lia]. }
  pose proof (IMG6 _ _ C0_5 ltac:(cbn; lia)) as C0_6.
  pose proof (IMG6 _ _ C32_5 ltac:(cbn; lia)) as C32_6.
  pose proof (IMG6 _ _ PAD_5 ltac:(cbn; lia)) as PAD_6.
  pose proof (sr_hi 8224 (bv_unsigned sp - 16) _ _ L2 A2 m5 md2 L3 A3 m6 md3 _ _ SEG ltac:(lia) HM5 RM5 FR5
                ltac:(lia) ltac:(cbn; lia) ltac:(intros i Hi X; cbv beta in X; lia)) as FR6.
  assert (PV6 : pv = 0 \/ In (pv, 6000) (blocks L3 A3)).
  { destruct PV4 as [X|X]; [left; exact X|]. destruct (Z.eqb_spec pv 0) as [E|E]; [left; exact E|right].
    apply (B3a pv 6000 X). apply D3.
    destruct (pv =? 0) eqn:EZ; [apply Z.eqb_eq in EZ; exfalso; exact (E EZ) | left; reflexivity]. }
  assert (WR5 : forall a, bv_unsigned sp - 8240 <= a < bv_unsigned sp -> writable_at (ms_segs Bm) m5 a)
    by (intros a Ha; apply SC5; unfold sk; left; exact Ha).
  pose proof (rmid_widen Bm API 8224 (bv_unsigned sp - 16) 8240 (bv_unsigned sp)
                (fun a => HA + 80 <= a < HA + 80 + 16) (fun q => In q (list_blocks lh)) _ _ _ _ _ _ _ _ HM5
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) WR5 ltac:(intros a Ha X; cbv beta in X; lia) RM5) as RM5w.
  pose proof (rmid_seq Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HWF RM01234 RM5w) as RM05.
  pose proof RM05 as (HM6' & HWF6' & HBD6' & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC6').
  destruct (mr_model _ _ LAWS _ _ _ _ HM6) as (Hh6 & Hl6 & _).
  assert (E6_2 : getr regs6 2 = Z_to_bv 64 (bv_unsigned sp + -16))
    by exact (eq_trans (PR5 2 ltac:(unfold callee_saved; lia)) E5_2).
  assert (E6_4 : getr regs6 4 = getr regs 4) by exact (eq_trans (PR5 4 ltac:(unfold callee_saved; lia)) E5_4).
  assert (E6_8 : getr regs6 8 = Z_to_bv 64 HA) by exact (eq_trans (PR5 8 ltac:(unfold callee_saved; lia)) E5_8).
  assert (KEEP6 : forall r, (r = 3 \/ r = 4 \/ r = 9 \/ 18 <= r <= 27) ->
            getr regs6 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr. rewrite (PR5 r ltac:(unfold callee_saved; lia)). exact (KEEP5 r Hr). }
  destruct (hg_cut rsegs m6 (HA + 32) [C8 w4] [C8 (Z_to_bv 64 pv); C8 w5; C4 w6] C32_6) as (_ & C40a).
  destruct (hg_cut rsegs m6 _ [C8 (Z_to_bv 64 pv)] [C8 w5; C4 w6] C40a) as (C40 & _).
  match type of C40 with rw_cells _ _ ?a _ => replace a with (HA + 40) in C40 by (cbn; lia) end.
  change (PropExec.getr regs5 1) with (getr regs5 1). rewrite E5_1.
  eapply (kseg regs6 (Z_to_bv 64 0x14624) m6 md3); [exact WX | exact RO6 | exact Hh6 | exact Hl6 | | |].
  { unfold Regs6ss.mkR_of. eapply (sr_seg4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                      (Z_to_bv 64 pv)).
    - change (reg_get regs6 8) with (getr regs6 8). rewrite E6_8, unsigned_lit by lia. lia.
    - change (reg_get regs6 8) with (getr regs6 8). rewrite E6_8, unsigned_lit by lia. lia.
    - change (reg_get regs6 8) with (getr regs6 8). rewrite E6_8, unsigned_lit by lia.
      apply (rw_cells_normalize rsegs m6 _ _ RO6 C40). intros i Hi. apply hf_ro_glob. cbn in Hi. lia. }
  { intros s0 ->. do 3 eexists. reflexivity. }
  intros R pc' m0' regs7 m7 HQ GR7 MREL7 ROS7.
  injection HQ as ER EP EM. subst R pc' m0'.
  destruct (rmid_norm Bm API 8240 (bv_unsigned sp) (fun _ => False) (fun _ => False) L3 A3 m6 md3
              (normalize rsegs m6) m7 [] SEG RO6 MREL7 ROS7 (munch_refl _ _) (wmono_refl _ _) HM6' HWF6' HBD6' HK0)
    as (RM6 & MU7 & WM7).
  { exact SC6'. }
  { intros x Hx O. exfalso. exact (O I). }
  { intros a Ho. exact I. }
  { intros p n i Hp Hi O. exfalso. exact (O I). }
  pose proof (rmid_seq Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HWF RM05 RM6) as RM06.
  pose proof RM06 as (HM7 & HWF7 & HBD7 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC7).
  pose proof (ro_agree_same rsegs m6 m7 RO6 ROS7) as RO7.
  assert (KF3 : forall q, kept_block (fun _ => False) (fun _ => False) L3 A3 q)
    by (intros q; split; [intros [] | intros k i _ _ []]).
  assert (IMG7 : forall a cs, rw_cells rsegs m6 a cs -> HA <= a -> a + Z.of_nat (cells_size cs) <= HA + 96 ->
                 rw_cells rsegs m7 a cs).
  { intros a cs H Ha Hb. apply (sr_img 8240 (bv_unsigned sp) _ _ L3 A3 m6 md3 L3 A3 m7 md3 a cs SEG HK0 HM6' RM6 H).
    intros i Hi. split; [apply PLR'; lia | intros []]. }
  assert (LT7 : forall LA l lines, list_at Bm L3 A3 m6 LA l lines -> HA <= LA -> LA + 16 <= HA + 96 ->
                list_at Bm L3 A3 m7 LA l lines).
  { intros LA l lines H Ha Hb. apply (list_at_rmid Bm API AX BW 8240 (bv_unsigned sp) _ _ L3 A3 m6 md3 L3 A3 m7 md3
      _ _ _ SEG HK0 HM6' RM6 H); [intros i Hi; split; [apply PLR'; lia | intros []] | intros q _; apply KF3]. }
  pose proof (LT7 _ _ _ LP6 ltac:(lia) ltac:(lia)) as LP7.
  pose proof (LT7 _ _ _ LE6 ltac:(lia) ltac:(lia)) as LE7.
  pose proof (LT7 _ _ _ LH6 ltac:(lia) ltac:(lia)) as LH7.
  pose proof (IMG7 _ _ C0_6 ltac:(lia) ltac:(cbn; lia)) as C0_7.
  pose proof (IMG7 _ _ C32_6 ltac:(lia) ltac:(cbn; lia)) as C32_7.
  pose proof (IMG7 _ _ PAD_6 ltac:(lia) ltac:(cbn; lia)) as PAD_7.
  pose proof (rw_cells_transport rsegs [] m6 m7 _ _ FR6 MU7 WM7 I) as FR7.
  assert (E7_1 : getr regs7 1 = Z_to_bv 64 0x1462c) by (rewrite GR7; reflexivity).
  assert (E7_2 : getr regs7 2 = Z_to_bv 64 (bv_unsigned sp + -16)) by (rewrite GR7; exact E6_2).
  assert (E7_4 : getr regs7 4 = getr regs 4) by (rewrite GR7; exact E6_4).
  assert (E7_8 : getr regs7 8 = Z_to_bv 64 HA) by (rewrite GR7; exact E6_8).
  assert (E7_10 : getr regs7 10 = Z_to_bv 64 pv) by (rewrite GR7; reflexivity).
  assert (KEEP7 : forall r, (r = 3 \/ r = 4 \/ r = 9 \/ 18 <= r <= 27) ->
            getr regs7 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr. rewrite <- (KEEP6 r Hr), GR7.
    assert (Hc : r = 3 \/ r = 4 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                 r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    repeat (destruct Hc as [Hc|Hc]; [subst r; reflexivity|]); subst r; reflexivity. }
  assert (SP7 : spZ regs7 = bv_unsigned sp - 16) by (unfold spZ; rewrite E7_2; apply unsigned_lit; lia).
  set (bnd3 := runF RF [] (runF RF [] (runF RF [] bnd (hlist_free_tr (known_at L A) lp)) (hlist_free_tr (known_at L A) le))
    (hlist_free_tr (known_at L A) lh)) in *.
  destruct (mr_model _ _ LAWS _ _ _ _ HM7) as (Hh7 & Hl7 & _).
  assert (FREE : SR rsegs (mkCfg (YK11.mkst regs7 (Z_to_bv 64 0x15664) m7 (seg_rom rsegs)) md3)
     (fun c' => exists L4 A4 regs8 m8 md4, c' = mkCfg (YK11.mkst regs8 (getr regs7 1) m8 (seg_rom rsegs)) md4 /\
        rmid Bm API 8240 (bv_unsigned sp) (fun _ => False) (fun q => pv <> 0 /\ q = pv) L3 A3 m7 md3 L4 A4 m8 md4 /\
        regs_preserved regs7 regs8 /\ st_init_done A4 = true /\ ro_agree rsegs m8 /\
        rt_ok RF A4 (runF RF [] bnd3 (if pv =? 0 then [] else [RFree 6000 (known_at L A pv)])) /\
        rw_cells rsegs m8 (bv_unsigned sp - 16) [C8 (reg_get regs 8); C8 (reg_get regs 1)] /\
        (forall q m, In (q, m) (blocks L3 A3) -> (pv = 0 \/ q <> pv) -> In (q, m) (blocks L4 A4)) /\
        (forall q m, In (q, m) (blocks L4 A4) -> In (q, m) (blocks L3 A3) /\ (pv = 0 \/ q <> pv)) /\
        (pv = 0 -> blocks L4 A4 = blocks L3 A3))).
  { destruct (Z.eqb_spec pv 0) as [PZ|PNZ].
    - pose proof FN as FNc. unfold free_null_contract in FNc. rewrite SEG, HFREE in FNc.
      eapply SR_mono.
      { apply FNc; [rewrite E7_1; apply ret_ok_even; vm_compute; reflexivity | rewrite E7_10, PZ; reflexivity
                   | exact Hh7 | exact Hl7]. }
      intros c' ->. exists L3, A3, regs7, m7, md3.
      split; [reflexivity|].
      split.
      { apply (rmid_A Bm API 8240 (bv_unsigned sp) _ _ L3 A3 m7 md3 m7 [] HM7 HWF7 HBD7 (hg_img_low Bm SEG) HK0 SC7
                 (munch_refl _ _)).
        - rewrite SEG. apply wmono_refl.
        - intros x _ O. exfalso. exact (O I).
        - intros a _. exact I.
        - intros p n i _ _ O. exfalso. exact (O I). }
      split; [intros r _; reflexivity|].
      split; [exact INIT3|]. split; [exact RO7|].
      split; [exact RES3|].
      split; [exact FR7|].
      split; [intros q m H _; exact H|]. split; [intros q m H; split; [exact H | left; exact PZ]|].
      intros _; reflexivity.
    - destruct PV6 as [X|PB]; [contradiction|].
      pose proof PB as PB'. unfold blocks in PB'. apply in_map_iff in PB' as ([p k] & Ep & Hp).
      cbn [fst snd] in Ep. injection Ep as Ep Ek. subst k.
      assert (NP1 : ~ In pv (list_blocks lp)).
      { apply D1. apply in_or_app. left. try rewrite (proj2 (Z.eqb_neq pv 0) PNZ). simpl. left. reflexivity. }
      assert (NP2 : ~ In pv (list_blocks le)).
      { apply D2. apply in_or_app. left. try rewrite (proj2 (Z.eqb_neq pv 0) PNZ). simpl. left. reflexivity. }
      assert (NP3 : ~ In pv (list_blocks lh)).
      { apply D3. try rewrite (proj2 (Z.eqb_neq pv 0) PNZ). simpl. left. reflexivity. }
      assert (Hin0 : In (pv, 6000) (blocks L A)) by (destruct PVC as [X|X]; [contradiction | exact X]).
      pose proof (B1a pv 6000 Hin0 NP1) as Hin1.
      pose proof (B2a pv 6000 Hin1 NP2) as Hin2.
      assert (PE : sptr_of L A pv = p).
      { rewrite <- (sr_sptr_keep _ _ _ _ _ _ _ _ _ _ _ _ pv 6000 RM1 (NODUP _ _ _ _ HM1) (NODUP _ _ _ _ HM2) Hin0
                      ltac:(lia) NP1).
        rewrite <- (sr_sptr_keep _ _ _ _ _ _ _ _ _ _ _ _ pv 6000 RM3 (NODUP _ _ _ _ HM3) (NODUP _ _ _ _ HM4) Hin1
                      ltac:(lia) NP2).
        rewrite <- (sr_sptr_keep _ _ _ _ _ _ _ _ _ _ _ _ pv 6000 RM5 (NODUP _ _ _ _ HM5) (NODUP _ _ _ _ HM6) Hin2
                      ltac:(lia) NP3).
        rewrite <- Ep. exact (sptr_of_eq L3 A3 p 6000 (NODUP _ _ _ _ HM7) Hp). }
      pose proof FRc as FRcc. unfold free_contract_rt in FRcc. rewrite SEG, HFREE in FRcc.
      eapply SR_mono.
      { apply (FRcc L3 A3 regs7 m7 md3 p 6000 bnd3).
        - change (call_pre_k Bm (aa_MR API) ALLOC_STACK L3 A3 regs7 m7 md3).
          eapply cpk_of_rmid; [exact RM06 | exact INIT3 | rewrite E7_1; apply ret_ok_even; vm_compute; reflexivity
             | rewrite E7_4; exact HTP | rewrite SP7, Zminus_mod, HAL; reflexivity | rewrite SP7; unfold ALLOC_STACK; lia
             | rewrite SP7; lia | unfold ALLOC_STACK; lia | rewrite SP7; unfold ALLOC_STACK; lia | rewrite SP7; lia].
        - exact RO7.
        - exact Hp.
        - rewrite E7_10, Ep. reflexivity.
        - exact RES3. }
      intros c' (L4 & A4 & regs8 & m8 & md4 & -> & CP & (b1 & b2 & BLa & BLb) & KEPT & RO8 & GK & SURV & INITi &
        LEN & RES4).
      destruct (rmid_of_free Bm API _ _ _ _ _ _ _ _ _ _ _ p 6000 AX CTX HM7 HWF7 CP Hp ltac:(lia) LEN SURV)
        as (RMf & PRf).
      rewrite SP7 in RMf.
      assert (WR7 : forall a, bv_unsigned sp - 8240 <= a < bv_unsigned sp -> writable_at (ms_segs Bm) m7 a)
        by (intros a Ha; apply SC7; unfold sk; left; exact Ha).
      pose proof (rmid_widen Bm API ALLOC_STACK (bv_unsigned sp - 16) 8240 (bv_unsigned sp) (fun _ => False)
                    (fun q => q = ptr_addr L3 p) _ _ _ _ _ _ _ _ HM7 ltac:(unfold ALLOC_STACK; lia) ltac:(lia)
                    ltac:(lia) ltac:(lia) WR7 (fun a _ X => X) RMf) as RMfw.
      exists L4, A4, regs8, m8, md4.
      split; [reflexivity|].
      split; [apply (rmid_EF Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ _ RMfw); [intros a [] | intros q ->; split; congruence]|].
      split; [exact PRf|].
      split; [exact (INITi INIT3)|]. split; [exact RO8|].
      split; [rewrite <- PE in RES4; exact RES4|].
      split; [exact (sr_hi ALLOC_STACK (bv_unsigned sp - 16) _ _ L3 A3 m7 md3 L4 A4 m8 md4 _ _ SEG
                      ltac:(unfold ALLOC_STACK in *; lia) HM7 RMf FR7 ltac:(lia) ltac:(cbn; lia) (fun _ _ X => X))|].
      assert (ND3 := NODUP L3 A3 m7 md3 HM7). apply hf_nodup in ND3. rewrite BLa, map_app in ND3. cbn [map fst] in ND3.
      apply NoDup_remove_2 in ND3. rewrite <- map_app in ND3.
      split.
      { intros q m Hq [X|Hne]; [contradiction|]. rewrite BLb. rewrite BLa in Hq.
        apply in_app_iff in Hq as [Hq|[Hq|Hq]]; [apply in_or_app; left; exact Hq | | apply in_or_app; right; exact Hq].
        injection Hq as E1 E2. exfalso. apply Hne. rewrite <- E1, Ep. reflexivity. }
      split.
      { intros q m Hq. rewrite BLb in Hq. split.
        - rewrite BLa. apply in_app_iff in Hq as [Hq|Hq]; apply in_or_app; [left; exact Hq | right; right; exact Hq].
        - right. intros ->. apply ND3. rewrite Ep. exact (in_map fst _ (pv, m) Hq). }
      intros X. contradiction. }
  eapply SR_bind; [exact FREE|].
  intros c8 (L4 & A4 & regs8 & m8 & md4 & -> & RM7 & PR7 & INIT4 & RO8 & RES4 & FR8 & B4a & B4b & ZB4).
  pose proof (rmid_seq Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HWF RM06 RM7) as RM07.
  pose proof RM07 as (HM8 & HWF8 & HBD8 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC8).
  destruct (mr_model _ _ LAWS _ _ _ _ HM8) as (Hh8 & Hl8 & _).
  pose proof RM7 as (HM8a & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  assert (IMG8 : forall a cs, rw_cells rsegs m7 a cs -> HA <= a -> a + Z.of_nat (cells_size cs) <= HA + 96 ->
                 rw_cells rsegs m8 a cs).
  { intros a cs H Ha Hb. apply (sr_img 8240 (bv_unsigned sp) _ _ L3 A3 m7 md3 L4 A4 m8 md4 a cs SEG HK0 HM7 RM7 H).
    intros i Hi. split; [apply PLR'; lia | intros []]. }
  assert (LT8 : forall LA, list_at Bm L3 A3 m7 LA empty_list true \/ list_at Bm L3 A3 m7 LA empty_list false ->
                HA <= LA -> LA + 16 <= HA + 96 ->
                rw_cells rsegs m8 LA [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]).
  { intros LA [H|H] Ha Hb; destruct H as (H & _); rewrite SEG in H; exact (IMG8 _ _ H Ha ltac:(cbn; lia)). }
  pose proof (LT8 _ (or_intror LP7) ltac:(lia) ltac:(lia)) as H16.
  pose proof (LT8 _ (or_introl LE7) ltac:(lia) ltac:(lia)) as H64.
  pose proof (LT8 _ (or_introl LH7) ltac:(lia) ltac:(lia)) as H80.
  pose proof (IMG8 _ _ C0_7 ltac:(lia) ltac:(cbn; lia)) as C0_8.
  pose proof (IMG8 _ _ C32_7 ltac:(lia) ltac:(cbn; lia)) as C32_8.
  pose proof (IMG8 _ _ PAD_7 ltac:(lia) ltac:(cbn; lia)) as PAD_8.
  pose proof (hg_join rsegs m8 HA (HA + 16) _ _ C0_8 H16 ltac:(cbn; lia)) as J1.
  pose proof (hg_join rsegs m8 HA (HA + 32) _ _ J1 C32_8 ltac:(cbn; lia)) as J2.
  pose proof (hg_join rsegs m8 HA (HA + 60) _ _ J2 PAD_8 ltac:(cbn; lia)) as J3.
  pose proof (hg_join rsegs m8 HA (HA + 64) _ _ J3 H64 ltac:(cbn; lia)) as J4.
  pose proof (hg_join rsegs m8 HA (HA + 80) _ _ J4 H80 ltac:(cbn; lia)) as J5.
  match type of J5 with rw_cells _ _ _ ?cs =>
    assert (SL : rw_cells rsegs m8 HA [CB 96 (cells_bytes cs)]) end.
  { apply (rw_cells_retype rsegs m8 HA _ _ J5); [| cbn [cells_bytes cbytes]; apply app_nil_r].
    destruct J5 as [[W _] _]. pose proof (cells_bytes_length _ W) as LW. cbn in LW |- *. tauto. }
  assert (E8_2 : getr regs8 2 = Z_to_bv 64 (bv_unsigned sp + -16))
    by exact (eq_trans (PR7 2 ltac:(unfold callee_saved; lia)) E7_2).
  assert (E8_8 : getr regs8 8 = Z_to_bv 64 HA) by exact (eq_trans (PR7 8 ltac:(unfold callee_saved; lia)) E7_8).
  assert (KEEP8 : forall r, (r = 3 \/ r = 4 \/ r = 9 \/ 18 <= r <= 27) ->
            getr regs8 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
  { intros r Hr. rewrite (PR7 r ltac:(unfold callee_saved; lia)). exact (KEEP7 r Hr). }
  assert (S08 : bv_unsigned (reg_get regs8 8) = HA).
  { change (reg_get regs8 8) with (getr regs8 8). rewrite E8_8. apply unsigned_lit. lia. }
  rewrite E7_1.
  eapply (kseg regs8 (Z_to_bv 64 0x1462c) m8 md4); [exact WX | exact RO8 | exact Hh8 | exact Hl8 | | |].
  { unfold Regs6ss.mkR_of. eapply (sr_tail MSC) with (B := bv_unsigned sp - 16) (s0v := reg_get regs 8)
      (rav := reg_get regs 1).
    - exact E8_2.
    - lia.
    - lia.
    - apply mem_inv_normalize.
    - apply (rw_cells_normalize rsegs m8 _ _ RO8 FR8). intros i Hi. cbn in Hi.
      match goal with |- ro_addr _ ?x = _ => change x with (wa (bv_unsigned sp - 16 + i)) end.
      apply ro_addr_hi. lia.
    - rewrite S08. apply (rw_cells_normalize rsegs m8 _ _ RO8 SL). intros i Hi. apply hf_ro_glob. cbn in Hi. lia. }
  { intros s0 (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & -> & _).
    do 3 eexists. reflexivity. }
  intros R pc' m0' regs9 m9 HQ GR9 MREL9 ROS9.
  destruct HQ as (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m9n & EQ & MU9 & WM9 & MI9 & Z9).
  injection EQ as ER EP EM. subst R pc' m0'.
  rewrite S08 in MU9, Z9.
  destruct (rmid_norm Bm API 8240 (bv_unsigned sp) (fun a => HA <= a < HA + 96) (fun _ => False) L4 A4 m8 md4
              m9n m9 [(HA, HA + 96)] SEG RO8 MREL9 ROS9 MU9 WM9 HM8 HWF8 HBD8 HK0) as (RM8 & MU9r & WM9r).
  { exact SC8. }
  { intros x Hx O. destruct (hg_not_out _ _ O) as (lo & hi & [E|[]] & Hlh). injection E as <- <-. right. lia. }
  { intros a Ho. apply hg_out. intros lo hi [E|[]]. injection E as <- <-.
    destruct (Z_lt_le_dec a HA) as [D|D]; [left; exact D|].
    destruct (Z_le_gt_dec (HA + 96) a) as [D'|D']; [right; exact D'|].
    exfalso. exact (hg_img_not_owned Bm API AX L4 A4 m8 md4 a HM8 (PLR' a ltac:(lia)) Ho). }
  { intros p n i Hp Hi O. exfalso. destruct (hg_not_out _ _ O) as (lo & hi & [E|[]] & Hlh). injection E as <- <-.
    apply (ax_blocks_img AX L4 A4 m8 md4 p n i HM8 Hp Hi). exact (proj1 (PLR' (ptr_addr L4 p + i) ltac:(lia))). }
  pose proof (rmid_seq Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HWF RM07 RM8) as RMall.
  apply SR_ret. exists L4, A4, regs9, m9, md4.
  split; [f_equal; f_equal; change (reg_get regs 1) with (getr regs 1); exact (ret_pc_of_ok _ HRA)|].
  split.
  { apply rp_join.
    - rewrite SPE. apply (rmid_EF Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ _ RMall).
      + intros a X. cbv beta in X |- *. unfold SRC_SIZE.
        repeat match type of X with _ \/ _ => destruct X as [X|X] | False => destruct X end; lia.
      + intros q X. cbv beta in X. unfold sr_S.
        repeat match type of X with
               | _ \/ _ => destruct X as [X|X]
               | False => destruct X
               end;
          try (apply in_or_app; left; exact X);
          try (apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; exact X);
          try (apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact X);
          try (destruct X as (X1 & ->); apply in_or_app; right; apply in_or_app; left;
               rewrite (proj2 (Z.eqb_neq pv 0) X1); left; reflexivity).
    - intros r Hr. rewrite GR9. unfold callee_saved in Hr.
      assert (Hc : r = 2 \/ r = 8 \/ r = 3 \/ r = 4 \/ r = 9 \/ 18 <= r <= 27) by lia.
      destruct Hc as [->|[->|Hc]].
      + transitivity (Z_to_bv 64 (bv_unsigned sp - 16 + 16)); [reflexivity|].
        replace (bv_unsigned sp - 16 + 16) with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
      + reflexivity.
      + rewrite <- (KEEP8 r Hc).
        assert (Hc' : r = 3 \/ r = 4 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                      r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
        repeat (destruct Hc' as [Hc'|Hc']; [subst r; reflexivity|]); subst r; reflexivity. }
  split; [exact INIT4|].
  split; [exact (ro_agree_same rsegs m8 m9 RO8 ROS9)|].
  split; [exact (rw_cells_of_rel rsegs m9 m9n _ _ MREL9 Z9)|].
  split; [unfold sr_tr; rewrite !runF_app0 by apply nret_hlist_free; exact RES4|].
  assert (SP : forall q, ~ In q (sr_S lp le lh pv) <->
            ~ In q (list_blocks lp) /\ (pv = 0 \/ q <> pv) /\ ~ In q (list_blocks le) /\ ~ In q (list_blocks lh)).
  { intros q. unfold sr_S. rewrite !in_app_iff. destruct (Z.eqb_spec pv 0) as [E|E]; cbn [In].
    - split; [intros X; split; [tauto|]; split; [left; exact E | tauto] | tauto].
    - split; [intros X; split; [tauto|]; split; [right; intros ->; tauto | tauto]|].
      intros (X1 & X2 & X3 & X4) [Y|[[Y|[]]|[Y|Y]]]; [exact (X1 Y) | destruct X2; [contradiction | congruence] |
                                                     exact (X3 Y) | exact (X4 Y)]. }
  split.
  { intros q m Hq Hn. apply SP in Hn. destruct Hn as (X1 & X2 & X3 & X4).
    exact (B4a q m (B3a q m (B2a q m (B1a q m Hq X1) X3) X4) X2). }
  split.
  { intros q m Hq. destruct (B4b q m Hq) as (Y3 & X2). destruct (B3b q m Y3) as (Y2 & X4).
    destruct (B2b q m Y2) as (Y1 & X3). destruct (B1b q m Y1) as (Y0 & X1).
    split; [exact Y0|]. apply SP. tauto. }
  intros ES. unfold sr_S in ES. apply app_eq_nil in ES as (ES1 & ES).
  apply app_eq_nil in ES as (ES2 & ES). apply app_eq_nil in ES as (ES3 & ES4).
  assert (PV0 : pv = 0) by (destruct (Z.eqb_spec pv 0) as [E|E]; [exact E | discriminate]).
  rewrite (ZB4 PV0), (ZB3 ES4), (ZB2 ES3), (ZB1 ES1). reflexivity.
Qed.

Lemma sr_zero_not_src : forall L A mem HA h, rw_cells (ms_segs Bm) mem HA [CB 96%nat (nulbytes 96)] ->
  ~ src_at Bm L A mem HA h.
Proof.
  intros L A mem HA h Z S. destruct S as (C & _ & _ & HO & _).
  destruct Z as [[_ BZ] _]. destruct C as [[_ BC] _].
  rewrite HO in BC.
  destruct BZ as (_ & _ & BZ). destruct BC as (_ & _ & BC).
  specialize (BZ 4%nat ltac:(cbn; lia)). specialize (BC 4%nat ltac:(cbn; lia)).
  rewrite BZ in BC.
  assert (X : nth_error (cells_bytes [C4 (Z_to_bv 64 (hs_fd h)); C4 (Z_to_bv 64 1);
                C4 (Z_to_bv 64 (hs_closed h)); C4 (Z_to_bv 64 (hs_eintr h))]) 4 = Some (Z_to_bv 8 1))
    by reflexivity.
  rewrite X in BC. injection BC as BC. vm_compute in BC. discriminate.
Qed.

Lemma sr_zero_list : forall L A m LA lines,
  rw_cells (ms_segs Bm) m LA [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  list_at Bm L A m LA empty_list lines.
Proof.
  intros L A m LA lines H. split; [exact H|].
  split; [change (hl_n empty_list) with 0; change (hl_cap empty_list) with 0; lia|].
  split; [left; split; reflexivity|].
  split; [constructor|]. split; [intros X; exact X|]. apply Forall_nil.
Qed.

Theorem source_reset_holds : list_free_contract Bm API RF -> free_contract_rt Bm API RF -> free_null_contract Bm ->
  memset_contract -> source_reset_contract Bm API RF.
Proof.
  intros LF FRc FN MSC. unfold source_reset_contract.
  intros L A regs mem md bnd h j SEG PRE INIT RO PLR Hj4 R10 CASE PAD RES.
  set (HA := G_S + SRC_SIZE * Z.of_nat j) in *.
  destruct PAD as (pad & PAD).
  assert (Hrp : forall L' A' regs' mem' md' (S : list Z) (F' : Z -> Prop),
            relay_post Bm API SOURCE_RESET_K (fun a => HA <= a < HA + SRC_SIZE) (fun q => In q S)
              L A regs mem md L' A' regs' mem' md' -> (forall q, In q S -> F' q) ->
            relay_post Bm API SOURCE_RESET_K (fun a => HA <= a < HA + SRC_SIZE) F' L A regs mem md L' A' regs' mem' md').
  { intros L' A' regs' mem' md' S F' RP HF. destruct (rp_split Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ RP) as (RM & PR).
    apply rp_join; [|exact PR]. exact (rmid_EF Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ _ RM (fun a X => X) HF). }
  destruct CASE as [S1|S2].
  - pose proof S1 as S1'. apply src_at_iff in S1'. destruct S1' as (SB & LE & LH & ND).
    pose proof SB as (C0 & H1 & H2 & H3 & H4 & LP & C32 & H5 & H6 & H7 & PIn & PFr & PJ & PC & PW).
    rewrite SEG in C0, C32, PAD, RO.
    assert (PV0 : hs_partial h <> 0) by (destruct PFr as (F1 & _); lia).
    assert (SS : sr_S (hs_pending h) (hs_expected h) (hs_held h) (hs_partial h) = hs_blocks h).
    { unfold sr_S, hs_blocks. rewrite (proj2 (Z.eqb_neq _ 0) PV0). reflexivity. }
    assert (STR : sr_tr (known_at L A) (hs_pending h) (hs_expected h) (hs_held h) (hs_partial h) =
                  source_reset_tr (known_at L A) h).
    { unfold sr_tr, source_reset_tr. rewrite (proj2 (Z.eqb_neq _ 0) PV0). reflexivity. }
    rewrite SEG.
    eapply SR_mono.
    { apply (sr_chain LF FRc FN MSC L A regs mem md bnd (hs_pending h) (hs_expected h) (hs_held h) (hs_partial h)
               (Z_to_bv 64 (hs_fd h)) (Z_to_bv 64 (hs_open h)) (Z_to_bv 64 (hs_closed h)) (Z_to_bv 64 (hs_eintr h))
               (Z_to_bv 64 (hs_off h)) (Z_to_bv 64 (hs_npartial h)) (Z_to_bv 64 (hs_overlong h)) pad j
               SEG PRE INIT RO PLR Hj4 R10 C0 LP C32 PAD LE LH).
      - rewrite SS. apply hf_nodup. exact ND.
      - right. exact PIn.
      - exact RES. }
    intros c' (L' & A' & regs' & mem' & md' & -> & RP & INIT' & RO' & ZR & RES' & B1 & B2 & _).
    exists L', A', regs', mem', md'.
    split; [reflexivity|].
    split; [apply (Hrp _ _ _ _ _ _ _ RP); intros q X; split; [exact S1 | rewrite <- SS; exact X]|].
    split; [exact INIT'|]. split; [exact RO'|]. split; [exact ZR|].
    split.
    + intros _. split.
      * exists []. split; [unfold source_reset_tr; rewrite !nret_app, !nret_hlist_free; reflexivity|].
        rewrite <- STR. exact RES'.
      * rewrite <- SS. split; [exact B1 | exact B2].
    + intros Z. exfalso. rewrite <- SEG in Z. exact (sr_zero_not_src L A mem HA h Z S1).
  - rewrite SEG in S2, PAD, RO.
    assert (ZZ : rw_cells rsegs mem HA
      ([C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ++
       [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ++
       [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ++
       [CB 4 (nulbytes 4)] ++
       [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ++
       [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)])).
    { apply (rw_cells_retype rsegs mem HA _ _ S2); [cbn; tauto | vm_compute; reflexivity]. }
    destruct (hg_cut rsegs mem HA _ _ ZZ) as (Z0 & ZR1). clear ZZ.
    destruct (hg_cut rsegs mem _ _ _ ZR1) as (Z16 & ZR2). clear ZR1.
    destruct (hg_cut rsegs mem _ _ _ ZR2) as (Z32 & ZR3). clear ZR2.
    destruct (hg_cut rsegs mem _ _ _ ZR3) as (_ & ZR4). clear ZR3.
    destruct (hg_cut rsegs mem _ _ _ ZR4) as (Z64 & Z80). clear ZR4.
    match type of Z16 with rw_cells _ _ ?a _ => replace a with (HA + 16) in Z16 by (cbn; lia) end.
    match type of Z32 with rw_cells _ _ ?a _ => replace a with (HA + 32) in Z32 by (cbn; lia) end.
    match type of Z64 with rw_cells _ _ ?a _ => replace a with (HA + 64) in Z64 by (cbn; lia) end.
    match type of Z80 with rw_cells _ _ ?a _ => replace a with (HA + 80) in Z80 by (cbn; lia) end.
    rewrite <- SEG in Z16, Z64, Z80.
    rewrite SEG.
    eapply SR_mono.
    { apply (sr_chain LF FRc FN MSC L A regs mem md bnd empty_list empty_list empty_list 0
               (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
               (Z_to_bv 64 0) pad j SEG PRE INIT RO PLR Hj4 R10 Z0 (sr_zero_list L A mem _ false Z16) Z32 PAD
               (sr_zero_list L A mem _ true Z64) (sr_zero_list L A mem _ true Z80)).
      - constructor.
      - left. reflexivity.
      - exact RES. }
    intros c' (L' & A' & regs' & mem' & md' & -> & RP & INIT' & RO' & ZR & RES' & B1 & B2 & BE).
    exists L', A', regs', mem', md'.
    split; [reflexivity|].
    split; [apply (Hrp _ _ _ _ _ _ _ RP); intros q []|].
    split; [exact INIT'|]. split; [exact RO'|]. split; [exact ZR|].
    split.
    + intros X. exfalso. rewrite <- SEG in S2. exact (sr_zero_not_src L A mem HA h S2 X).
    + intros _. split; [exact RES' | exact (BE eq_refl)].
Qed.

End SRB.
