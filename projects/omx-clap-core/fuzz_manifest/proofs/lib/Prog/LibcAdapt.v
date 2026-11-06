From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import ManifestModel ManifestMem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require strlen_c bcmp_c strncmp_c isalnum_c strncmp LibcNeeds_c.
Import ListNotations.
Open Scope Z_scope.

(* a Theorem Labs lane's contracts imply a Theorem Labs lane's needs (LibcNeeds_c.v) for strlen, bcmp, strncmp and isalnum. *)

Lemma bv64_small_zero : forall v, -255 <= v <= 255 -> (bv_unsigned (Z_to_bv 64 v) = 0 <-> v = 0).
Proof.
  intros v Hv. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
  split; intros H.
  - apply Z.mod_divide in H; [|lia]. destruct H as [k Hk]. lia.
  - subst. reflexivity.
Qed.

Lemma kret_of_same : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m m' (R : word -> Prop)
    t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
  munch [] m m' -> wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m lo (bv_unsigned sp) -> R a0 ->
  kret ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo 0 m [] R
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (ret_pc ra) fc None m' (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m m' R t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    MU WM MI ST HR.
  unfold kret. exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m'.
  refine (conj eq_refl (conj _ (conj WM (conj MI (conj _ HR))))).
  - eapply munch_weaken; [|exact MU]. intros x _. exact I.
  - eapply stk_transport_disjoint; [exact ST|exact MU|exact WM|exact I].
Qed.

Theorem strlen_adapt : strlen_c.strlen_contract -> LibcNeeds_c.strlen_contract.
Proof.
  intros H. unfold LibcNeeds_c.strlen_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo bs slack
    [HB [HF HW]] MI ST.
  eapply evt_mono.
  - apply (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m bs slack
             HB); [|exact HW|exact MI].
    intros Hin. rewrite Forall_forall in HF. apply (HF _ Hin). reflexivity.
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & _).
    apply kret_of_same; try assumption. reflexivity.
Qed.

Lemma memcmp_iff : forall lb rb, length lb = length rb ->
  exists v, memcmp_model lb rb (length lb) = Some v /\ (v = 0 <-> zbytes lb = zbytes rb) /\ -255 <= v <= 255.
Proof.
  unfold zbytes.
  induction lb as [|a lb IH]; intros [|b rb] HL; cbn in HL; try discriminate.
  - exists 0. split; [reflexivity|]. split; [tauto|lia].
  - injection HL as HL. destruct (IH rb HL) as (v & Hv & Hi & Hr).
    pose proof (byte_range a). pose proof (byte_range b).
    cbn [memcmp_model length map].
    destruct (bv_unsigned a =? bv_unsigned b) eqn:E.
    + apply Z.eqb_eq in E. exists v. split; [exact Hv|]. split; [|exact Hr].
      rewrite Hi, E. split; [intros H'; rewrite H'; reflexivity|intros H'; injection H' as H''; exact H''].
    + apply Z.eqb_neq in E. exists (bv_unsigned a - bv_unsigned b). split; [reflexivity|].
      split; [split; [lia|intros H'; injection H' as H1 _; lia]|lia].
Qed.

Theorem bcmp_adapt : bcmp_c.bcmp_contract -> LibcNeeds_c.bcmp_contract.
Proof.
  intros H. unfold LibcNeeds_c.bcmp_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo lb rb
    HL HR NL NR MI ST.
  assert (HLen : length lb = length rb) by lia.
  destruct (memcmp_iff lb rb HLen) as (v & Hv & Hi & Hr).
  assert (HN : Z.to_nat (bv_unsigned a2) = length lb) by lia.
  eapply evt_mono.
  - apply (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lb rb v
             HL HR); [rewrite HN; exact Hv|exact MI].
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & _).
    apply kret_of_same; try assumption. cbv beta. rewrite bv64_small_zero by lia. exact Hi.
Qed.

Lemma strncmp_iff : forall lb rb k,
  Forall (fun b => bv_unsigned b <> 0) lb -> Forall (fun b => bv_unsigned b <> 0) rb ->
  exists v, strncmp_walk (lb ++ [Z_to_bv 8 0]) (rb ++ [Z_to_bv 8 0]) k = Some v
         /\ (v = 0 <-> firstn (S k) (zbytes lb ++ [0]) = firstn (S k) (zbytes rb ++ [0]))
         /\ -255 <= v <= 255.
Proof.
  assert (Z0 : bv_unsigned (Z_to_bv 8 0) = 0) by reflexivity.
  unfold zbytes.
  induction lb as [|a lb IH]; intros [|b rb] k Hl Hr; cbn [app map].
  - rewrite strncmp.walk_stop by (left; exact Z0). rewrite Z0.
    eexists; split; [reflexivity|]. split; [split; intros; [reflexivity|lia]|lia].
  - inversion Hr as [|? ? Hb Hr']; subst. pose proof (byte_range b).
    rewrite strncmp.walk_stop by (left; exact Z0). rewrite Z0.
    eexists; split; [reflexivity|]. cbn [firstn].
    split; [split; [intros; lia|intros H'; injection H' as H1 _; lia]|lia].
  - inversion Hl as [|? ? Ha Hl']; subst. pose proof (byte_range a).
    rewrite strncmp.walk_stop by (right; left; exact Z0). rewrite Z0.
    eexists; split; [reflexivity|]. cbn [firstn].
    split; [split; [intros; lia|intros H'; injection H' as H1 _; lia]|lia].
  - inversion Hl as [|? ? Ha Hl']; subst. inversion Hr as [|? ? Hb Hr']; subst.
    pose proof (byte_range a). pose proof (byte_range b).
    destruct k as [|k].
    + rewrite strncmp.walk_stop by (right; right; left; reflexivity).
      eexists; split; [reflexivity|]. cbn [firstn].
      split; [split; [intros; f_equal; lia|intros H'; injection H' as H1; lia]|lia].
    + destruct (Z.eq_dec (bv_unsigned a) (bv_unsigned b)) as [E|E].
      * rewrite strncmp.walk_go by assumption.
        destruct (IH rb k Hl' Hr') as (v & Hv & Hi & Hrg).
        exists v. split; [exact Hv|]. split; [|exact Hrg].
        change (firstn (S (S k)) (bv_unsigned a :: map bv_unsigned lb ++ [0]))
          with (bv_unsigned a :: firstn (S k) (map bv_unsigned lb ++ [0])).
        change (firstn (S (S k)) (bv_unsigned b :: map bv_unsigned rb ++ [0]))
          with (bv_unsigned b :: firstn (S k) (map bv_unsigned rb ++ [0])).
        rewrite Hi, E. split; [intros H'; rewrite H'; reflexivity|intros H'; injection H' as H''; exact H''].
      * rewrite strncmp.walk_stop by (right; right; right; exact E).
        eexists; split; [reflexivity|]. cbn [firstn].
        split; [split; [intros; lia|intros H'; injection H' as H1 _; lia]|lia].
Qed.

Theorem strncmp_adapt : strncmp_c.strncmp_contract -> LibcNeeds_c.strncmp_contract.
Proof.
  intros H. unfold LibcNeeds_c.strncmp_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo lb rb
    [HL FL] [HR FR] MI ST.
  pose proof (bv_unsigned_in_range 64 a2) as R2. unfold bv_modulus in R2. cbn in R2.
  assert (E : exists v, strncmp_model (lb ++ [Z_to_bv 8 0]) (rb ++ [Z_to_bv 8 0]) (bv_unsigned a2) = Some v /\
     (v = 0 <-> firstn (Z.to_nat (bv_unsigned a2)) (zbytes lb ++ [0])
                = firstn (Z.to_nat (bv_unsigned a2)) (zbytes rb ++ [0])) /\ -255 <= v <= 255).
  { unfold strncmp_model. destruct (Z.eqb_spec (bv_unsigned a2) 0) as [Z|NZ].
    - exists 0. rewrite Z. split; [reflexivity|]. split; [split; intros; reflexivity|lia].
    - destruct (strncmp_iff lb rb (Z.to_nat (bv_unsigned a2 - 1)) FL FR) as (v & Hv & Hi & Hr).
      exists v. split; [exact Hv|]. split; [|exact Hr].
      replace (Z.to_nat (bv_unsigned a2)) with (S (Z.to_nat (bv_unsigned a2 - 1))) by lia. exact Hi. }
  destruct E as (v & Hv & Hi & Hr).
  eapply evt_mono.
  - apply (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             (lb ++ [Z_to_bv 8 0]) (rb ++ [Z_to_bv 8 0]) v HL HR Hv MI).
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & _).
    apply kret_of_same; try assumption. cbv beta. rewrite bv64_small_zero by lia. exact Hi.
Qed.

Theorem isalnum_adapt : isalnum_c.isalnum_contract -> LibcNeeds_c.isalnum_contract.
Proof.
  intros H. unfold LibcNeeds_c.isalnum_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo HC MI ST.
  pose proof (bv_unsigned_in_range 64 a0) as R0. unfold bv_modulus in R0. cbn in R0.
  assert (B1 : bv_unsigned (Z_to_bv 64 1) = 1) by reflexivity.
  assert (B0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
  eapply evt_mono.
  - apply (H ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             (bv_unsigned a0)); [lia|symmetry; apply Z_to_bv_bv_unsigned].
  - intros ms' (a1' & ->).
    apply kret_of_same; [apply munch_refl|apply wmono_refl|exact MI|exact ST|].
    cbv beta. change (isalnum_c.alnum_b (bv_unsigned a0)) with (is_alnum (bv_unsigned a0)).
    destruct (is_alnum (bv_unsigned a0)); rewrite ?B1, ?B0; split; intros; (reflexivity || discriminate || lia).
Qed.
