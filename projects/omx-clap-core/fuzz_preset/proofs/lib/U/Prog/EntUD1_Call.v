From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Tac Bytes Step ZBridge Image.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct PjSame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import pj_get_c pj_get_str_c EntUD1_Base.
Import ListNotations.
Open Scope Z_scope.

Section C.
Hypothesis HGET : pj_get_contract.
Hypothesis HGSTR : pj_get_str_contract.

Lemma ud1_get : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (lblk : Z -> Z -> Prop) (S lo k : Z) (K : list Z)
    (t : jv) (D : list (Z * Z)),
  sp = Z_to_bv 64 S -> a0 = Z_to_bv 64 (S + 8) -> a1 = Z_to_bv 64 k ->
  152 <= S -> S mod 16 = 0 -> ud1_blk lblk S -> ud1_inv m0 m S lo ->
  pj_node rsegs m0 lblk (S + 8) t D -> ud1_key k K ->
  evt rsegs (fun ms' => exists (t0' t1' t2' r a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                               (m' : word -> option byte) (z : Z),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs) /\
      ud1_inv m0 m' S lo /\ r = Z_to_bv 64 z /\ pj_get_res m0 lblk (S + 8) t D K z)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 PJ_GET) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m lblk
    S lo k K t D Esp E0 E1 HS H16 HB (MU & WM & MI & ST & HLo & SL) HN HK.
  assert (HS72 : S + 72 <= 2 ^ 64) by (destruct SL as (_ & ? & _); lia).
  assert (HSU : bv_unsigned sp = S) by (subst sp; apply unsigned_lit; lia).
  pose proof (ud1_root_out m0 lblk S t D HB HN) as HO.
  pose proof (ud1_node_tr _ m0 m lblk (S + 8) t D HN MU HO) as HNm.
  pose proof (ud1_key_apart m lo S 80 k K MI ST ltac:(lia) ltac:(lia) HK) as HKA.
  eapply evt_mono.
  { apply (HGET ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m lblk (S + 8) k K t D lo E0 E1 (or_intror HNm) (ud1_key_cb m k K MI HK)); rewrite ?HSU.
    - intros a n Ha. destruct (HB a n Ha) as (A1 & A2 & A3 & A4). cbn [disjoint_from] in A4 |- *.
      split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [lia | exact I].
    - exact H16.
    - exact ST.
    - lia.
    - cbn [disjoint_from]. split; [lia|]. split; [lia | exact I].
    - exact MI. }
  intros ms' (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MU' & WM' & MI' & ST' & _ & Hr).
  rewrite HSU in MU', ST'.
  destruct Hr as [(Ho & _)|(_ & HN' & z & Er & HR)]; [lia|].
  pose proof (ud1_munch_call S 80 m0 m m' ltac:(lia) MU MU') as MU2.
  exists t0', t1', t2', r, a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', z.
  split; [exact E|]. split.
  - apply (ud1_inv_mk m0 m' S lo MU2 (wmono_trans rsegs m0 m m' WM WM') MI' ST' HLo).
    apply (stk_transport_disjoint rsegs [(S - 80, S)] m m' (S + 64) (S + 72) SL MU' WM').
    cbn [disjoint_from]. split; [lia | exact I].
  - split; [exact Er|].
    exact (ud1_res_tr _ m' m0 lblk (S + 8) t D K z HN' HR (ud1_munch_sym _ m0 m' MU2) HO).
Qed.

Lemma ud1_gstr : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m0 m : word -> option byte) (lblk : Z -> Z -> Prop) (S lo o k : Z) (K : list Z),
  sp = Z_to_bv 64 S -> a0 = Z_to_bv 64 o -> a1 = Z_to_bv 64 k ->
  152 <= S -> S mod 16 = 0 -> ud1_blk lblk S -> ud1_inv m0 m S lo ->
  (o = 0 \/ exists v Dv, pj_node rsegs m0 lblk o v Dv /\
     (forall x, pj_foot o Dv x -> outside [(S - 96, S); (S + 64, S + 72)] x)) ->
  ud1_key k K ->
  evt rsegs (fun ms' => exists (t0' t1' t2' r a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                               (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 r a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs) /\
      ud1_inv m0 m' S lo)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 PJ_GET_STR) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m lblk
    S lo o k K Esp E0 E1 HS H16 HB (MU & WM & MI & ST & HLo & SL) Ho HK.
  assert (HS72 : S + 72 <= 2 ^ 64) by (destruct SL as (_ & ? & _); lia).
  assert (HSU : bv_unsigned sp = S) by (subst sp; apply unsigned_lit; lia).
  pose proof (ud1_key_apart m lo S 96 k K MI ST ltac:(lia) ltac:(lia) HK) as HKA.
  assert (HX : exists v Dv, (o = 0 \/ pj_node rsegs m lblk o v Dv) /\ (S <= o \/ o + 56 <= S - 96)).
  { destruct Ho as [Ho|(v & Dv & HNv & HOv)].
    - exists JNull, []. split; [left; exact Ho | right; lia].
    - exists v, Dv. split; [right; exact (ud1_node_tr _ m0 m lblk o v Dv HNv MU HOv)|].
      assert (HA : forall x, o <= x < o + 56 -> ~ (S - 96 <= x < S)).
      { intros x Hx. pose proof (HOv x (or_introl Hx)) as Hq. cbn [outside] in Hq. exact (proj1 Hq). }
      destruct (ud1_apart o 56 (S - 96) S ltac:(lia) ltac:(lia) HA) as [E|E]; [right|left]; lia. }
  destruct HX as (v & Dv & HNo & HDo).
  eapply evt_mono.
  { apply (HGSTR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m lblk o k K v Dv lo E0 E1 HNo (ud1_key_cb m k K MI HK)); rewrite ?HSU.
    - intros a n Ha. destruct (HB a n Ha) as (A1 & A2 & A3 & A4). cbn [disjoint_from] in A4 |- *.
      split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [lia | exact I].
    - exact H16.
    - exact ST.
    - lia.
    - cbn [disjoint_from]. split; [lia|]. split; [lia | exact I].
    - exact MI. }
  intros ms' (t0' & t1' & t2' & r & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
              E & MU' & WM' & MI' & ST' & _ & _).
  rewrite HSU in MU', ST'.
  pose proof (ud1_munch_call S 96 m0 m m' ltac:(lia) MU MU') as MU2.
  exists t0', t1', t2', r, a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [exact E|].
  apply (ud1_inv_mk m0 m' S lo MU2 (wmono_trans rsegs m0 m m' WM WM') MI' ST' HLo).
  apply (stk_transport_disjoint rsegs [(S - 96, S)] m m' (S + 64) (S + 72) SL MU' WM').
  cbn [disjoint_from]. split; [lia | exact I].
Qed.

End C.
