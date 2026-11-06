From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require PropExec.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0 MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import strlen_c write_value_blocks.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import put_kb put.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Open Scope Z_scope.

Definition wv_exitr (pc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
  (fc : bv 32) (lo : Z) (m : word -> option byte) (R : word -> word -> word -> Prop) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F pc fc None m' (seg_rom rsegs) /\
    R a0 a1 a2 /\ munch [(bv_unsigned sp - WV_FRAME, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
    stk rsegs m' lo (bv_unsigned sp).

Definition wv_insider (sp : word) (lo : Z) (m m' : word -> option byte) (junk : list byte) (d : word) (c16 : cell)
  (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : Prop :=
  munch [(bv_unsigned sp - WV_FRAME, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
  stk rsegs m' lo (bv_unsigned sp - WV_FRAME) /\ wv_frame m' sp junk d c16 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.

Lemma wve_node_norm : forall m v ty str kids keys n pa pb, ro_agree rsegs m -> wv_node m v ty str kids keys n pa pb ->
  (forall i, 0 <= i < 56 -> ro_addr rsegs (wa (v + i)) = false) ->
  wv_node (normalize rsegs m) v ty str kids keys n pa pb.
Proof.
  intros m v ty str kids keys n pa pb RO ND NR. unfold wv_node in *. apply (rw_cells_norm _ _ _ RO ND).
  intros i Hi. cbn [cells_size csize Nat.add] in Hi. apply NR. lia.
Qed.

Lemma wve_stk_norm : forall m lo hi, ro_agree rsegs m -> stk rsegs m lo hi -> IMG_TOP <= lo ->
  stk rsegs (normalize rsegs m) lo hi.
Proof.
  intros m lo hi RO ST Hlo. pose proof ST as (_ & Hhi & _). apply (stk_norm _ _ _ RO ST).
  intros a Ha. apply ro_false_hi. lia.
Qed.

Lemma wve_frame_norm : forall m sp junk d c16 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11, ro_agree rsegs m ->
  IMG_TOP <= bv_unsigned sp - WV_FRAME ->
  wv_frame m sp junk d c16 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ->
  wv_frame (normalize rsegs m) sp junk d c16 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.
Proof.
  intros m sp junk d c16 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 RO Hlo FR. unfold wv_frame in *.
  pose proof (rw_cells_bound _ _ _ _ FR) as RV.
  apply (rw_cells_norm _ _ _ RO FR). intros i Hi. apply ro_false_hi. lia.
Qed.

Lemma wve_inside_rel : forall sp lo m m0 m' m0' junk d c16 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11,
  mem_rel rsegs m m0 -> mem_rel rsegs m' m0' -> ro_same rsegs m m' ->
  wv_inside sp lo m0 m0' junk d c16 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ->
  wv_insider sp lo m m' junk d c16 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.
Proof.
  intros sp lo m m0 m' m0' junk d c16 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 HR HR' HO (MU & WM & _ & ST & FR).
  unfold wv_frame in *.
  split; [exact (munch_rel rsegs _ m m0 m' m0' HR HR' HO MU)|].
  split; [exact (wmono_rel rsegs m m0 m' m0' HR HR' HO WM)|].
  split; [exact (stk_rel _ _ _ _ HR' ST) | exact (rw_cells_rel _ _ _ _ HR' FR)].
Qed.

Lemma wve_exit_norm : forall (pc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (fc : bv 32) (lo : Z) (m : word -> option byte) (R : word -> word -> word -> Prop) R0 F0 pc0 fc0 rv0,
  ro_agree rsegs m ->
  Exec.evt rsegs (wv_exit pc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo (normalize rsegs m) R)
    (MS R0 F0 pc0 fc0 rv0 (normalize rsegs m) (PropExec.seg_rom rsegs)) ->
  Exec.evt rsegs (fun x => wv_exitr pc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m R x /\
                           ro_agree rsegs (ms_mem x))
    (MS R0 F0 pc0 fc0 rv0 m (PropExec.seg_rom rsegs)).
Proof.
  intros pc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m R R0 F0 pc0 fc0 rv0 RO H.
  pose proof (mem_rel_normalize rsegs m RO) as HN.
  eapply evt_mono; [exact (evt_normalize rsegs _ R0 F0 pc0 fc0 rv0 m _ wx_apart_img RO H)|].
  intros x (x0 & (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m0 & E0 & HR0 & MU & WM & _
    & ST) & HR & HO).
  subst x0. pose proof (ms_rel_MS _ _ _ _ _ _ _ _ HR) as EX.
  destruct HR as (_ & _ & _ & _ & _ & _ & _ & HM). change (mem_rel rsegs (ms_mem x) m0) in HM.
  split; [|exact (ro_agree_same rsegs m _ RO HO)].
  exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, (ms_mem x).
  split; [exact EX|]. split; [exact HR0|].
  split; [exact (munch_rel rsegs _ m (normalize rsegs m) (ms_mem x) m0 HN HM HO MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) (ms_mem x) m0 HN HM HO WM)|].
  exact (stk_rel _ _ _ _ HM ST).
Qed.

Lemma wv_null_ro : forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo o v pretty depth str kids keys n : Z)
  (pa pb : list byte),
  ro_agree rsegs m -> wv_node m v 0 str kids keys n pa pb ->
  (forall i, 0 <= i < 56 -> ro_addr rsegs (wa (v + i)) = false) -> 0 < v -> v mod 8 = 0 ->
  stk rsegs m lo (bv_unsigned sp) -> lo + WV_FRAME <= bv_unsigned sp -> IMG_TOP <= lo ->
  (v + 56 <= bv_unsigned sp - WV_FRAME \/ bv_unsigned sp <= v) ->
  Exec.evt rsegs (fun x => wv_exitr (Z_to_bv 64 WV_PUT) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m
               (fun x0 x1 x2 => x0 = Z_to_bv 64 o /\ x1 = Z_to_bv 64 WV_S_NULL /\ x2 = Z_to_bv 64 4) x /\
             ro_agree rsegs (ms_mem x))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 v) (Z_to_bv 64 pretty) (Z_to_bv 64 depth)
           a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 WRITE_VALUE) fc None m (PropExec.seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo o v pretty depth str kids keys n pa pb RO ND NR HV HA ST LO TOP DV.
  apply wve_exit_norm; [exact RO|].
  eapply wv_null; [apply mem_inv_normalize | exact (wve_node_norm _ _ _ _ _ _ _ _ _ RO ND NR) | exact HV | exact HA
                  | exact (wve_stk_norm _ _ _ RO ST TOP) | exact LO | exact DV].
Qed.

Lemma wv_false_ro : forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo o v pretty depth str kids keys n : Z)
  (pa pb : list byte),
  ro_agree rsegs m -> wv_node m v 1 str kids keys n pa pb ->
  (forall i, 0 <= i < 56 -> ro_addr rsegs (wa (v + i)) = false) -> 0 < v -> v mod 8 = 0 ->
  stk rsegs m lo (bv_unsigned sp) -> lo + WV_FRAME <= bv_unsigned sp -> IMG_TOP <= lo ->
  (v + 56 <= bv_unsigned sp - WV_FRAME \/ bv_unsigned sp <= v) ->
  Exec.evt rsegs (fun x => wv_exitr (Z_to_bv 64 WV_PUT) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m
               (fun x0 x1 x2 => x0 = Z_to_bv 64 o /\ x1 = Z_to_bv 64 WV_S_FALSE /\ x2 = Z_to_bv 64 5) x /\
             ro_agree rsegs (ms_mem x))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 v) (Z_to_bv 64 pretty) (Z_to_bv 64 depth)
           a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 WRITE_VALUE) fc None m (PropExec.seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo o v pretty depth str kids keys n pa pb RO ND NR HV HA ST LO TOP DV.
  apply wve_exit_norm; [exact RO|].
  eapply wv_false; [apply mem_inv_normalize | exact (wve_node_norm _ _ _ _ _ _ _ _ _ RO ND NR) | exact HV | exact HA
                   | exact (wve_stk_norm _ _ _ RO ST TOP) | exact LO | exact DV].
Qed.

Lemma wv_true_ro : forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo o v pretty depth str kids keys n : Z)
  (pa pb : list byte),
  ro_agree rsegs m -> wv_node m v 2 str kids keys n pa pb ->
  (forall i, 0 <= i < 56 -> ro_addr rsegs (wa (v + i)) = false) -> 0 < v -> v mod 8 = 0 ->
  stk rsegs m lo (bv_unsigned sp) -> lo + WV_FRAME <= bv_unsigned sp -> IMG_TOP <= lo ->
  (v + 56 <= bv_unsigned sp - WV_FRAME \/ bv_unsigned sp <= v) ->
  Exec.evt rsegs (fun x => wv_exitr (Z_to_bv 64 WV_PUT) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m
               (fun x0 x1 x2 => x0 = Z_to_bv 64 o /\ x1 = Z_to_bv 64 WV_S_TRUE /\ x2 = Z_to_bv 64 4) x /\
             ro_agree rsegs (ms_mem x))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 v) (Z_to_bv 64 pretty) (Z_to_bv 64 depth)
           a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 WRITE_VALUE) fc None m (PropExec.seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo o v pretty depth str kids keys n pa pb RO ND NR HV HA ST LO TOP DV.
  apply wve_exit_norm; [exact RO|].
  eapply wv_true; [apply mem_inv_normalize | exact (wve_node_norm _ _ _ _ _ _ _ _ _ RO ND NR) | exact HV | exact HA
                  | exact (wve_stk_norm _ _ _ RO ST TOP) | exact LO | exact DV].
Qed.

Lemma wv_str_ro : forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo o v pretty depth str kids keys n : Z)
  (pa pb : list byte),
  ro_agree rsegs m -> wv_node m v 4 str kids keys n pa pb ->
  (forall i, 0 <= i < 56 -> ro_addr rsegs (wa (v + i)) = false) -> 0 < v -> v mod 8 = 0 -> 0 <= str < 2^64 ->
  stk rsegs m lo (bv_unsigned sp) -> lo + WV_FRAME <= bv_unsigned sp -> IMG_TOP <= lo ->
  (v + 56 <= bv_unsigned sp - WV_FRAME \/ bv_unsigned sp <= v) ->
  Exec.evt rsegs (fun x => wv_exitr (Z_to_bv 64 WV_PUT_STRING) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m
               (fun x0 x1 _ => x0 = Z_to_bv 64 o /\ x1 = Z_to_bv 64 (wv_nz str WV_S_EMPTY)) x /\
             ro_agree rsegs (ms_mem x))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 v) (Z_to_bv 64 pretty) (Z_to_bv 64 depth)
           a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 WRITE_VALUE) fc None m (PropExec.seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo o v pretty depth str kids keys n pa pb RO ND NR HV HA HS ST LO TOP DV.
  apply wve_exit_norm; [exact RO|].
  eapply wv_str; [apply mem_inv_normalize | exact (wve_node_norm _ _ _ _ _ _ _ _ _ RO ND NR) | exact HV | exact HA
                 | exact HS | exact (wve_stk_norm _ _ _ RO ST TOP) | exact LO | exact DV].
Qed.

Lemma wv_open_call_ro : forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo o v pretty depth ty str kids keys n : Z)
  (pa pb : list byte),
  ro_agree rsegs m -> wv_node m v ty str kids keys n pa pb ->
  (forall i, 0 <= i < 56 -> ro_addr rsegs (wa (v + i)) = false) -> (ty = 5 \/ ty = 6) -> 0 < v -> v mod 8 = 0 ->
  stk rsegs m lo (bv_unsigned sp) -> lo + WV_FRAME <= bv_unsigned sp -> IMG_TOP <= lo ->
  (v + 56 <= bv_unsigned sp - WV_FRAME \/ bv_unsigned sp <= v) ->
  Exec.evt rsegs
    (fun x => (exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte)
                      (junk j16 : list byte),
       x = MS (mkR (Z_to_bv 64 WV_R_OPEN) (Z_to_bv 64 (bv_unsigned sp - WV_FRAME)) gp tp t0' t1' t2'
                   (Z_to_bv 64 o) (Z_to_bv 64 v) (Z_to_bv 64 o) (Z_to_bv 64 (wv_open ty)) (Z_to_bv 64 1)
                   a3' a4' a5' a6' a7' s2 (Z_to_bv 64 pretty) s4 s5 s6 s7 s8 s9 s10 s11
                   t3' t4' t5' t6')
              F (Z_to_bv 64 WV_PUT) fc None m' (PropExec.seg_rom rsegs) /\
       wv_insider sp lo m m' junk (Z_to_bv 64 depth) (CB 8 j16) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 /\
       wv_node m' v ty str kids keys n pa pb) /\ ro_agree rsegs (ms_mem x))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 v) (Z_to_bv 64 pretty) (Z_to_bv 64 depth)
           a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 WRITE_VALUE) fc None m (PropExec.seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo o v pretty depth ty str kids keys n pa pb RO ND NR HT HV HA ST LO TOP DV.
  pose proof (mem_rel_normalize rsegs m RO) as HN.
  eapply evt_mono.
  { eapply (evt_normalize rsegs); [exact wx_apart_img | exact RO |].
    eapply wv_open_call; [apply mem_inv_normalize | exact (wve_node_norm _ _ _ _ _ _ _ _ _ RO ND NR) | exact HT
                         | exact HV | exact HA | exact (wve_stk_norm _ _ _ RO ST TOP) | exact LO | exact DV]. }
  intros x (x0 & (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0 & junk & j16 & E0 & INS
    & ND0) & HR & HO).
  subst x0. pose proof (ms_rel_MS _ _ _ _ _ _ _ _ HR) as EX.
  destruct HR as (_ & _ & _ & _ & _ & _ & _ & HM). change (mem_rel rsegs (ms_mem x) m0) in HM.
  split; [|exact (ro_agree_same rsegs m _ RO HO)].
  exists t0', t1', t2', a3', a4', a5', a6', a7', t3', t4', t5', t6', (ms_mem x), junk, j16.
  split; [exact EX|].
  split; [eapply wve_inside_rel; [exact HN | exact HM | exact HO | exact INS] | exact (rw_cells_rel _ _ _ _ HM ND0)].
Qed.

Lemma wv_after_open_empty_ro : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
  (fc : bv 32) (ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 g18 g20 g21 g22 g23 g24 g25 g26 g27 t3 t4 t5 t6 : word)
  (m : word -> option byte) (lo o v pretty ty str kids keys : Z) (pa pb junk j16 : list byte) (d : word),
  ro_agree rsegs m -> wv_node m v ty str kids keys 0 pa pb ->
  (forall i, 0 <= i < 56 -> ro_addr rsegs (wa (v + i)) = false) -> 0 <= ty < 2^31 -> 0 <= pretty < 2^64 ->
  wv_frame m sp junk d (CB 8 j16) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ->
  stk rsegs m lo (bv_unsigned sp - WV_FRAME) -> lo + WV_FRAME <= bv_unsigned sp -> IMG_TOP <= lo ->
  (v + 56 <= bv_unsigned sp - WV_FRAME \/ bv_unsigned sp <= v) ->
  Exec.evt rsegs (fun x => wv_exitr (Z_to_bv 64 WV_PUT) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m
               (fun x0 x1 x2 => x0 = Z_to_bv 64 o /\ x1 = Z_to_bv 64 (wv_close ty) /\ x2 = Z_to_bv 64 1) x /\
             ro_agree rsegs (ms_mem x))
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp - WV_FRAME)) gp tp t0 t1 t2 (Z_to_bv 64 o) (Z_to_bv 64 v)
           a0 a1 a2 a3 a4 a5 a6 a7 g18 (Z_to_bv 64 pretty) g20 g21 g22 g23 g24 g25 g26 g27 t3 t4 t5 t6)
        F (Z_to_bv 64 WV_R_OPEN) fc None m (PropExec.seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
    g18 g20 g21 g22 g23 g24 g25 g26 g27 t3 t4 t5 t6 m lo o v pretty ty str kids keys pa pb junk j16 d
    RO ND NR HT HP FR ST LO TOP DV.
  pose proof (fun H => wve_frame_norm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RO H FR) as FRN. specialize (FRN ltac:(lia)).
  apply wve_exit_norm; [exact RO|].
  eapply wv_after_open_empty; [apply mem_inv_normalize | exact (wve_node_norm _ _ _ _ _ _ _ _ _ RO ND NR) | exact HT
    | exact HP | exact FRN | exact (wve_stk_norm _ _ _ RO ST TOP) | exact LO | exact DV].
Qed.

Lemma wv_after_open_first_ro : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
  (fc : bv 32) (ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 g18 g20 g21 g22 g23 g24 g25 g26 g27 t3 t4 t5 t6 : word)
  (m : word -> option byte) (lo o v pretty depth ty str kids keys n : Z) (pa pb junk j16 : list byte),
  ro_agree rsegs m -> wv_node m v ty str kids keys n pa pb ->
  (forall i, 0 <= i < 56 -> ro_addr rsegs (wa (v + i)) = false) ->
  0 < n < 2^64 -> 0 <= pretty < 2^64 -> 0 <= depth -> depth + 1 < 2^31 ->
  wv_frame m sp junk (Z_to_bv 64 depth) (CB 8 j16) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ->
  stk rsegs m lo (bv_unsigned sp - WV_FRAME) -> lo + WV_FRAME <= bv_unsigned sp -> IMG_TOP <= lo ->
  (v + 56 <= bv_unsigned sp - WV_FRAME \/ bv_unsigned sp <= v) ->
  Exec.evt rsegs (fun x => (exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      x = wv_ls WV_INDENT (Z_to_bv 64 WV_R_INDENT) sp gp tp t0' t1' t2' (Z_to_bv 64 o) (Z_to_bv 64 pretty)
            (Z_to_bv 64 (depth + 1)) a3' a4' a5' a6' a7' t3' t4' t5' t6' F fc o v pretty depth 0 m' /\
      wv_insider sp lo m m' junk (Z_to_bv 64 depth) (C8 (Z_to_bv 64 (wv_sep pretty))) ra s0 s1 s2 s3 s4 s5
        s6 s7 s8 s9 s10 s11 /\
      wv_node m' v ty str kids keys n pa pb) /\ ro_agree rsegs (ms_mem x))
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp - WV_FRAME)) gp tp t0 t1 t2 (Z_to_bv 64 o) (Z_to_bv 64 v)
           a0 a1 a2 a3 a4 a5 a6 a7 g18 (Z_to_bv 64 pretty) g20 g21 g22 g23 g24 g25 g26 g27 t3 t4 t5 t6)
        F (Z_to_bv 64 WV_R_OPEN) fc None m (PropExec.seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
    g18 g20 g21 g22 g23 g24 g25 g26 g27 t3 t4 t5 t6 m lo o v pretty depth ty str kids keys n pa pb junk j16
    RO ND NR HN HP HD HD1 FR ST LO TOP DV.
  pose proof (mem_rel_normalize rsegs m RO) as HN0.
  pose proof (fun H => wve_frame_norm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RO H FR) as FRN. specialize (FRN ltac:(lia)).
  eapply evt_mono.
  { eapply (evt_normalize rsegs); [exact wx_apart_img | exact RO |].
    eapply wv_after_open_first; [apply mem_inv_normalize | exact (wve_node_norm _ _ _ _ _ _ _ _ _ RO ND NR) | exact HN
      | exact HP | exact HD | exact HD1 | exact FRN | exact (wve_stk_norm _ _ _ RO ST TOP) | exact LO | exact DV]. }
  intros x (x0 & (t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0 & E0 & INS & ND0)
    & HR & HO).
  subst x0. unfold wv_ls in HR. pose proof (ms_rel_MS _ _ _ _ _ _ _ _ HR) as EX.
  destruct HR as (_ & _ & _ & _ & _ & _ & _ & HM). change (mem_rel rsegs (ms_mem x) m0) in HM.
  split; [|exact (ro_agree_same rsegs m _ RO HO)].
  exists t0', t1', t2', a3', a4', a5', a6', a7', t3', t4', t5', t6', (ms_mem x).
  split; [unfold wv_ls; exact EX|].
  split; [eapply wve_inside_rel; [exact HN0 | exact HM | exact HO | exact INS] | exact (rw_cells_rel _ _ _ _ HM ND0)].
Qed.

Lemma wv_close_tail_ro : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
  (fc : bv 32) (ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 t3 t4 t5 t6 : word)
  (m : word -> option byte) (lo o v ty str kids keys n : Z) (pa pb junk : list byte) (d : word) (c16 : cell),
  ro_agree rsegs m -> wv_node m v ty str kids keys n pa pb ->
  (forall i, 0 <= i < 56 -> ro_addr rsegs (wa (v + i)) = false) -> 0 <= ty < 2^31 ->
  wv_frame m sp junk d c16 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ->
  ((exists j, c16 = CB 8 j) \/ (exists w, c16 = C8 w)) ->
  stk rsegs m lo (bv_unsigned sp - WV_FRAME) -> lo + WV_FRAME <= bv_unsigned sp -> IMG_TOP <= lo ->
  Exec.evt rsegs (fun x => wv_exitr (Z_to_bv 64 WV_PUT) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m
               (fun x0 x1 x2 => x0 = Z_to_bv 64 o /\ x1 = Z_to_bv 64 (wv_close ty) /\ x2 = Z_to_bv 64 1) x /\
             ro_agree rsegs (ms_mem x))
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp - WV_FRAME)) gp tp t0 t1 t2 (Z_to_bv 64 o) (Z_to_bv 64 v)
           a0 a1 a2 a3 a4 a5 a6 a7 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 t3 t4 t5 t6)
        F (Z_to_bv 64 WV_R_CLOSE) fc None m (PropExec.seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
    g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 t3 t4 t5 t6 m lo o v ty str kids keys n pa pb junk d c16
    RO ND NR HT FR C16 ST LO TOP.
  pose proof (fun H => wve_frame_norm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RO H FR) as FRN. specialize (FRN ltac:(lia)).
  apply wve_exit_norm; [exact RO|].
  eapply wv_close_tail; [apply munch_refl | apply wmono_refl | apply mem_inv_normalize
    | exact (wve_node_norm _ _ _ _ _ _ _ _ _ RO ND NR) | exact HT | exact FRN | exact C16
    | exact (wve_stk_norm _ _ _ RO ST TOP) | exact LO].
Qed.

Lemma wve_num_mi : strlen_contract -> forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo o v pretty depth str kids keys n : Z)
  (pa pb : list byte) (txt : list Z) (slack : list byte),
  mem_inv rsegs m -> wv_node m v 3 str kids keys n pa pb -> 0 < v -> v mod 8 = 0 -> 0 < str < 2 ^ 64 ->
  stk rsegs m lo (bv_unsigned sp) -> lo + WV_FRAME <= bv_unsigned sp -> IMG_TOP <= lo ->
  (v + 56 <= bv_unsigned sp - WV_FRAME \/ bv_unsigned sp <= v) ->
  bytes_at rsegs m str (map (Z_to_bv 8) txt ++ Z_to_bv 8 0 :: slack) -> Forall (fun c => 0 < c < 256) txt ->
  (- (str + Z.of_nat (length txt) + 1)) mod 8 <= Z.of_nat (length slack) ->
  str + Z.of_nat (length txt) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - WV_FRAME ->
  Exec.evt rsegs (wv_exit (Z_to_bv 64 WV_PUT) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m
               (fun x0 x1 x2 => x0 = Z_to_bv 64 o /\ x1 = Z_to_bv 64 str /\ x2 = Z_to_bv 64 (Z.of_nat (length txt))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 v) (Z_to_bv 64 pretty) (Z_to_bv 64 depth)
           a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 WRITE_VALUE) fc None m (PropExec.seg_rom rsegs)).
Proof.
  intros SC ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo o v pretty depth str kids keys n pa pb txt slack MI ND HV HA HS ST LO TOP DV BS TXT AL TL.
  unfold strlen_contract in SC.
  assert (NZ : wv_nz str WV_S_ZERO = str) by (unfold wv_nz; rewrite (proj2 (Z.eqb_neq str 0)) by lia; reflexivity).
  assert (NONUL : ~ In (Z_to_bv 8 0) (map (Z_to_bv 8) txt)).
  { intros Hin. apply in_map_iff in Hin as (c & Ec & Hc). rewrite Forall_forall in TXT.
    specialize (TXT c Hc). cbv beta in TXT.
    apply (f_equal bv_unsigned) in Ec. rewrite !Z_to_bv_unsigned in Ec. unfold bv_wrap in Ec.
    change (bv_modulus 8) with 256 in Ec. rewrite (Z.mod_small c 256) in Ec by lia. cbn in Ec. lia. }
  eapply evt_cut; [eapply wv_num_call; [exact MI | exact ND | exact HV | exact HA | lia | exact ST | exact LO
    | exact DV]|].
  intros x1 (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 & junk & j16 & E1
    & (MU1 & WM1 & MI1 & ST1 & FR1) & ND1).
  subst x1. rewrite NZ. unfold wv_frame in FR1.
  assert (B1 : bytes_at rsegs m1 (bv_unsigned (Z_to_bv 64 str)) (map (Z_to_bv 8) txt ++ Z_to_bv 8 0 :: slack)).
  { rewrite unsigned_lit by lia. apply (bytes_at_transport rsegs _ m m1 _ _ BS MU1). cbn [disjoint_from].
    rewrite length_app, length_map. cbn [length]. split; [lia | exact I]. }
  eapply evt_cut.
  { change (Z_to_bv 64 WV_STRLEN) with (Z_to_bv 64 STRLEN).
    eapply SC with (str := map (Z_to_bv 8) txt) (slack := slack);
      [exact B1 | exact NONUL | rewrite unsigned_lit by lia; rewrite length_map; exact AL | exact MI1]. }
  intros x2 (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & E2 & MU2 & WM2 & MI2 & B2).
  subst x2.
  rewrite (ret_pc_even WV_R_STRLEN) by (unfold WV_R_STRLEN; first [reflexivity | lia]).
  assert (FR2 : wv_frame m2 sp junk (Z_to_bv 64 depth) (CB 8 j16) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
    by exact (rw_cells_transport rsegs [] m1 m2 _ _ FR1 MU2 WM2 I).
  assert (ST2 : stk rsegs m2 lo (bv_unsigned sp - WV_FRAME))
    by exact (stk_transport_disjoint rsegs [] m1 m2 _ _ ST1 MU2 WM2 I).
  eapply evt_mono; [eapply wv_num_tail; [exact MI2 | exact FR2 | left; eexists; reflexivity | exact ST2 | exact LO]|].
  intros x3 (w0 & w1 & w2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & w3 & w4 & w5 & w6 & m3 & E3 & (Y0 & Y1 & Y2)
    & MU3 & WM3 & MI3 & ST3).
  exists w0, w1, w2, c0, c1, c2, c3, c4, c5, c6, c7, w3, w4, w5, w6, m3.
  split; [exact E3|].
  split; [rewrite length_map in Y2; cbv beta; split; [exact Y0 | split; [exact Y1 | exact Y2]]|].
  split; [exact (munch_trans _ _ _ _ (munch_trans _ _ _ _ MU1 (munch_weaken [] _ _ _ (fun _ _ => I) MU2)) MU3)|].
  split; [exact (wmono_trans rsegs _ _ _ (wmono_trans rsegs _ _ _ WM1 WM2) WM3)|].
  split; [exact MI3 | exact ST3].
Qed.

Lemma wv_num_ro : strlen_contract -> forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo o v pretty depth str kids keys n : Z)
  (pa pb : list byte) (txt : list Z) (slack : list byte),
  ro_agree rsegs m -> wv_node m v 3 str kids keys n pa pb ->
  (forall i, 0 <= i < 56 -> ro_addr rsegs (wa (v + i)) = false) -> 0 < v -> v mod 8 = 0 -> 0 < str < 2 ^ 64 ->
  stk rsegs m lo (bv_unsigned sp) -> lo + WV_FRAME <= bv_unsigned sp -> IMG_TOP <= lo ->
  (v + 56 <= bv_unsigned sp - WV_FRAME \/ bv_unsigned sp <= v) ->
  bytes_at rsegs m str (map (Z_to_bv 8) txt ++ Z_to_bv 8 0 :: slack) -> Forall (fun c => 0 < c < 256) txt ->
  (- (str + Z.of_nat (length txt) + 1)) mod 8 <= Z.of_nat (length slack) ->
  str + Z.of_nat (length txt) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - WV_FRAME ->
  Exec.evt rsegs (fun x => wv_exitr (Z_to_bv 64 WV_PUT) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m
               (fun x0 x1 x2 => x0 = Z_to_bv 64 o /\ x1 = Z_to_bv 64 str /\ x2 = Z_to_bv 64 (Z.of_nat (length txt))) x /\
             ro_agree rsegs (ms_mem x))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 v) (Z_to_bv 64 pretty) (Z_to_bv 64 depth)
           a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 WRITE_VALUE) fc None m (PropExec.seg_rom rsegs)).
Proof.
  intros SC ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo o v pretty depth str kids keys n pa pb txt slack RO ND NR HV HA HS ST LO TOP DV BS TXT AL TL.
  apply wve_exit_norm; [exact RO|].
  eapply (wve_num_mi SC); [apply mem_inv_normalize | exact (wve_node_norm _ _ _ _ _ _ _ _ _ RO ND NR) | exact HV
                          | exact HA | exact HS | exact (wve_stk_norm _ _ _ RO ST TOP) | exact LO | exact TOP
                          | exact DV | exact (bytes_at_normalize rsegs m _ _ RO BS) | exact TXT | exact AL | exact TL].
Qed.
