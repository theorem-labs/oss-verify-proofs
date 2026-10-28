(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From stdpp Require Import base list.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr SysStep.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF AllocSpec SReach.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv HttpAlloc HttpAllocX.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs H_prep H_httpmsg_compare H_httpheader_free H_scanner_get_token H_ListFind H_list_access H_ListAddTail H_freelist H_obj
     H_membuffer_init H_membuffer_destroy H_membuffer_assign H_membuffer_append H_membuffer_append_str H_memptr_cmp H_map_str_to_int
     H_vfmatch_A H_vfmatch_F H_vfmatch_G1 H_match H_phdr_A H_phdr_B H_phdr_C.
Import ListNotations.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Section W.
Context {HCEIL : HasCeiling}.
  Variable AI : alloc_if rsegs.
  Variable AC : alloc_contracts AI.
  Notation L_ := (ai_L rsegs AI).
  Notation K := (ai_K rsegs AI).
  Notation BLK := (block K).
  Notation hdr := (hdr AI).
  Hypothesis LOK : layout_ok AI.
  Hypothesis MALPC : al_malloc_pc L_ = 0x180f0.
  Hypothesis FREEPC : al_free_pc L_ = 0x17fb0.
  Hypothesis REALLOCPC : al_realloc_pc L_ = 0x1995c.
  Hypothesis strncasecmp_spec : strncasecmp_stmt.
  Hypothesis IMGW1 : In (0x10000, 0x2a000)%Z (al_img L_).
  Hypothesis IMGW2 : In (0x2a000, 0x5d000)%Z (al_img L_).

  Hypothesis TABST : exists lo hi, al_client_static L_ lo hi /\ lo <= TAB_HDR /\ TAB_HDR + 528 <= hi.
  Hypothesis ZST : exists lo hi, al_client_static L_ lo hi /\ lo <= ZERO_ADDR /\ ZERO_ADDR + 1 <= hi.

  Variables (P q lo B : Z) (ws : list word).
  Variables (isreq maj min : Z) (cur0 X0 len methE : Z).
  Notation S := (P + 480)%Z.
  Notation L := (P + 288)%Z.
  Notation MB := (P + 400)%Z.
  Hypothesis QLO : (lo + 368 <= q)%Z.
  Hypothesis QLO2 : (lo <= q - 64 - al_stack L_)%Z.
  Hypothesis STK0 : (0 <= al_stack L_)%Z.
  Hypothesis LO0 : (0x5d000 <= lo)%Z.
  Hypothesis CEIL : (alloc_ceiling <= lo)%Z.
  Hypothesis QP : (q + 240 <= P)%Z.
  Hypothesis PB : (P + 504 <= B)%Z.
  Hypothesis BHI : (B < 2^63)%Z.
  Hypothesis P8 : (P mod 8 = 0)%Z.
  Hypothesis WSL : length ws = 66%nat.
  Hypothesis HID : forall i, (0 <= i < 33)%Z -> exists id, nth_error ws (Z.to_nat (2 * i + 1)) = Some (wz id) /\ (0 <= id < 64)%Z.
  Hypothesis TS : table_strings ws 33 lo.
  Hypothesis CUR0 : (0 <= cur0 <= len)%Z.
  Hypothesis X00 : (0 <= X0)%Z.
  Hypothesis XMAX : (X0 + 2 * (len - cur0) <= VMAX)%Z.
  Hypothesis METHE : (0 <= methE <= 11)%Z.

  Notation PRS pc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 gp tp F fc m :=
    (MS (mkR x1 (wz q) gp tp t0 t1 t2 (wz P) (wz S) a0 a1 a2 a3 a4 a5 a6 a7 (wz L) (wz FMT_HDR) (wz TAB_HDR) s5 s6 s7 (wz 4) s9 (wz (-1)) (wz (-104)) t3 t4 t5 t6)
        F (wz pc) fc None m (seg_rom rsegs)).

  Definition WH (okm : option K) (A cap : Z) : list ivl :=
    ((P + 4, P + 8) :: (P + 288, P + 384) :: (P + 440, P + 452) :: (P + 488, P + 496) :: mwin AI okm A cap)%Z.

  Definition ph_post (ra s0w s1w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w gp : word) (F : bvmap 5 word) (fc : bv 32)
      (A cap : Z) (okm : option K) (bs : list byte) (LBK : list BLK) (err hack pos entp clen csz esp : Z) (m0 : mem)
      : ai_PS rsegs AI -> list BLK -> machine_state -> Prop :=
    fun s' LB' ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (r cur' meth' err' pos' : Z) (ns' : list (BLK * Z)) (hs' : list hdr),
      ms' = MS (mkR ra (wz (q + 240)) gp (wz (al_tp L_)) t0 t1 t2 s0w s1w (wz r) a1 a2 a3 a4 a5 a6 a7 s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom rsegs)
      /\ mem_inv rsegs m' /\ stk rsegs m' lo (q + 240) /\ RENV rsegs AI m' B
      /\ (exists e, rw_cells rsegs m' (al_errno L_) [C4 e])
      /\ hpx AI (WH okm A cap) LBK (q + 240) m0 m'
      /\ RHEAP rsegs AI s' LB' m'
      /\ p_scan m' P cur' /\ (cur0 <= cur' <= len)%Z
      /\ p_msg AI m' LB' P A len cap okm bs /\ p_meth m' P meth' /\ (meth' = methE \/ meth' = 11)
      /\ p_ver m' P isreq maj min /\ p_ctl m' P err' hack pos' entp clen csz esp /\ (err' = err \/ err' = 500)
      /\ p_hlist AI m' P ns' hs' (X0 + 2 * (cur' - cur0))
      /\ bsub AI (hl_blocks AI ns' hs' ++ LBK) LB' /\ NoDup (map blk_id (hl_blocks AI ns' hs' ++ LBK))
      /\ u64arr rsegs m' TAB_HDR ws /\ (exists zb, bytes_at rsegs m' ZERO_ADDR [zb])
      /\ (0 <= r <= 5)%Z /\ (r = 4 -> pos' = POS_ENTITY) /\ (r = 4 -> okm <> None).

  Definition ph_statics (m : mem) : Prop := u64arr rsegs m TAB_HDR ws /\ (exists zb, bytes_at rsegs m ZERO_ADDR [zb]).

  #[using="P WSL"] Lemma ph_statics_ext : forall m m',
    (forall a, (TAB_HDR <= a < TAB_HDR + 528 \/ a = ZERO_ADDR)%Z -> m' (wa a) = m (wa a) /\ (wview rsegs m (wa a) <> None -> wview rsegs m' (wa a) <> None)) ->
    ph_statics m -> ph_statics m'.
  Proof.
    intros m m' EXT [[TB TW] [zb ZB]]. pose proof (bytes_at_bound _ _ _ _ TB) as BB. rewrite u64s_length, WSL in BB.
    split; [split|].
    - destruct TB as (B0 & B1 & B2). split; [exact B0|]. split; [exact B1|]. intros i Hi. rewrite <- (B2 i Hi). unfold mrd.
      rewrite u64s_length, WSL in Hi. destruct (EXT (TAB_HDR + Z.of_nat i)%Z ltac:(left; lia)) as [E _]. rewrite E. reflexivity.
    - destruct TW as (W0 & W1 & W2). split; [exact W0|]. split; [exact W1|]. intros i Hi. rewrite WSL in Hi.
      destruct (EXT (TAB_HDR + i)%Z ltac:(left; lia)) as [_ Wi]. apply Wi. apply W2. rewrite WSL. exact Hi.
    - exists zb. destruct ZB as (B0 & B1 & B2). split; [exact B0|]. split; [exact B1|]. intros i Hi. cbn in Hi. rewrite <- (B2 i Hi). unfold mrd.
      destruct (EXT (ZERO_ADDR + Z.of_nat i)%Z ltac:(right; lia)) as [E _]. rewrite E. reflexivity.
  Qed.

  #[using="LOK TABST ZST P q lo QLO LO0 CEIL QP P8 WSL"] Lemma ph_statics_hp : forall (LB : list BLK) SP m m', heap_pres AI LB SP m m' -> ph_statics m -> ph_statics m'.
  Proof.
    intros LB SP m m' HP PS. eapply ph_statics_ext; [| exact PS]. intros a Ha. apply HP; [| right; left].
    - destruct TABST as (l1 & h1 & ST1 & ? & ?). destruct ZST as (l2 & h2 & ST2 & ? & ?).
      destruct (lo_static_img rsegs AI LOK l1 h1 ST1) as (w1 & Hw1 & ? & ?). pose proof (lo_img_ceiling rsegs AI LOK w1 Hw1).
      destruct (lo_static_img rsegs AI LOK l2 h2 ST2) as (w2 & Hw2 & ? & ?). pose proof (lo_img_ceiling rsegs AI LOK w2 Hw2).
      pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8. lia.
    - destruct Ha as [Ha| ->].
      + destruct TABST as (l1 & h1 & ST1 & ? & ?). exists l1, h1. split; [exact ST1| lia].
      + destruct ZST as (l2 & h2 & ST2 & ? & ?). exists l2, h2. split; [exact ST2| lia].
  Qed.

  #[using="HCEIL AI TABST P WSL"] Lemma ph_statics_munch : forall W m m', munch W m m' -> wmono rsegs m m' -> disjoint_from W TAB_HDR 528 -> disjoint_from W ZERO_ADDR 1 ->
    ph_statics m -> ph_statics m'.
  Proof.
    intros W m m' MU WM D1 D2 PS. eapply ph_statics_ext; [| exact PS]. intros a Ha. split; [| intros Hw; apply WM; exact Hw].
    unfold munch in MU. pose proof (MU (wa a)) as E. unfold wa in E |- *. destruct TABST as (l1 & h1 & _ & ? & ?).
    rewrite unsigned_lit in E by lia_v1. apply E. destruct Ha as [Ha| ->]; [eapply disjoint_outside; [exact D1| lia_v1]| eapply disjoint_outside; [exact D2| lia_v1]].
  Qed.

  Definition ph_inv (ra s0w s1w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w : word)
      (A cap : Z) (okm : option K) (bs : list byte) (LBK : list BLK) (err hack pos entp clen csz esp : Z) (m0 : mem)
      (s : ai_PS rsegs AI) (LB : list BLK) (m : mem) (cur meth : Z) (ns : list (BLK * Z)) (hs : list hdr) : Prop :=
    RHEAP rsegs AI s LB m /\ RENV rsegs AI m B /\ mem_inv rsegs m /\ stk rsegs m lo q
    /\ (exists e, rw_cells rsegs m (al_errno L_) [C4 e])
    /\ rw_cells rsegs m (q + 136) (phFS ra s0w s1w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w) /\ phFX q m
    /\ p_scan m P cur /\ (cur0 <= cur <= len)%Z
    /\ p_msg AI m LB P A len cap okm bs /\ p_meth m P meth /\ (meth = methE \/ meth = 11)
    /\ p_ver m P isreq maj min /\ p_ctl m P err hack pos entp clen csz esp
    /\ p_hlist AI m P ns hs (X0 + 2 * (cur - cur0))
    /\ bsub AI (hl_blocks AI ns hs ++ LBK) LB /\ NoDup (map blk_id (hl_blocks AI ns hs ++ LBK))
    /\ u64arr rsegs m TAB_HDR ws /\ (exists zb, bytes_at rsegs m ZERO_ADDR [zb])
    /\ hpx AI (WH okm A cap) LBK (q + 240) m0 m
    /\ (forall k, okm = Some k -> In (k, A, cap + 1) LBK).

  #[using="cur0 len methE CUR0 METHE"] Lemma hdrs_mem_app : forall m hs1 hs2, hdrs_mem AI m (hs1 ++ hs2) <-> hdrs_mem AI m hs1 /\ hdrs_mem AI m hs2.
  Proof. induction hs1 as [|h hs1 IH]; intros hs2; cbn; [LiaTuning.ctauto|]. rewrite IH. LiaTuning.ctauto. Qed.

  #[using="Type"] Lemma hdrs_blocks_app : forall hs1 hs2, hdrs_blocks AI (hs1 ++ hs2) = hdrs_blocks AI hs1 ++ hdrs_blocks AI hs2.
  Proof. intros. unfold hdrs_blocks. rewrite map_app, concat_app. reflexivity. Qed.

  Definition bH (h : hdr) : BLK := (hk AI h, hA AI h, 88).
  Definition bV (h : hdr) : BLK := (vk AI h, vA AI h, vcap AI h + 1).
  Definition bN (h : hdr) : BLK := (nk AI h, nA AI h, ncap AI h + 1).

  #[using="Type"] Lemma hl_split : forall ns hs1 h hs2 (LBK : list BLK),
    hl_blocks AI ns (hs1 ++ h :: hs2) ++ LBK = (map fst ns ++ hdrs_blocks AI hs1 ++ [bH h]) ++ bV h :: ([bN h] ++ hdrs_blocks AI hs2 ++ LBK).
  Proof.
    intros. unfold hl_blocks. rewrite hdrs_blocks_app, hdrs_blocks_cons. unfold hblocks, bH, bV, bN.
    repeat rewrite <- app_assoc. cbn. repeat rewrite <- app_assoc. reflexivity.
  Qed.

  Definition hupd (h : hdr) (vA' vlen' vcap' : Z) (vk' : K) : hdr :=
    {| hA := hA AI h; hk := hk AI h; hid := hid AI h; nA := nA AI h; nlen := nlen AI h; ncap := ncap AI h; nk := nk AI h;
       vA := vA'; vlen := vlen'; vcap := vcap'; vk := vk' |}.

  #[using="Type"] Lemma nodup_ids_eq : forall (LB : list BLK) b1 b2, NoDup (map blk_id LB) -> In b1 LB -> In b2 LB -> blk_id b1 = blk_id b2 -> b1 = b2.
  Proof.
    induction LB as [|b LB IH]; intros b1 b2 ND H1 H2 E; [destruct H1|]. cbn in ND. inversion ND as [|x l NI ND']; subst.
    destruct H1 as [<-|H1], H2 as [<-|H2]; [reflexivity| | | eapply IH; eauto].
    - exfalso. apply NI. rewrite E. apply base.list_elem_of_In. apply in_map. exact H2.
    - exfalso. apply NI. rewrite <- E. apply base.list_elem_of_In. apply in_map. exact H1.
  Qed.

  #[using="Type"] Lemma fresh_ids_cons : forall s LBf mf (bn : BLK) OB,
    RHEAP rsegs AI s LBf mf -> In bn LBf -> bsub AI OB LBf -> (forall b, In b OB -> b <> bn) ->
    NoDup (map blk_id OB) -> NoDup (map blk_id (bn :: OB)).
  Proof.
    intros s LBf mf bn OB HR HIN SUB NE ND. cbn. constructor; [| exact ND].
    intros HI. apply base.list_elem_of_In in HI. apply in_map_iff in HI. destruct HI as (b' & E & Hb').
    apply (NE b' Hb'). eapply nodup_ids_eq; [exact (ai_blocks_nodup rsegs AI _ _ _ HR)| apply SUB; exact Hb'| exact HIN| exact E].
  Qed.

  #[using="Type"] Lemma fresh_ids_keep : forall s LBf mf (bn : BLK) OB,
    RHEAP rsegs AI s LBf mf -> In bn LBf -> bsub AI OB LBf -> (forall b, In b OB -> b <> bn) ->
    bsub AI OB (lb_remove (ai_K_eqb rsegs AI) (blk_id bn) LBf).
  Proof.
    intros s LBf mf bn OB HR HIN SUB NE b Hb. apply (in_lb_remove AI); [apply SUB; exact Hb|].
    intros E. apply (NE b Hb). eapply nodup_ids_eq; [exact (ai_blocks_nodup rsegs AI _ _ _ HR)| apply SUB; exact Hb| exact HIN| exact E].
  Qed.

  #[using="Type"] Lemma ids_ne_mid : forall (b b' : BLK) (OB1 OB2 : list BLK),
    NoDup (map blk_id (OB1 ++ b :: OB2)) -> In b' (OB1 ++ OB2) -> blk_id b' <> blk_id b.
  Proof.
    intros b b' OB1 OB2 ND H E. rewrite map_app in ND. cbn in ND. apply list.NoDup_app in ND. destruct ND as (ND1 & DJ & ND2).
    apply in_app_or in H. destruct H as [H|H].
    - apply (DJ (blk_id b')). { apply base.list_elem_of_In. apply in_map. exact H. } rewrite E. left.
    - inversion ND2 as [|x l NI ND']; subst. apply NI. rewrite <- E. apply base.list_elem_of_In. apply in_map. exact H.
  Qed.

  #[using="Type"] Lemma nodup_mid : forall (b : BLK) (OB1 OB2 : list BLK),
    NoDup (map blk_id (b :: OB1 ++ OB2)) <-> NoDup (map blk_id (OB1 ++ b :: OB2)).
  Proof. intros. rewrite !map_app. cbn. rewrite <- Permutation_middle. rewrite map_app. reflexivity. Qed.

  #[using="q lo ws QLO LO0 QP WSL"] Lemma p_hlist_mono : forall m ns hs X X', p_hlist AI m P ns hs X -> (X <= X')%Z -> p_hlist AI m P ns hs X'.
  Proof.
    intros m ns hs X X' (LC & FLC & FF & DL & HS & IT & HB & NB & X0') HX. repeat (split; [assumption|]).
    split; [| lia]. intros h Hh. destruct (HB h Hh). lia.
  Qed.

  #[using="LOK P lo ws QLO CEIL QP WSL"] Lemma hpx_inblock : forall s LBf mf (b : BLK) W (LBs LBK : list BLK) SP0 WX m m',
    hpx AI W LBs SP0 m m' -> RHEAP rsegs AI s LBf mf -> In b LBf -> (forall b0, In b0 LBK -> In b0 LBf /\ b0 <> b) -> bsub AI LBK LBs ->
    (SP0 <= q + 240)%Z -> Forall (fun iv => blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b)%Z W ->
    hpx AI WX LBK (q + 240) m m'.
  Proof.
    intros s LBf mf b W LBs LBK SP0 WX m m' HP HR HIN SUB SUBs HS FA.
    pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
    eapply (hpx_weaken rsegs AI [] WX LBK LBK (q + 240) (q + 240)); [| intros x _; exact I| lia| intros b0 Hb0; exact Hb0].
    eapply (hpx_drop rsegs AI); [exact HP| exact HS| exact SUBs|].
    intros a Ha Hc. apply outside_of_forall. eapply Forall_impl; [| exact FA]. cbn. intros [lo' hi'] [H1 H2] Hr. cbn in *.
    eapply (fresh_block_not_client rsegs AI); [exact LOK| exact HR| exact HIN| exact SUB| | | exact Hc]; lia.
  Qed.

  #[using="LOK lo ws QLO CEIL QP PB WSL"] Lemma seg_frames : forall s LB m m' W (LBK : list BLK) (A cap : Z) (okm : option K),
    RHEAP rsegs AI s LB m -> RENV rsegs AI m B -> munch W m m' -> wmono rsegs m m' ->
    (forall k, okm = Some k -> In (k, A, cap + 1) LB) -> bsub AI LBK LB ->
    Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= q + 240) \/ inside (WH okm A cap) (fst iv) (snd iv - fst iv))%Z W ->
    RHEAP rsegs AI s LB m' /\ RENV rsegs AI m' B /\ hpx AI (WH okm A cap) LBK (q + 240) m m'.
  Proof.
    intros s LB m m' W LBK A cap okm HR HE MU WM HK SUBK FA. pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
    assert (CAT : Forall (fun iv => alloc_ceiling <= fst iv
                        \/ (exists lo hi, al_client_static L_ lo hi /\ lo <= fst iv /\ snd iv <= hi)
                        \/ (al_errno L_ <= fst iv /\ snd iv <= al_errno L_ + 4)
                        \/ (exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b))%Z W
            /\ Forall (fun iv => (alloc_ceiling <= fst iv /\ snd iv <= B)
                        \/ (exists lo hi, al_client_static L_ lo hi /\ lo <= fst iv /\ snd iv <= hi)
                        \/ (al_errno L_ <= fst iv /\ snd iv <= al_errno L_ + 4)
                        \/ (exists b, In b LB /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b))%Z W).
    { rewrite !Forall_forall. rewrite Forall_forall in FA. split; intros [lo' hi'] Hx; specialize (FA _ Hx); cbn in FA |- *.
      all: destruct FA as [FA|FA]; [left; lia|].
      all: unfold WH in FA; cbn [inside] in FA; destruct okm as [k|]; cbn [mwin inside] in FA.
      all: repeat match type of FA with _ \/ _ => destruct FA as [FA|FA] end; try (left; lia); try contradiction.
      all: right; right; right; exists (k, A, cap + 1); split; [apply HK; reflexivity| cbn; lia]. }
    destruct CAT as [CAT1 CAT2].
    split. { eapply (ai_heap_frame rsegs AI); [exact HR| exact MU| exact WM| exact CAT1]. }
    split. { eapply (ai_env_frame rsegs AI); [exact HR| exact HE| exact MU| exact WM| exact CAT2]. }
    eapply (hpx_seg rsegs AI); [exact LOK| exact HR| exact SUBK| exact MU| exact WM|].
    eapply Forall_impl; [| exact FA]. cbn. intros iv [H|H]; [left; exact H| right; right; exact H].
  Qed.

  #[using="LOK P q lo ws QLO LO0 QP WSL"] Lemma hp_keep : forall s LBf mf (bX : BLK) W (KEEP OBk : list BLK) SP m m',
    hpx AI W KEEP SP m m' -> RHEAP rsegs AI s LBf mf -> In bX LBf -> (forall b0, In b0 OBk -> In b0 LBf /\ b0 <> bX) -> bsub AI OBk KEEP ->
    (alloc_ceiling <= SP)%Z -> Forall (fun iv => blk_addr bX <= fst iv /\ snd iv <= blk_addr bX + blk_size bX)%Z W ->
    heap_pres AI OBk SP m m'.
  Proof.
    intros s LBf mf bX W KEEP OBk SP m m' HP HR HIN SUB SUBk HS FA.
    eapply (heap_pres_of_hpx rsegs AI W). { eapply (hpx_weaken rsegs AI); [exact HP| intros x Hx; exact Hx| lia| exact SUBk]. }
    intros a Ha Hc. apply outside_of_forall. eapply Forall_impl; [| exact FA]. cbn. intros [lo' hi'] [H1 H2] Hr. cbn in *.
    eapply (fresh_block_not_client rsegs AI); [exact LOK| exact HR| exact HIN| exact SUB| exact HS| | exact Hc]. lia.
  Qed.

  #[using="P ws WSL"] Lemma heap_pres_u64arr : forall (LB : list BLK) SP m m' A0 xs,
    heap_pres AI LB SP m m' -> u64arr rsegs m A0 xs -> client_range AI LB SP A0 (8 * Z.of_nat (length xs)) -> u64arr rsegs m' A0 xs.
  Proof.
    intros LB SP m m' A0 xs HP [BA WA] CR. split.
    - eapply (heap_pres_bytes_at rsegs AI); [exact HP| exact BA|]. rewrite u64s_length. replace (Z.of_nat (8 * length xs)) with (8 * Z.of_nat (length xs))%Z by lia. exact CR.
    - eapply (heap_pres_wr_at rsegs AI); [exact HP| exact WA| exact CR].
  Qed.

  #[using="TABST P WSL"] Lemma tab_client : forall (LB : list BLK) SP, client_range AI LB SP TAB_HDR (8 * Z.of_nat (length ws)).
  Proof. intros. destruct TABST as (lo' & hi' & ST & H1 & H2). eapply client_range_static; [exact ST| lia| rewrite WSL; cbn; lia]. Qed.
  #[using="ZST P ws WSL"] Lemma zero_client : forall (LB : list BLK) SP, client_range AI LB SP ZERO_ADDR 1.
  Proof. intros. destruct ZST as (lo' & hi' & ST & H1 & H2). eapply client_range_static; [exact ST| lia| lia]. Qed.

  Ltac hp_cell1 HP H :=
    let H' := fresh in
    pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HP H ltac:(apply client_range_above; generalize QP; clear - q P; cbn; intros; lia)) as H';
    clear H; rename H' into H.
  Ltac hp_cells HP :=
    lazymatch type of HP with heap_pres _ _ ?sp ?m ?m' =>
      repeat match goal with
      | H : rw_cells rsegs m sp ?cs |- _ => hp_cell1 HP H
      | H : rw_cells rsegs m (sp + _) ?cs |- _ => hp_cell1 HP H
      | H : rw_cells rsegs m P ?cs |- _ => hp_cell1 HP H
      | H : rw_cells rsegs m (P + _) ?cs |- _ => hp_cell1 HP H
      end
    end.

  #[using="Type"] Lemma perm3 : forall (l : list BLK) a b c, Permutation (l ++ [a; b; c]) (b :: c :: a :: l).
  Proof.
    intros. eapply Permutation_trans; [apply Permutation_app_comm|]. cbn.
    eapply perm_trans; [apply perm_swap|]. apply perm_skip. apply perm_swap.
  Qed.

  Definition comma_bytes : list byte := map (Z_to_bv 8) [44; 32].
  #[using="P ws WSL"] Lemma comma_at : forall m, mem_inv rsegs m -> bytes_at rsegs m COMMA_ADDR (comma_bytes ++ Z_to_bv 8 0 :: [Z_to_bv 8 37; Z_to_bv 8 100; Z_to_bv 8 32]).
  Proof.
    intros m MI. pose proof (ro_cells_image rsegs m COMMA_ADDR (map (Z_to_bv 8) [44; 32; 0; 37; 100; 32]) MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as RO.
    destruct RO as [_ B']. cbn [cells_bytes cbytes map] in B'. rewrite app_nil_r in B'. exact B'.
  Qed.

  #[using="P q lo ws QLO LO0 QP WSL"] Lemma nul_of_firstn : forall (bs pre : list byte) (n : Z),
    firstn (Z.to_nat (n + 1)) bs = pre ++ [Z_to_bv 8 0] -> Z.of_nat (length pre) = n -> (0 <= n)%Z ->
    nth_error bs (Z.to_nat n) = Some (Z_to_bv 8 0).
  Proof.
    intros bs pre n E L N. rewrite <- (firstn_skipn (Z.to_nat (n + 1)) bs). rewrite E.
    rewrite nth_error_app1 by (rewrite app_length; cbn; lia). rewrite nth_error_app2 by lia.
    replace (Z.to_nat n - length pre)%nat with 0%nat by lia. reflexivity.
  Qed.

  Section EXIST.
    Variables (A cap : Z) (okm : option K) (bs : list byte) (LBK : list BLK) (err hack pos entp clen csz esp : Z) (m0 : mem).
    Variables (ra s0w s1w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w gp : word) (F : bvmap 5 word) (fc : bv 32).
    Notation POST := (ph_post ra s0w s1w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w gp F fc A cap okm bs LBK err hack pos entp clen csz esp m0).
    Notation INV := (ph_inv ra s0w s1w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w A cap okm bs LBK err hack pos entp clen csz esp m0).
    Notation TP := (wz (al_tp L_)).

    #[using="AC LOK REALLOCPC IMGW1 TABST ZST QLO QLO2 STK0 LO0 CEIL QP PB BHI P8 WSL CUR0 XMAX METHE"] Lemma ph_exist : forall (cur cur2 o l meth : Z) (h : hdr) (ns : list (BLK * Z)) (hs : list hdr) (LB : list BLK) s
        x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s9 t3 t4 t5 t6 m,

      (forall s' LB' m' (cur' meth' : Z) ns' hs' x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s6' s7' s9' t3' t4' t5' t6',
         (cur + 2 <= cur')%Z -> INV s' LB' m' cur' meth' ns' hs' ->
         SREACH AI POST (PRS 0x14cd4 x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s6' s7' s9' t3' t4' t5' t6' gp TP F fc m') s' LB') ->
      In h hs -> (cur0 <= cur)%Z -> (cur + 2 <= cur2 <= len)%Z -> (0 <= l <= cur2 - cur)%Z -> (cur <= o)%Z -> (o + l <= len)%Z -> okm <> None ->
      (meth = methE \/ meth = 11) ->
      RHEAP rsegs AI s LB m -> RENV rsegs AI m B -> mem_inv rsegs m -> stk rsegs m lo q -> (exists e, rw_cells rsegs m (al_errno L_) [C4 e]) ->
      rw_cells rsegs m (q + 136) (phFS ra s0w s1w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w) -> phFY q m ->
      rw_cells rsegs m (q + 16) [C8 (wz (A + o)); C8 (wz l)] ->
      p_scan m P cur2 -> p_msg AI m LB P A len cap okm bs -> p_meth m P meth -> p_ver m P isreq maj min -> p_ctl m P err hack pos entp clen csz esp ->
      p_hlist AI m P ns hs (X0 + 2 * (cur - cur0)) ->
      bsub AI (hl_blocks AI ns hs ++ LBK) LB -> NoDup (map blk_id (hl_blocks AI ns hs ++ LBK)) ->
      u64arr rsegs m TAB_HDR ws -> (exists zb, bytes_at rsegs m ZERO_ADDR [zb]) ->
      hpx AI (WH okm A cap) LBK (q + 240) m0 m -> (forall k, okm = Some k -> In (k, A, cap + 1) LBK) ->
      SREACH AI POST (PRS 0x14e30 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz (hA AI h)) s6 s7 s9 t3 t4 t5 t6 gp TP F fc m) s LB.
    Proof.
      intros until m. intros IH Hh CURA CUR2 LR OR OL OKM METHD HR HE MI ST [e ERR] FSH FY Q16 SCN MSG METH VER CTL HL BSUB ND TAB [zb ZB] HPX MSGK.
      pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
      pose proof (word_lt64 (wz q)) as QR'. assert (EQ : bv_unsigned (wz q) = q) by (apply unsigned_lit; lia).
      destruct (lo_errno_img rsegs AI LOK) as (we & Hwe & WE1 & WE2). pose proof (lo_img_ceiling rsegs AI LOK we Hwe) as WE3.
      pose proof (rw_cells_bound rsegs _ _ _ ERR) as EB. cbn [cells_size csize Nat.add] in EB.
      destruct (hl_facts AI P q lo ws QLO LO0 QP P8 WSL s LB m ns hs _ LBK HR HL BSUB) as [NF HF].
      destruct (in_split _ _ Hh) as (hs1 & hs2 & EHS).
      pose proof HL as HLc. destruct HLc as (LC & FLC & FF & DL & HS & ITEMS & HB & NB & XR0).
      rewrite EHS in HS. apply hdrs_mem_app in HS. destruct HS as (HS1 & HSh). cbn [hdrs_mem] in HSh. destruct HSh as (HMh & HPh & HS2).
      pose proof HMh as HMc. destruct HMc as ([pad HC] & HVC & [vbs [VB VN]] & NC & [nbs [NBm NN]]). pose proof HPh as HP0. unfold hdro_pure in HP0.
      destruct (HF h Hh) as (H16 & HCE & HAL & N16 & NCE & NAL & V16 & VCE & VAL & _).
      destruct (HB h Hh) as [VX NX].
      pose proof BSUB as BSUB0. pose proof ND as ND0. rewrite EHS, hl_split in BSUB, ND.
      assert (BVIN : In (bV h) LB) by (apply BSUB; apply in_or_app; right; left; reflexivity).
      assert (BHIN : In (bH h) LB) by (apply BSUB; apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; left; reflexivity).
      assert (LMAXE : LMAX = 2^26 + 16) by reflexivity. assert (VMAXE : VMAX = 2^29) by reflexivity.
      assert (LENB : (len + 1 <= LMAX)%Z) by (destruct MSG as (_ & _ & ? & ? & _); lia).

      eapply sreach_evt. { eapply (ph_ex1 P q ws WSL (hA AI h) l); try eassumption; lia. }
      intros ms' [[-> ->]|[LNZ ->]].
      {
        eapply (IH s LB m cur2 meth ns hs); [lia|]. unfold ph_inv.
        split; [exact HR|]. split; [exact HE|]. split; [exact MI|]. split; [exact ST|]. split; [exists e; exact ERR|].
        split; [exact FSH|]. split; [apply (proj2 (phFX_Y q cur0 len CUR0 m)); split; [exact FY| do 2 eexists; exact Q16]|].
        split; [exact SCN|]. split; [lia|]. split; [exact MSG|]. split; [exact METH|]. split; [exact METHD|]. split; [exact VER|]. split; [exact CTL|].
        split; [eapply p_hlist_mono; [exact HL| lia]|]. split; [exact BSUB0|]. split; [exact ND0|]. split; [exact TAB|]. split; [exists zb; exact ZB|].
        split; [exact HPX| exact MSGK]. }

      destruct MSG as (MBC & OWNm & MLC & MCAP & MNUL). destruct METH as [MC METHR]. destruct VER as [(padw & VRC) VR]. destruct CTL as [CC CR].
      unfold p_ctl_cells in CC. unfold p_scan in SCN. unfold phFS in FSH.
      destruct FY as ([j0 Q0] & [tyw Q12] & (a32 & b32 & Q32) & (ja & idw & Q48) & [j68 Q68]).
      destruct okm as [km|]; [| exfalso; apply OKM; reflexivity]. cbn in OWNm. destruct OWNm as [MIN MBLK].
      destruct (p_msg_facts AI m LB P A len cap (Some km) bs s HR (conj MBC (conj (conj MIN MBLK) (conj MLC (conj MCAP MNUL))))) as (_ & _ & LBS & _ & SOMEF).
      destruct (SOMEF ltac:(discriminate)) as (A16 & ACE & AAL). cbn in LBS. clear SOMEF.
      assert (HWIN : (hA AI h + 88 <= 0x10000 \/ 0x2a000 <= hA AI h)%Z).
      { destruct (ai_block_range rsegs AI _ _ _ _ HR BHIN) as (_ & _ & _ & _ & FA). rewrite Forall_forall in FA. pose proof (FA _ IMGW1) as W1. cbn in W1. lia. }

      set (PRE := map fst ns ++ hdrs_blocks AI hs1 ++ [bH h]) in *. set (POST2 := [bN h] ++ hdrs_blocks AI hs2 ++ LBK) in *.
      assert (KSUB : bsub AI (PRE ++ POST2) (lb_remove (ai_K_eqb rsegs AI) (vk AI h) LB)).
      { replace (vk AI h) with (blk_id (bV h)) by reflexivity. eapply (bsub_remove_mid AI); [exact BSUB| exact ND]. }
      pose proof (nodup_remove_mid AI (bV h) PRE POST2 ND) as NDK.
      assert (INPRE_H : In (bH h) PRE) by (subst PRE; apply in_or_app; right; apply in_or_app; right; left; reflexivity).
      assert (INPOST_N : In (bN h) POST2) by (subst POST2; cbn; left; reflexivity).
      assert (INPOST_M : In (km, A, cap + 1) POST2) by (subst POST2; cbn; right; apply in_or_app; right; apply MSGK; reflexivity).
      assert (KLBK : bsub AI LBK (PRE ++ POST2)) by (intros b Hb; apply in_or_app; right; subst POST2; cbn; right; apply in_or_app; right; exact Hb).
      eapply sreach_bind.
      { eapply (membuffer_append_str_spec AI AC LOK REALLOCPC) with (lo := lo) (B := B) (MB := (hA AI h + 24)%Z) (SRC := COMMA_ADDR)
          (A := vA AI h) (len := vlen AI h) (cap := vcap AI h) (ok := Some (vk AI h)) (str := comma_bytes) (slack := [Z_to_bv 8 37; Z_to_bv 8 100; Z_to_bv 8 32]) (bs := vbs);
          rewrite ?EQ; try eassumption; try reflexivity; try (cbn; lia).
        - cbn. split; [exact BVIN| exact VB].
        - intros _. exact VN.
        - eapply (mbloc_block rsegs AI); [| | ]. { cbn. apply (in_lb_remove AI); [exact BHIN|]. exact (ids_ne_mid (bV h) (bH h) PRE POST2 ND ltac:(apply in_or_app; left; exact INPRE_H)). } all: cbn; lia.
        - apply comma_at. exact MI.
        - cbn. intros [H0|[H0|[]]]; apply (f_equal bv_unsigned) in H0; vm_compute in H0; lia.
        - right. split; [intros m' MI'; pose proof (comma_at m' MI') as B'; apply bytes_at_app in B'; exact (proj1 B')|].
          exists 0x10000, 0x2a000. split; [exact IMGW1| cbn; lia]. }
      clear HWIN. intros s1 LB1 ms1 Q1. unfold membuffer_append_post in Q1. rewrite !EQ in Q1. destruct_exs Q1.
      destruct Q1 as (-> & MI2 & ST2 & HE2 & [e2 ERR2] & HPX1 & HR2 & KSUB1 & VC2 & VLC2 & VCAP32 & VCAPB & OWN2 & FRESH2 & PFX2 & R1).
      lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
      lazymatch type of OWN2 with mown _ _ _ ?a ?c ?o ?b => rename a into vA1; rename c into vcap1; rename o into ok1; rename b into vbs1 end.
      lazymatch type of VC2 with rw_cells _ _ _ (mbuf_cells _ ?l _) => rename l into vlen1 end.
      lazymatch goal with |- SREACH _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?r) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) _ _ => rename r into r1 end.
      replace (ret_pc (Z_to_bv 64 0x14e54)) with (Z_to_bv 64 0x14e54) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      cbn [Z.of_nat length comma_bytes map] in R1, VCAPB, VLC2.

      destruct ok1 as [vk1|]; [| exfalso; cbn in OWN2; destruct R1 as [(_ & E1 & _)|(_ & _ & E1 & _)]; lia].
      cbn in OWN2. destruct OWN2 as [VIN1 VB1]. cbn [lb_keep] in HPX1, KSUB1, FRESH2. unfold mfresh in FRESH2. cbn [lb_keep] in FRESH2.

      set (OBk := (map fst ns ++ hdrs_blocks AI hs1) ++ POST2).
      assert (OBkK : bsub AI OBk (lb_remove (ai_K_eqb rsegs AI) (vk AI h) LB)).
      { intros b Hb. apply KSUB. subst OBk PRE. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left| right; exact Hb].
        apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; exact Hb| right]. apply in_or_app. left. exact Hb. }
      assert (OBkH : forall b0, In b0 OBk -> In b0 LB /\ b0 <> bH h).
      { intros b0 Hb0. split; [eapply (lb_remove_sub rsegs AI); apply OBkK; exact Hb0|].
        intros ->. apply (ids_ne_mid (bH h) (bH h) (map fst ns ++ hdrs_blocks AI hs1) POST2); [| subst OBk; exact Hb0| reflexivity].
        replace ((map fst ns ++ hdrs_blocks AI hs1) ++ bH h :: POST2) with (PRE ++ POST2) by (subst PRE; repeat rewrite <- app_assoc; reflexivity). exact NDK. }
      assert (INPRE : forall b, In b PRE -> In b OBk \/ b = bH h).
      { subst PRE OBk. intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [left; apply in_or_app; left; apply in_or_app; left; exact Hb|].
        apply in_app_or in Hb. destruct Hb as [Hb|[<-|[]]]; [left; apply in_or_app; left; apply in_or_app; right; exact Hb| right; reflexivity]. }
      assert (INPOST : forall b, In b POST2 -> In b OBk) by (intros b Hb; subst OBk; apply in_or_app; right; exact Hb).
      assert (HPk : heap_pres AI OBk q m m2).
      { eapply (hp_keep s LB m (bH h)); [exact HPX1| exact HR| exact BHIN| exact OBkH| exact OBkK| lia|]. constructor; [cbn; lia| constructor]. }
      hp_cells HPk.
      pose proof (heap_pres_u64arr _ _ _ _ _ _ HPk TAB (tab_client _ _)) as TAB2.
      pose proof (heap_pres_bytes_at rsegs AI _ _ _ _ _ _ HPk ZB (zero_client _ _)) as ZB2.
      assert (INk_M : In (km, A, cap + 1) OBk) by (subst OBk; apply in_or_app; right; exact INPOST_M).
      assert (INk_N : In (bN h) OBk) by (subst OBk; apply in_or_app; right; exact INPOST_N).
      pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPk MBLK ltac:(eapply client_range_block; [exact INk_M| cbn; lia| cbn [cells_size csize Nat.add blk_addr blk_size fst snd]; lia])) as MBLK2.
      pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPk NBm ltac:(eapply client_range_block; [exact INk_N| cbn; lia| unfold bN; cbn [cells_size csize Nat.add blk_addr blk_size fst snd]; lia])) as NBm2.
      pose proof (hpx_rw_cells rsegs AI _ _ _ _ _ _ _ HPX1 HC ltac:(eapply client_range_block; [apply (in_lb_remove AI); [exact BHIN| exact (ids_ne_mid (bV h) (bH h) PRE POST2 ND ltac:(apply in_or_app; left; exact INPRE_H))]| cbn; lia| cbn; lia]) ltac:(cbn; lia)) as HC2.
      pose proof (hpx_rw_cells rsegs AI _ _ _ _ _ _ _ HPX1 NC ltac:(eapply client_range_block; [apply (in_lb_remove AI); [exact BHIN| exact (ids_ne_mid (bV h) (bH h) PRE POST2 ND ltac:(apply in_or_app; left; exact INPRE_H))]| cbn; lia| cbn; lia]) ltac:(cbn; lia)) as NC2.
      assert (DL2 : dlseg AI m2 ns L (P + 312)).
      { eapply (dlseg_heap_pres AI); [exact DL| exact HPk|]. intros b it Hb. subst OBk. apply in_or_app. left. apply in_or_app. left. exact (in_map fst _ _ Hb). }
      assert (HS12 : hdrs_mem AI m2 hs1).
      { eapply (hdrs_mem_heap_pres AI); [exact HS1| exact HPk|]. intros b Hb. subst OBk. apply in_or_app. left. apply in_or_app. right. exact Hb. }
      assert (HS22 : hdrs_mem AI m2 hs2).
      { eapply (hdrs_mem_heap_pres AI); [exact HS2| exact HPk|]. intros b Hb. subst OBk POST2. apply in_or_app. right. cbn. right. apply in_or_app. left. exact Hb. }
      clear MBLK NBm HC NC DL HS1 HS2 TAB ZB.
      assert (VLEN1 : (vlen AI h <= vlen1 <= vlen AI h + 2)%Z /\ (vcap1 <= vcap AI h + 7)%Z) by (destruct R1 as [(_ & E1 & _)|(_ & _ & E1 & E2 & _)]; lia).
      assert (VN1 : nth_error vbs1 (Z.to_nat vlen1) = Some (Z_to_bv 8 0)).
      { destruct R1 as [(_ & E1 & E2)|(_ & _ & E1 & _ & _ & -> & _)]; [| rewrite E1; exact VN].
        eapply (nul_of_firstn vbs1 (firstn (Z.to_nat (vlen AI h)) vbs ++ [Z_to_bv 8 44; Z_to_bv 8 32])); [| | lia].
        - rewrite (E2 ltac:(lia)). rewrite <- app_assoc. reflexivity.
        - rewrite app_length, firstn_length. cbn [length]. pose proof (rw_cells_bound rsegs _ _ _ VB). destruct VB as [[W0 _] _]. cbn in W0. lia. }

      eapply sreach_evt. { eapply (ph_ex2 P q ws WSL r1 (hA AI h + 24) (A + o) l); try eassumption; lia. }
      intros ms' ->.
      assert (SRCB : bytes_at rsegs m2 (A + o) (firstn (Z.to_nat l) (skipn (Z.to_nat o) bs))).
      { pose proof (rw_cells_bytes_at rsegs _ _ _ MBLK2) as BB. cbn [cells_bytes cbytes] in BB. rewrite app_nil_r in BB.
        replace (A + o)%Z with (A + Z.of_nat (Z.to_nat o))%Z by lia. apply bytes_sub; [exact BB| lia]. }
      assert (KSUBv1 : bsub AI OBk (lb_remove (ai_K_eqb rsegs AI) vk1 LB1)).
      { replace vk1 with (blk_id (vk1, vA1, vcap1 + 1)) by reflexivity.
        eapply (fresh_ids_keep s1 LB1 m2); [exact HR2| exact VIN1| intros b Hb; apply KSUB1; apply OBkK; exact Hb| intros b Hb; apply FRESH2; apply OBkK; exact Hb]. }
      assert (BHIN1 : In (bH h) (lb_remove (ai_K_eqb rsegs AI) vk1 LB1)).
      { apply (in_lb_remove AI). { apply KSUB1. apply KSUB. apply in_or_app. left. exact INPRE_H. }
        intros E. apply (FRESH2 (bH h)); [apply KSUB; apply in_or_app; left; exact INPRE_H|].
        eapply nodup_ids_eq; [exact (ai_blocks_nodup rsegs AI _ _ _ HR2)| apply KSUB1; apply KSUB; apply in_or_app; left; exact INPRE_H| exact VIN1| exact E]. }
      eapply sreach_bind.
      { eapply (membuffer_append_spec AI AC LOK REALLOCPC) with (lo := lo) (B := B) (MB := (hA AI h + 24)%Z) (SRC := (A + o)%Z) (n := l)
          (A := vA1) (len := vlen1) (cap := vcap1) (ok := Some vk1) (bs := vbs1) (LB := LB1) (s := s1);
          rewrite ?EQ; try eassumption; try reflexivity; try lia.
        - cbn. split; [exact VIN1| exact VB1].
        - intros _. exact VN1.
        - eapply (mbloc_block rsegs AI); [exact BHIN1| cbn; lia| cbn; lia].
        - rewrite length_firstn, length_skipn. lia.
        - eapply client_range_block; [apply KSUBv1; exact INk_M| cbn; lia| cbn; lia].
        - assert (NEb : bH h <> (km, A, cap + 1)) by (eapply (nodup_in_neq AI); [exact ND| exact INPRE_H| right; exact INPOST_M]).
          pose proof (bsub_disjoint AI s LB m (PRE ++ bV h :: POST2) (bH h) (km, A, cap + 1) HR BSUB ND
                        ltac:(apply in_or_app; left; exact INPRE_H) ltac:(apply in_or_app; right; right; exact INPOST_M) NEb) as DJ.
          cbn in DJ. lia. }
      intros s2 LB2 ms2 Q2. unfold membuffer_append_post in Q2. rewrite !EQ in Q2. destruct_exs Q2.
      destruct Q2 as (-> & MI3 & ST3 & HE3 & [e3 ERR3] & HPX2 & HR3 & KSUB2 & VC3 & VLC3 & VCAP33 & VCAPB3 & OWN3 & FRESH3 & PFX3 & R2).
      lazymatch type of MI3 with mem_inv _ ?mm => rename mm into m3 end.
      lazymatch type of OWN3 with mown _ _ _ ?a ?c ?o ?b => rename a into vA2; rename c into vcap2; rename o into ok2; rename b into vbs2 end.
      lazymatch type of VC3 with rw_cells _ _ _ (mbuf_cells _ ?l _) => rename l into vlen2 end.
      lazymatch goal with |- SREACH _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?r) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) _ _ => rename r into r2 end.
      replace (ret_pc (Z_to_bv 64 0x14e68)) with (Z_to_bv 64 0x14e68) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      try rewrite length_firstn, length_skipn in R2.
      destruct ok2 as [vk2|]; [| exfalso; cbn in OWN3; destruct R2 as [(_ & E1 & _)|(_ & _ & E1 & _)]; lia].
      cbn in OWN3. destruct OWN3 as [VIN2 VB2]. cbn [lb_keep] in HPX2, KSUB2, FRESH3. unfold mfresh in FRESH3. cbn [lb_keep] in FRESH3.
      assert (VLEN2 : ((r2 = 0 /\ vlen2 = vlen1 + l /\ vcap2 <= vcap1 + l + 5) \/ (r2 = -104 /\ vlen2 = vlen1 /\ vcap2 = vcap1 /\ vbs2 = vbs1 /\ LB2 = LB1))%Z)
        by (destruct R2 as [(E0 & E1 & _)|(E0 & _ & E1 & E2 & _ & E3 & E4)]; [left| right]; repeat split; try assumption; lia).
      assert (VN2 : nth_error vbs2 (Z.to_nat vlen2) = Some (Z_to_bv 8 0)).
      { destruct R2 as [(_ & E1 & E2)|(_ & _ & E1 & _ & _ & -> & _)]; [| rewrite E1; exact VN1].
        eapply (nul_of_firstn vbs2 (firstn (Z.to_nat vlen1) vbs1 ++ firstn (Z.to_nat l) (skipn (Z.to_nat o) bs))); [| | lia].
        - rewrite (E2 ltac:(lia)). rewrite <- app_assoc. reflexivity.
        - rewrite app_length, !firstn_length, length_skipn. destruct VB1 as [[W0 _] _]. cbn in W0. lia. }

      assert (OBkH1 : forall b0, In b0 OBk -> In b0 LB1 /\ b0 <> bH h).
      { intros b0 Hb0. destruct (OBkH b0 Hb0) as [H1 H2]. split; [apply KSUB1; apply OBkK; exact Hb0| exact H2]. }
      assert (BHIN1' : In (bH h) LB1) by (eapply (lb_remove_sub rsegs AI); exact BHIN1).
      assert (HPk2 : heap_pres AI OBk q m2 m3).
      { eapply (hp_keep s1 LB1 m2 (bH h)); [exact HPX2| exact HR2| exact BHIN1'| exact OBkH1| exact KSUBv1| lia|]. constructor; [cbn; lia| constructor]. }
      hp_cells HPk2.
      pose proof (heap_pres_u64arr _ _ _ _ _ _ HPk2 TAB2 (tab_client _ _)) as TAB3.
      pose proof (heap_pres_bytes_at rsegs AI _ _ _ _ _ _ HPk2 ZB2 (zero_client _ _)) as ZB3.
      pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPk2 MBLK2 ltac:(eapply client_range_block; [exact INk_M| cbn; lia| cbn [cells_size csize Nat.add blk_addr blk_size fst snd]; lia])) as MBLK3.
      pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPk2 NBm2 ltac:(eapply client_range_block; [exact INk_N| cbn; lia| unfold bN; cbn [cells_size csize Nat.add blk_addr blk_size fst snd]; lia])) as NBm3.
      pose proof (hpx_rw_cells rsegs AI _ _ _ _ _ _ _ HPX2 HC2 ltac:(eapply client_range_block; [exact BHIN1| cbn; lia| cbn; lia]) ltac:(cbn; lia)) as HC3.
      pose proof (hpx_rw_cells rsegs AI _ _ _ _ _ _ _ HPX2 NC2 ltac:(eapply client_range_block; [exact BHIN1| cbn; lia| cbn; lia]) ltac:(cbn; lia)) as NC3.
      assert (DL3 : dlseg AI m3 ns L (P + 312)).
      { eapply (dlseg_heap_pres AI); [exact DL2| exact HPk2|]. intros b it Hb. subst OBk. apply in_or_app. left. apply in_or_app. left. exact (in_map fst _ _ Hb). }
      assert (HS13 : hdrs_mem AI m3 hs1).
      { eapply (hdrs_mem_heap_pres AI); [exact HS12| exact HPk2|]. intros b Hb. subst OBk. apply in_or_app. left. apply in_or_app. right. exact Hb. }
      assert (HS23 : hdrs_mem AI m3 hs2).
      { eapply (hdrs_mem_heap_pres AI); [exact HS22| exact HPk2|]. intros b Hb. subst OBk POST2. apply in_or_app. right. cbn. right. apply in_or_app. left. exact Hb. }
      clear MBLK2 NBm2 HC2 NC2 DL2 HS12 HS22 TAB2 ZB2.

      set (h' := hupd h vA2 vlen2 vcap2 vk2).
      assert (HM' : hdro_mem AI m3 h').
      { unfold hdro_mem. subst h'. cbn [hupd hA hk hid nA nlen ncap nk vA vlen vcap vk].
        split; [exists pad; exact HC3|]. split; [exact VC3|]. split; [exists vbs2; split; [exact VB2| exact VN2]|]. split; [exact NC3|]. exists nbs. split; [exact NBm3| exact NN]. }
      assert (HP' : hdro_pure AI h') by (unfold hdro_pure; subst h'; cbn; lia).
      assert (HL3 : p_hlist AI m3 P ns (hs1 ++ h' :: hs2) (X0 + 2 * (cur2 - cur0))).
      { split; [exact LC|]. split; [exact FLC|]. split; [exact FF|]. split; [exact DL3|].
        split. { apply hdrs_mem_app. split; [exact HS13|]. cbn [hdrs_mem]. split; [exact HM'|]. split; [exact HP'| exact HS23]. }
        split. { rewrite EHS in ITEMS. rewrite map_app in ITEMS |- *. cbn [map] in ITEMS |- *. subst h'. cbn [hupd hA]. exact ITEMS. }
        split. { intros h0 Hh0. apply in_app_or in Hh0. destruct Hh0 as [Hh0|[<-|Hh0]].
                 - destruct (HB h0 ltac:(rewrite EHS; apply in_or_app; left; exact Hh0)). lia.
                 - subst h'. cbn. lia.
                 - destruct (HB h0 ltac:(rewrite EHS; apply in_or_app; right; right; exact Hh0)). lia. }
        lia. }
      assert (BS3 : bsub AI (hl_blocks AI ns (hs1 ++ h' :: hs2) ++ LBK) LB2).
      { rewrite hl_split. change (bH h') with (bH h). change (bN h') with (bN h). fold PRE. fold POST2.
        intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|[<-|Hb]].
        - destruct (INPRE b Hb) as [Hk| ->]; [apply KSUB2; apply KSUBv1; exact Hk| apply KSUB2; exact BHIN1].
        - exact VIN2.
        - apply KSUB2. apply KSUBv1. apply INPOST. exact Hb. }
      assert (ND3 : NoDup (map blk_id (hl_blocks AI ns (hs1 ++ h' :: hs2) ++ LBK))).
      { rewrite hl_split. change (bH h') with (bH h). change (bN h') with (bN h). fold PRE. fold POST2.
        apply nodup_mid. eapply (fresh_ids_cons s2 LB2 m3); [exact HR3| exact VIN2| | | exact NDK].
        - intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
          + destruct (INPRE b Hb) as [Hk| ->]; [apply KSUB2; apply KSUBv1; exact Hk| apply KSUB2; exact BHIN1].
          + apply KSUB2. apply KSUBv1. apply INPOST. exact Hb.
        - intros b Hb. apply FRESH3. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
          + destruct (INPRE b Hb) as [Hk| ->]; [apply KSUBv1; exact Hk| exact BHIN1].
          + apply KSUBv1. apply INPOST. exact Hb. }

      assert (LBKk : forall b0, In b0 LBK -> In b0 LB /\ b0 <> bH h).
      { intros b0 Hb0. apply OBkH. subst OBk POST2. apply in_or_app. right. cbn. right. apply in_or_app. right. exact Hb0. }
      assert (HPX3 : hpx AI (WH (Some km) A cap) LBK (q + 240) m0 m3).
      { eapply (hpx_trans rsegs AI); [exact HPX|]. eapply (hpx_trans rsegs AI).
        - eapply (hpx_inblock s LB m (bH h)); [exact HPX1| exact HR| exact BHIN| exact LBKk| intros b Hb; apply KSUB; apply KLBK; exact Hb| lia|]. constructor; [cbn; lia| constructor].
        - assert (LBKP : forall b, In b LBK -> In b POST2) by (intros b Hb; subst POST2; cbn; right; apply in_or_app; right; exact Hb).
          eapply (hpx_inblock s1 LB1 m2 (bH h)); [exact HPX2| exact HR2| exact BHIN1'| | intros b Hb; apply KSUBv1; apply INPOST; apply LBKP; exact Hb| lia|].
          + intros b0 Hb0. destruct (LBKk b0 Hb0) as [H1 H2]. split; [apply KSUB1; apply KSUB; apply KLBK; exact Hb0| exact H2].
          + constructor; [cbn; lia| constructor]. }
      clear HPX HPX1 HPX2 HPk HPk2.

      eapply sreach_evt. { eapply (ph_ex3 P q r1 r2); [destruct R1 as [(E & _)|(E & _)]; lia| destruct R2 as [(E & _)|(E & _)]; lia]. }
      intros ms' [(-> & -> & ->)|(RF & ->)].
      -
        eapply (IH s2 LB2 m3 cur2 meth ns (hs1 ++ h' :: hs2)); [lia|]. unfold ph_inv.
        split; [exact HR3|]. split; [exact HE3|]. split; [exact MI3|]. split; [exact ST3|]. split; [exists e3; exact ERR3|].
        split; [exact FSH|]. split.
        { apply (proj2 (phFX_Y q cur0 len CUR0 m3)). split; [| do 2 eexists; exact Q16].
          unfold phFY. split; [eexists; exact Q0|]. split; [eexists; exact Q12|]. split; [do 2 eexists; exact Q32|]. split; [do 2 eexists; exact Q48| eexists; exact Q68]. }
        split; [exact SCN|]. split; [lia|].
        split. { split; [exact MBC|]. split; [cbn; split; [apply KSUB2; apply KSUBv1; exact INk_M| exact MBLK3]|]. split; [exact MLC|]. split; [exact MCAP| exact MNUL]. }
        split; [split; [exact MC| exact METHR]|]. split; [exact METHD|]. split; [split; [eexists; exact VRC| exact VR]|]. split; [split; [exact CC| exact CR]|].
        split; [exact HL3|]. split; [exact BS3|]. split; [exact ND3|]. split; [exact TAB3|]. split; [exists zb; exact ZB3|].
        split; [exact HPX3|]. intros k Ek. injection Ek as <-. apply MSGK. reflexivity.
      -
        eapply sreach_evt.
        { eapply (ph_err P q lo) with (err := err) (hack := hack) (pos := pos) (entp := entp) (clen := clen) (csz := csz) (esp := esp); try eassumption; try LiaTuning.alia.
          apply (proj2 (phFX_Y q cur0 len CUR0 m3)). split; [| do 2 eexists; exact Q16].
          unfold phFY. split; [eexists; exact Q0|]. split; [eexists; exact Q12|]. split; [do 2 eexists; exact Q32|]. split; [do 2 eexists; exact Q48| eexists; exact Q68]. }
        intros ms' (m4 & -> & MU4 & WM4 & MI4 & ST4 & CC4).
        destruct (seg_frames s2 LB2 m3 m4 _ LBK A cap (Some km) HR3 HE3 MU4 WM4 ltac:(intros k Ek; injection Ek as <-; apply KSUB2; apply KSUBv1; exact INk_M)
                    ltac:(intros b Hb; apply KSUB2; apply KSUBv1; apply INPOST; subst POST2; cbn; right; apply in_or_app; right; exact Hb) ltac:(apply Forall_cons; [right; cbn; lia| apply Forall_nil])) as (HR4 & HE4 & HPX4).
        assert (HPB : heap_pres AI LB2 B m3 m4).
        { eapply (heap_pres_seg rsegs AI); [exact LOK| exact HR3| intros b Hb; exact Hb| exact MU4| exact WM4|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
        pose proof (p_hlist_pres AI P ws WSL m3 m4 _ LB2 B ns (hs1 ++ h' :: hs2) _ HL3 MU4 WM4 ltac:(cbn; lia) HPB ltac:(intros b Hb; apply BS3; apply in_or_app; left; exact Hb)) as HL4.
        assert (MSG3 : p_msg AI m3 LB2 P A len cap (Some km) bs).
        { split; [exact MBC|]. split; [cbn; split; [apply KSUB2; apply KSUBv1; exact INk_M| exact MBLK3]|]. split; [exact MLC|]. split; [exact MCAP| exact MNUL]. }
        pose proof (p_msg_pres AI P q lo ws len QLO LO0 QP WSL m3 m4 _ LB2 LB2 LB2 B A cap (Some km) bs MSG3 MU4 WM4 ltac:(cbn; lia) HPB
                      ltac:(intros b Hb; cbn in Hb; destruct Hb as [<-|[]]; apply KSUB2; apply KSUBv1; exact INk_M) ltac:(intros b Hb; cbn in Hb; destruct Hb as [<-|[]]; apply KSUB2; apply KSUBv1; exact INk_M)) as MSG4.
        transport_after_call rsegs m3 m4 MU4 WM4.
        apply sreach_ret. unfold ph_post.
        do 14 eexists. exists m4, 3, cur2, meth, 500, pos, ns, (hs1 ++ h' :: hs2).
        split; [reflexivity|]. split; [exact MI4|]. split; [exact ST4|]. split; [exact HE4|]. split; [exists e3; exact ERR3|].
        split; [eapply (hpx_trans rsegs AI); [exact HPX3| exact HPX4]|]. split; [exact HR4|].
        split; [exact SCN|]. split; [lia|]. split; [exact MSG4|]. split; [split; [exact MC| exact METHR]|]. split; [exact METHD|].
        split; [split; [eexists; exact VRC| exact VR]|]. split; [split; [exact CC4| lia]|]. split; [right; reflexivity|].
        split; [exact HL4|]. split; [exact BS3|]. split; [exact ND3|]. split; [exact TAB3|]. split; [exists zb; exact ZB3|].
        split; [lia|]. split; intros; exfalso; lia.
    Qed.
  End EXIST.

  Section NEW.
    Variables (A cap : Z) (okm : option K) (bs : list byte) (LBK : list BLK) (err hack pos entp clen csz esp : Z) (m0 : mem).
    Variables (ra s0w s1w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w gp : word) (F : bvmap 5 word) (fc : bv 32).
    Notation POST := (ph_post ra s0w s1w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w gp F fc A cap okm bs LBK err hack pos entp clen csz esp m0).
    Notation INV := (ph_inv ra s0w s1w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w A cap okm bs LBK err hack pos entp clen csz esp m0).
    Notation TP := (wz (al_tp L_)).

    #[using="AC LOK FREEPC TABST ZST QLO QLO2 STK0 LO0 CEIL QP PB BHI P8 WSL CUR0"] Lemma ph_cleanup : forall (cur cur2 meth : Z) (ns : list (BLK * Z)) (hs : list hdr) (H nA nlen ncap vA vlen vcap : Z) (kH : K) (okn okv : option K)
        (nbs vbs : list byte) (LBx : list BLK) sx x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s9 t3 t4 t5 t6 mx,
      let OB := hl_blocks AI ns hs ++ LBK in
      (cur0 <= cur)%Z -> (cur + 2 <= cur2 <= len)%Z -> (meth = methE \/ meth = 11) ->
      RHEAP rsegs AI sx LBx mx -> RENV rsegs AI mx B -> mem_inv rsegs mx -> stk rsegs mx lo q -> (exists e, rw_cells rsegs mx (al_errno L_) [C4 e]) ->
      rw_cells rsegs mx (q + 136) (phFS ra s0w s1w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w) -> phFX q mx ->
      p_scan mx P cur2 -> p_msg AI mx LBx P A len cap okm bs -> p_meth mx P meth -> p_ver mx P isreq maj min -> p_ctl mx P err hack pos entp clen csz esp ->
      p_hlist AI mx P ns hs (X0 + 2 * (cur - cur0)) ->
      bsub AI OB LBx -> NoDup (map blk_id OB) ->
      u64arr rsegs mx TAB_HDR ws -> (exists zb, bytes_at rsegs mx ZERO_ADDR [zb]) ->
      hpx AI (WH okm A cap) LBK (q + 240) m0 mx -> (forall k, okm = Some k -> In (k, A, cap + 1) LBK) ->

      In (kH, H, 88) LBx -> (forall b, In b OB -> b <> (kH, H, 88)) -> (16 <= H)%Z -> (H + 88 <= alloc_ceiling)%Z -> (H mod 8 = 0)%Z ->
      rw_cells rsegs mx (H + 56) (mbuf_cells nA nlen ncap) -> mown AI mx LBx nA ncap okn nbs -> (0 <= nlen <= ncap)%Z ->
      (forall k, okn = Some k -> (forall b, In b OB -> b <> (k, nA, ncap + 1)) /\ (k, nA, ncap + 1) <> (kH, H, 88)) ->
      rw_cells rsegs mx (H + 24) (mbuf_cells vA vlen vcap) -> mown AI mx LBx vA vcap okv vbs -> (0 <= vlen <= vcap)%Z ->
      (forall k, okv = Some k -> (forall b, In b OB -> b <> (k, vA, vcap + 1)) /\ (k, vA, vcap + 1) <> (kH, H, 88) /\ (forall k', okn = Some k' -> (k, vA, vcap + 1) <> (k', nA, ncap + 1))) ->
      SREACH AI POST (PRS 0x14f14 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz H) (wz (H + 56)) (wz (H + 24)) s9 t3 t4 t5 t6 gp TP F fc mx) sx LBx.
    Proof.
      intros until mx. intros OB CURA CUR2 METHD HR HE MI ST [e ERR] FSH FX SCN MSG METH VER CTL HL BSUB ND TAB [zb ZB] HPX MSGK
             HIN HNE H16 HCE H8 NC OWNn NLC NFR VC OWNv VLC VFR.
      pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
      assert (EQ : bv_unsigned (wz q) = q) by (apply unsigned_lit; lia).
      destruct (lo_errno_img rsegs AI LOK) as (we & Hwe & WE1 & WE2). pose proof (lo_img_ceiling rsegs AI LOK we Hwe) as WE3.
      pose proof (rw_cells_bound rsegs _ _ _ ERR) as EB. cbn [cells_size csize Nat.add] in EB.
      assert (LMAXE : LMAX = 2^26 + 16) by reflexivity. assert (LENB : (len + 1 <= LMAX)%Z) by (destruct MSG as (_ & _ & ? & ? & _); lia).
      destruct MSG as (MBC & OWNm & MLC & MCAP & MNUL). destruct METH as [MC METHR]. destruct VER as [(padw & VRC) VR]. destruct CTL as [CC CR].
      unfold p_ctl_cells in CC. unfold p_scan in SCN. unfold phFS in FSH.
      destruct FX as ([j0 Q0] & [tyw Q12] & (a16 & b16 & Q16) & (a32 & b32 & Q32) & (ja & idw & Q48) & [j68 Q68]).
      pose proof HL as HLc. destruct HLc as (LC & FLC & FF & DL & HS & ITEMS & HB & NB & XR0).
      pose proof (ai_blocks_nodup rsegs AI _ _ _ HR) as NDX.

      assert (OBID : forall b, In b OB -> blk_id b <> kH /\ (forall k, okn = Some k -> blk_id b <> k) /\ (forall k, okv = Some k -> blk_id b <> k)).
      { intros b Hb. split; [| split].
        - intros E. apply (HNE b Hb). eapply nodup_ids_eq; [exact NDX| apply BSUB; exact Hb| exact HIN| exact E].
        - intros k Ek E. destruct (NFR k Ek) as [N1 _]. apply (N1 b Hb). rewrite Ek in OWNn. cbn in OWNn. destruct OWNn as [NIN _].
          eapply nodup_ids_eq; [exact NDX| apply BSUB; exact Hb| exact NIN| exact E].
        - intros k Ek E. destruct (VFR k Ek) as (V1 & _). apply (V1 b Hb). rewrite Ek in OWNv. cbn in OWNv. destruct OWNv as [VIN _].
          eapply nodup_ids_eq; [exact NDX| apply BSUB; exact Hb| exact VIN| exact E]. }
      assert (HIDS : (forall k, okn = Some k -> k <> kH) /\ (forall k, okv = Some k -> k <> kH /\ forall k', okn = Some k' -> k <> k')).
      { split.
        - intros k Ek E. destruct (NFR k Ek) as [_ N2]. apply N2. rewrite Ek in OWNn. cbn in OWNn. destruct OWNn as [NIN _].
          eapply nodup_ids_eq; [exact NDX| exact NIN| exact HIN| exact E].
        - intros k Ek. destruct (VFR k Ek) as (_ & V2 & V3). rewrite Ek in OWNv. cbn in OWNv. destruct OWNv as [VIN _]. split.
          + intros E. apply V2. eapply nodup_ids_eq; [exact NDX| exact VIN| exact HIN| exact E].
          + intros k' Ek' E. apply (V3 k' Ek'). rewrite Ek' in OWNn. cbn in OWNn. destruct OWNn as [NIN _]. eapply nodup_ids_eq; [exact NDX| exact VIN| exact NIN| rewrite E; reflexivity]. }
      destruct HIDS as [HIDn HIDv].

      assert (MSGOB : forall k, okm = Some k -> In (k, A, cap + 1) OB) by (intros k Ek; subst OB; apply in_or_app; right; apply MSGK; exact Ek).

      eapply sreach_evt. { eapply (ph_clean1 P q). }
      intros ms' ->.
      set (LB1 := match okv with None => LBx | Some k => lb_remove (ai_K_eqb rsegs AI) k LBx end).
      assert (SUB1 : bsub AI OB LB1 /\ In (kH, H, 88) LB1 /\ (forall k, okn = Some k -> In (k, nA, ncap + 1) LB1) /\ (forall b, In b LB1 -> In b LBx)).
      { subst LB1. destruct okv as [kv|].
        - split. { intros b Hb. apply (in_lb_remove AI); [apply BSUB; exact Hb|]. exact (proj2 (proj2 (OBID b Hb)) kv eq_refl). }
          split. { apply (in_lb_remove AI); [exact HIN|]. cbn. intros E. exact (proj1 (HIDv kv eq_refl) (eq_sym E)). }
          split. { intros k Ek. rewrite Ek in OWNn. cbn in OWNn. destruct OWNn as [NIN _]. apply (in_lb_remove AI); [exact NIN|]. cbn. intros E. exact (proj2 (HIDv kv eq_refl) k Ek (eq_sym E)). }
          intros b Hb. eapply (lb_remove_sub rsegs AI). exact Hb.
        - split; [exact BSUB|]. split; [exact HIN|]. split; [| auto]. intros k Ek. rewrite Ek in OWNn. cbn in OWNn. exact (proj1 OWNn). }
      destruct SUB1 as (SUB1 & HIN1 & NIN1 & SUB1x).
      eapply sreach_bind.
      { eapply (membuffer_destroy_spec AI AC LOK FREEPC) with (lo := lo) (B := B) (MB := (H + 24)%Z) (A := vA) (len := vlen) (cap := vcap) (LBrest := LB1);
          rewrite ?EQ; try eassumption; try reflexivity; try lia.
        - eapply (mbloc_block rsegs AI); [exact HIN1| cbn; lia| cbn; lia].
        - subst LB1. destruct okv as [kv|]; [right; exists kv; split; [| reflexivity]| left; split; [| reflexivity]]; cbn in OWNv; [exact (proj1 OWNv)| lia]. }
      intros sx1 LB1' ms1 Q1. unfold membuffer_destroy_post in Q1. rewrite !EQ in Q1. destruct_exs Q1.
      destruct Q1 as (-> & MI1 & ST1 & HE1 & [e1 ERR1] & HPX1 & -> & HR1 & VC1).
      lazymatch type of MI1 with mem_inv _ ?mm => rename mm into m1 end.
      replace (ret_pc (Z_to_bv 64 0x14f1c)) with (Z_to_bv 64 0x14f1c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (OBH : forall b0, In b0 OB -> In b0 LBx /\ b0 <> (kH, H, 88)) by (intros b0 Hb0; split; [apply BSUB; exact Hb0| apply HNE; exact Hb0]).
      assert (HP1 : heap_pres AI OB q mx m1).
      { eapply (hp_keep sx LBx mx (kH, H, 88)); [exact HPX1| exact HR| exact HIN| exact OBH| exact SUB1| lia|]. constructor; [cbn; lia| constructor]. }
      pose proof (hpx_rw_cells rsegs AI _ _ _ _ _ _ _ HPX1 NC ltac:(eapply client_range_block; [exact HIN1| cbn; lia| cbn; lia]) ltac:(cbn; lia)) as NC1.
      assert (OWNn1 : mown AI m1 LB1 nA ncap okn nbs).
      { destruct okn as [kn|]; cbn in OWNn |- *; [| exact OWNn]. destruct OWNn as [NIN NBLK]. split; [exact (NIN1 kn eq_refl)|].
        pose proof (ai_blocks_disjoint rsegs AI _ _ _ _ _ HR NIN HIN ltac:(intros E; exact (HIDn kn eq_refl (f_equal blk_id E)))) as DJ. cbn in DJ.
        destruct (ai_block_range rsegs AI _ _ _ _ HR NIN) as (R1 & _ & R3 & R4 & _). cbn in R1, R3, R4.
        eapply (hpx_rw_cells rsegs AI); [exact HPX1| exact NBLK| |]. { eapply client_range_block; [exact (NIN1 kn eq_refl)| cbn; lia| cbn [cells_size csize Nat.add blk_addr blk_size fst snd]; lia]. }
        cbn [disjoint_from cells_size csize Nat.add]. lia. }
      hp_cells HP1.
      pose proof (heap_pres_u64arr _ _ _ _ _ _ HP1 TAB (tab_client _ _)) as TAB1.
      pose proof (heap_pres_bytes_at rsegs AI _ _ _ _ _ _ HP1 ZB (zero_client _ _)) as ZB1.
      assert (OWNm1 : mown AI m1 LB1 A cap okm bs).
      { destruct okm as [km|]; cbn in OWNm |- *; [| exact OWNm]. destruct OWNm as [MIN MBLK]. pose proof (MSGOB km eq_refl) as MOB. split; [apply SUB1; exact MOB|].
        pose proof MBLK as MB'. destruct MB' as [[W0 _] _]. cbn in W0.
        eapply (heap_pres_rw_cells rsegs AI); [exact HP1| exact MBLK|]. eapply client_range_block; [exact MOB| cbn; lia| cbn [cells_size csize Nat.add blk_addr blk_size fst snd]; lia]. }
      assert (DL1 : dlseg AI m1 ns L (P + 312)).
      { eapply (dlseg_heap_pres AI); [exact DL| exact HP1|]. intros b it Hb. subst OB. apply in_or_app. left. apply in_or_app. left. exact (in_map fst _ _ Hb). }
      assert (HS1 : hdrs_mem AI m1 hs).
      { eapply (hdrs_mem_heap_pres AI); [exact HS| exact HP1|]. intros b Hb. subst OB. apply in_or_app. left. apply in_or_app. right. exact Hb. }
      clear NC DL HS TAB ZB VC.

      eapply sreach_evt. { eapply (ph_clean2 P q). }
      intros ms' ->.
      set (LB2 := match okn with None => LB1 | Some k => lb_remove (ai_K_eqb rsegs AI) k LB1 end).
      assert (SUB2 : bsub AI OB LB2 /\ In (kH, H, 88) LB2 /\ (forall b, In b LB2 -> In b LB1)).
      { subst LB2. destruct okn as [kn|].
        - split. { intros b Hb. apply (in_lb_remove AI); [apply SUB1; exact Hb|]. exact (proj1 (proj2 (OBID b Hb)) kn eq_refl). }
          split. { apply (in_lb_remove AI); [exact HIN1|]. cbn. intros E. exact (HIDn kn eq_refl (eq_sym E)). }
          intros b Hb. eapply (lb_remove_sub rsegs AI). exact Hb.
        - split; [exact SUB1|]. split; [exact HIN1| auto]. }
      destruct SUB2 as (SUB2 & HIN2 & SUB2x).
      eapply sreach_bind.
      { eapply (membuffer_destroy_spec AI AC LOK FREEPC) with (lo := lo) (B := B) (MB := (H + 56)%Z) (A := nA) (len := nlen) (cap := ncap) (LBrest := LB2);
          rewrite ?EQ; try eassumption; try reflexivity; try lia.
        - eapply (mbloc_block rsegs AI); [exact HIN2| cbn; lia| cbn; lia].
        - subst LB2. destruct okn as [kn|]; [right; exists kn; split; [| reflexivity]| left; split; [| reflexivity]]; cbn in OWNn1; [exact (proj1 OWNn1)| lia]. }
      intros sx2 LB2' ms2 Q2. unfold membuffer_destroy_post in Q2. rewrite !EQ in Q2. destruct_exs Q2.
      destruct Q2 as (-> & MI2 & ST2 & HE2 & [e2 ERR2] & HPX2 & -> & HR2 & NC2).
      lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
      replace (ret_pc (Z_to_bv 64 0x14f24)) with (Z_to_bv 64 0x14f24) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (OBH1 : forall b0, In b0 OB -> In b0 LB1 /\ b0 <> (kH, H, 88)) by (intros b0 Hb0; split; [apply SUB1; exact Hb0| apply HNE; exact Hb0]).
      assert (HP2 : heap_pres AI OB q m1 m2).
      { eapply (hp_keep sx1 LB1 m1 (kH, H, 88)); [exact HPX2| exact HR1| exact HIN1| exact OBH1| exact SUB2| lia|]. constructor; [cbn; lia| constructor]. }
      hp_cells HP2.
      pose proof (heap_pres_u64arr _ _ _ _ _ _ HP2 TAB1 (tab_client _ _)) as TAB2.
      pose proof (heap_pres_bytes_at rsegs AI _ _ _ _ _ _ HP2 ZB1 (zero_client _ _)) as ZB2.
      assert (OWNm2 : mown AI m2 LB2 A cap okm bs).
      { destruct okm as [km|]; cbn in OWNm1 |- *; [| exact OWNm1]. destruct OWNm1 as [MIN MBLK]. pose proof (MSGOB km eq_refl) as MOB. split; [apply SUB2; exact MOB|].
        pose proof MBLK as MB'. destruct MB' as [[W0 _] _]. cbn in W0.
        eapply (heap_pres_rw_cells rsegs AI); [exact HP2| exact MBLK|]. eapply client_range_block; [exact MOB| cbn; lia| cbn [cells_size csize Nat.add blk_addr blk_size fst snd]; lia]. }
      assert (DL2 : dlseg AI m2 ns L (P + 312)).
      { eapply (dlseg_heap_pres AI); [exact DL1| exact HP2|]. intros b it Hb. subst OB. apply in_or_app. left. apply in_or_app. left. exact (in_map fst _ _ Hb). }
      assert (HS2 : hdrs_mem AI m2 hs).
      { eapply (hdrs_mem_heap_pres AI); [exact HS1| exact HP2|]. intros b Hb. subst OB. apply in_or_app. left. apply in_or_app. right. exact Hb. }
      clear OWNm1 DL1 HS1 TAB1 ZB1 NC1 OWNn1 VC1.

      eapply sreach_evt. { eapply (ph_clean3 P q). }
      intros ms' ->.
      eapply sreach_bind.
      { rewrite <- FREEPC. eapply (ac_free rsegs AI AC) with (lo := lo) (B := B) (k := kH) (A := H) (n := 88); rewrite ?EQ; try eassumption; try reflexivity; lia. }
      intros sx3 LB3 ms3 Q3. unfold free_post in Q3. destruct_exs Q3. destruct Q3 as (-> & AF & -> & HR3).
      destruct AF as (MI3 & ST3 & HE3 & [e3 ERR3] & HPF). rewrite ?EQ in ST3, HPF.
      lazymatch type of MI3 with mem_inv _ ?mm => rename mm into m3 end.
      replace (ret_pc (Z_to_bv 64 0x14f2c)) with (Z_to_bv 64 0x14f2c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (SUB3 : bsub AI OB (lb_remove (ai_K_eqb rsegs AI) kH LB2)).
      { intros b Hb. apply (in_lb_remove AI); [apply SUB2; exact Hb|]. exact (proj1 (OBID b Hb)). }
      assert (HP3 : heap_pres AI OB q m2 m3) by (eapply (heap_pres_weaken rsegs AI); [exact HPF| lia| exact SUB3]).
      hp_cells HP3.
      pose proof (heap_pres_u64arr _ _ _ _ _ _ HP3 TAB2 (tab_client _ _)) as TAB3.
      pose proof (heap_pres_bytes_at rsegs AI _ _ _ _ _ _ HP3 ZB2 (zero_client _ _)) as ZB3.
      assert (MSG3 : p_msg AI m3 (lb_remove (ai_K_eqb rsegs AI) kH LB2) P A len cap okm bs).
      { split; [exact MBC|]. split; [| split; [exact MLC| split; [exact MCAP| exact MNUL]]].
        destruct okm as [km|]; cbn in OWNm2 |- *; [| exact OWNm2]. destruct OWNm2 as [MIN MBLK]. pose proof (MSGOB km eq_refl) as MOB. split; [apply SUB3; exact MOB|].
        pose proof MBLK as MB'. destruct MB' as [[W0 _] _]. cbn in W0.
        eapply (heap_pres_rw_cells rsegs AI); [exact HP3| exact MBLK|]. eapply client_range_block; [exact MOB| cbn; lia| cbn [cells_size csize Nat.add blk_addr blk_size fst snd]; lia]. }
      assert (HL3 : p_hlist AI m3 P ns hs (X0 + 2 * (cur - cur0))).
      { split; [exact LC|]. split; [exact FLC|]. split; [exact FF|]. split.
        { eapply (dlseg_heap_pres AI); [exact DL2| exact HP3|]. intros b it Hb. subst OB. apply in_or_app. left. apply in_or_app. left. exact (in_map fst _ _ Hb). }
        split. { eapply (hdrs_mem_heap_pres AI); [exact HS2| exact HP3|]. intros b Hb. subst OB. apply in_or_app. left. apply in_or_app. right. exact Hb. }
        auto. }

      assert (LBKOB : forall b, In b LBK -> In b OB) by (intros b Hb; subst OB; apply in_or_app; right; exact Hb).
      assert (HPX3 : hpx AI (WH okm A cap) LBK (q + 240) m0 m3).
      { eapply (hpx_trans rsegs AI); [exact HPX|]. eapply (hpx_trans rsegs AI); [| eapply (hpx_trans rsegs AI)].
        - eapply (hpx_inblock sx LBx mx (kH, H, 88)); [exact HPX1| exact HR| exact HIN| intros b0 Hb0; apply OBH; apply LBKOB; exact Hb0| intros b Hb; apply SUB1; apply LBKOB; exact Hb| lia|]. constructor; [cbn; lia| constructor].
        - eapply (hpx_inblock sx1 LB1 m1 (kH, H, 88)); [exact HPX2| exact HR1| exact HIN1| intros b0 Hb0; apply OBH1; apply LBKOB; exact Hb0| intros b Hb; apply SUB2; apply LBKOB; exact Hb| lia|]. constructor; [cbn; lia| constructor].
        - apply hpx_of_heap_pres. eapply (heap_pres_weaken rsegs AI); [exact HPF| lia| intros b Hb; apply SUB3; apply LBKOB; exact Hb]. }
      clear HPX HPX1 HPX2 HP1 HP2 HP3 HPF.

      eapply sreach_evt.
      { eapply (ph_err P q lo) with (err := err) (hack := hack) (pos := pos) (entp := entp) (clen := clen) (csz := csz) (esp := esp); try eassumption; try LiaTuning.alia.
        apply (proj2 (phFX_Y q cur0 len CUR0 m3)). split; [| do 2 eexists; exact Q16].
        unfold phFY. split; [eexists; exact Q0|]. split; [eexists; exact Q12|]. split; [do 2 eexists; exact Q32|]. split; [do 2 eexists; exact Q48| eexists; exact Q68]. }
      intros ms' (m4 & -> & MU4 & WM4 & MI4 & ST4 & CC4).
      destruct (seg_frames sx3 _ m3 m4 _ LBK A cap okm HR3 HE3 MU4 WM4 ltac:(intros k Ek; apply SUB3; apply MSGOB; exact Ek)
                  ltac:(intros b Hb; apply SUB3; apply LBKOB; exact Hb) ltac:(apply Forall_cons; [right; cbn; lia| apply Forall_nil])) as (HR4 & HE4 & HPX4).
      assert (HPB : heap_pres AI (lb_remove (ai_K_eqb rsegs AI) kH LB2) B m3 m4).
      { eapply (heap_pres_seg rsegs AI); [exact LOK| exact HR3| intros b Hb; exact Hb| exact MU4| exact WM4|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
      pose proof (p_hlist_pres AI P ws WSL m3 m4 _ _ B ns hs _ HL3 MU4 WM4 ltac:(cbn; lia) HPB ltac:(intros b Hb; apply SUB3; subst OB; apply in_or_app; left; exact Hb)) as HL4.
      pose proof (p_msg_pres AI P q lo ws len QLO LO0 QP WSL m3 m4 _ _ _ _ B A cap okm bs MSG3 MU4 WM4 ltac:(cbn; lia) HPB
                    ltac:(eapply (mown_okb AI); destruct MSG3 as (_ & OW & _); exact OW) ltac:(intros b Hb; eapply (mown_okb AI); [destruct MSG3 as (_ & OW & _); exact OW| exact Hb])) as MSG4.
      transport_after_call rsegs m3 m4 MU4 WM4.
      apply sreach_ret. unfold ph_post.
      do 14 eexists. exists m4, 3, cur2, meth, 500, pos, ns, hs.
      split; [reflexivity|]. split; [exact MI4|]. split; [exact ST4|]. split; [exact HE4|]. split; [exists e3; exact ERR3|].
      split; [eapply (hpx_trans rsegs AI); [exact HPX3| exact HPX4]|]. split; [exact HR4|].
      split; [exact SCN|]. split; [lia|]. split; [exact MSG4|]. split; [split; [exact MC| exact METHR]|]. split; [exact METHD|].
      split; [split; [eexists; exact VRC| exact VR]|]. split; [split; [exact CC4| lia]|]. split; [right; reflexivity|].
      split; [eapply p_hlist_mono; [exact HL4| lia]|]. split; [exact SUB3|]. split; [exact ND|]. split; [exact TAB3|]. split; [exists zb; exact ZB3|].
      split; [lia|]. split; intros; exfalso; lia.
    Qed.

    #[using="AC LOK MALPC FREEPC REALLOCPC IMGW1 IMGW2 TABST ZST QLO QLO2 STK0 LO0 CEIL QP PB BHI P8 WSL CUR0 XMAX METHE"] Lemma ph_newhdr : forall (cur cur2 o l tl meth id : Z) (ns : list (BLK * Z)) (hs : list hdr) (LB : list BLK) s
        x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 t3 t4 t5 t6 m,
      (forall s' LB' m' (cur' meth' : Z) ns' hs' x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s6' s7' s9' t3' t4' t5' t6',
         (cur + 2 <= cur')%Z -> INV s' LB' m' cur' meth' ns' hs' ->
         SREACH AI POST (PRS 0x14cd4 x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s6' s7' s9' t3' t4' t5' t6' gp TP F fc m') s' LB') ->
      (cur0 <= cur)%Z -> (cur + 2 <= cur2 <= len)%Z -> (0 <= l <= cur2 - cur)%Z -> (cur <= o)%Z -> (o + l <= len)%Z -> okm <> None ->
      (1 <= tl)%Z -> (cur + tl < len)%Z -> (-1 <= id < 64)%Z -> (meth = methE \/ meth = 11) ->
      RHEAP rsegs AI s LB m -> RENV rsegs AI m B -> mem_inv rsegs m -> stk rsegs m lo q -> (exists e, rw_cells rsegs m (al_errno L_) [C4 e]) ->
      rw_cells rsegs m (q + 136) (phFS ra s0w s1w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w) -> phFY q m ->
      rw_cells rsegs m (q + 16) [C8 (wz (A + o)); C8 (wz l)] -> rw_cells rsegs m (q + 32) [C8 (wz (A + cur)); C8 (wz tl)] ->
      p_scan m P cur2 -> p_msg AI m LB P A len cap okm bs -> p_meth m P meth -> p_ver m P isreq maj min -> p_ctl m P err hack pos entp clen csz esp ->
      p_hlist AI m P ns hs (X0 + 2 * (cur - cur0)) ->
      bsub AI (hl_blocks AI ns hs ++ LBK) LB -> NoDup (map blk_id (hl_blocks AI ns hs ++ LBK)) ->
      u64arr rsegs m TAB_HDR ws -> (exists zb, bytes_at rsegs m ZERO_ADDR [zb]) ->
      hpx AI (WH okm A cap) LBK (q + 240) m0 m -> (forall k, okm = Some k -> In (k, A, cap + 1) LBK) ->
      SREACH AI POST (PRS 0x14e7c x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (wz 0) s6 s7 (wz id) t3 t4 t5 t6 gp TP F fc m) s LB.
    Proof.
      intros until m. intros IH CURA CUR2 LR OR OL OKM TL1 TLT IDR METHD HR HE MI ST [e ERR] FSH FY Q16 TC SCN MSG METH VER CTL HL BSUB ND TAB [zb ZB] HPX MSGK.
      pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
      assert (EQ : bv_unsigned (wz q) = q) by (apply unsigned_lit; lia).
      destruct (lo_errno_img rsegs AI LOK) as (we & Hwe & WE1 & WE2). pose proof (lo_img_ceiling rsegs AI LOK we Hwe) as WE3.
      pose proof (rw_cells_bound rsegs _ _ _ ERR) as EB. cbn [cells_size csize Nat.add] in EB.
      assert (LMAXE : LMAX = 2^26 + 16) by reflexivity. assert (VMAXE : VMAX = 2^29) by reflexivity.
      assert (LENB : (len + 1 <= LMAX)%Z) by (destruct MSG as (_ & _ & ? & ? & _); lia).
      destruct (hl_facts AI P q lo ws QLO LO0 QP P8 WSL s LB m ns hs _ LBK HR HL BSUB) as [NF HF].
      set (OB := hl_blocks AI ns hs ++ LBK) in *.
      pose proof MSG as MSGc. destruct MSGc as (MBC & OWNm & MLC & MCAP & MNUL). destruct METH as [MC METHR]. destruct VER as [(padw & VRC) VR]. destruct CTL as [CC CR].
      unfold p_ctl_cells in CC. unfold p_scan in SCN. unfold phFS in FSH.
      destruct FY as ([j0 Q0] & [tyw Q12] & (a32 & b32 & Q32) & (ja & idw & Q48) & [j68 Q68]).
      assert (EOK' : exists km, okm = Some km) by (destruct okm as [km|]; [exists km; reflexivity| exfalso; apply OKM; reflexivity]).
      destruct EOK' as [km EOK]. rewrite EOK in OWNm, MNUL. cbn in OWNm, MNUL. destruct OWNm as [MIN MBLK].
      destruct (p_msg_facts AI m LB P A len cap okm bs s HR MSG) as (_ & _ & LBS & _ & SOMEF).
      destruct (SOMEF OKM) as (A16 & ACE & AAL). rewrite EOK in LBS. cbn in LBS. clear SOMEF.
      assert (MOB : In (km, A, cap + 1) OB) by (subst OB; apply in_or_app; right; apply MSGK; exact EOK).
      assert (LBKOB : forall b, In b LBK -> In b OB) by (intros b Hb; subst OB; apply in_or_app; right; exact Hb).
      assert (MSGWIN : ((A + (cap + 1) <= 0x10000 \/ 0x2a000 <= A) /\ (A + (cap + 1) <= 0x2a000 \/ 0x5d000 <= A))%Z).
      { destruct (ai_block_range rsegs AI _ _ _ _ HR MIN) as (_ & _ & _ & _ & FA). rewrite Forall_forall in FA.
        pose proof (FA _ IMGW1) as W1. pose proof (FA _ IMGW2) as W2. cbn in W1, W2. lia. }
      pose proof HL as HLc. destruct HLc as (LC & FLC & FF & DL & HS & ITEMS & HB & NB & XR0).

      eapply sreach_evt. { eapply (ph_new1 P q). }
      intros ms' ->.
      eapply sreach_bind.
      { rewrite <- MALPC. eapply (ac_malloc rsegs AI AC) with (lo := lo) (B := B); rewrite ?EQ; try eassumption; try reflexivity; lia. }
      intros s1 LB1 ms1 Q1. unfold malloc_post in Q1. destruct_exs Q1. destruct Q1 as (-> & AF & CASES).
      destruct AF as (MI1 & ST1 & HE1 & [e1 ERR1] & HPF). rewrite ?EQ in ST1, HPF.
      lazymatch type of MI1 with mem_inv _ ?mm => rename mm into m1 end.
      replace (ret_pc (Z_to_bv 64 0x14e84)) with (Z_to_bv 64 0x14e84) by (symmetry; apply ret_pc_even; [lia| reflexivity]).

      hp_cells HPF.
      pose proof (heap_pres_u64arr _ _ _ _ _ _ HPF TAB (tab_client _ _)) as TAB1.
      pose proof (heap_pres_bytes_at rsegs AI _ _ _ _ _ _ HPF ZB (zero_client _ _)) as ZB1.
      pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPF MBLK ltac:(eapply client_range_block; [exact MIN| cbn; lia| cbn [cells_size csize Nat.add blk_addr blk_size fst snd]; lia])) as MBLK1.
      assert (DL1 : dlseg AI m1 ns L (P + 312)).
      { eapply (dlseg_heap_pres AI); [exact DL| exact HPF|]. intros b it Hb. apply BSUB. subst OB. apply in_or_app. left. apply in_or_app. left. exact (in_map fst _ _ Hb). }
      assert (HS1 : hdrs_mem AI m1 hs).
      { eapply (hdrs_mem_heap_pres AI); [exact HS| exact HPF|]. intros b Hb. apply BSUB. subst OB. apply in_or_app. left. apply in_or_app. right. exact Hb. }
      assert (HPX1 : hpx AI (WH okm A cap) LBK (q + 240) m m1).
      { apply hpx_of_heap_pres. eapply (heap_pres_weaken rsegs AI); [exact HPF| lia| intros b Hb; apply BSUB; apply LBKOB; exact Hb]. }
      clear TAB ZB MBLK DL HS HPF.
      lazymatch goal with |- SREACH _ _ (MS (mkR _ _ _ _ _ _ _ _ _ ?a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) _ _ => set (rv := a) end.
      assert (HL1 : p_hlist AI m1 P ns hs (X0 + 2 * (cur - cur0))) by (split; [exact LC| split; [exact FLC| split; [exact FF| split; [exact DL1| split; [exact HS1| auto]]]]]).
      assert (MSG1 : p_msg AI m1 LB P A len cap okm bs) by (unfold p_msg; rewrite EOK; cbn; split; [exact MBC| split; [split; [exact MIN| exact MBLK1]| auto]]).
      destruct CASES as [(-> & -> & HR1)|(kH & H & junk & -> & -> & BR & HR1 & HBLK)]; subst rv.
      {
        eapply sreach_evt. { eapply (ph_new2 P q lo) with (H := 0) (T := (A + cur)%Z) (tl := tl) (l := l) (hb := (A + o)%Z) (junk := []); try eassumption; try LiaTuning.alia. all: intros X; exfalso; apply X; reflexivity. }
        intros ms' (m2 & [(_ & -> & ->)|(hb' & l' & jj & R)]); [| destruct R as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & NZ & _); exfalso; apply NZ; reflexivity].
        eapply sreach_evt.
        { eapply (ph_err P q lo) with (err := err) (hack := hack) (pos := pos) (entp := entp) (clen := clen) (csz := csz) (esp := esp); try eassumption; try LiaTuning.alia.
          apply (proj2 (phFX_Y q cur0 len CUR0 m1)). split; [| do 2 eexists; exact Q16].
          unfold phFY. split; [eexists; exact Q0|]. split; [eexists; exact Q12|]. split; [do 2 eexists; exact Q32|]. split; [do 2 eexists; exact Q48| eexists; exact Q68]. }
        intros ms' (m4 & -> & MU4 & WM4 & MI4 & ST4 & CC4).
        destruct (seg_frames s1 LB m1 m4 _ LBK A cap okm HR1 HE1 MU4 WM4 ltac:(intros k Ek; rewrite EOK in Ek; injection Ek as <-; exact MIN)
                    ltac:(intros b Hb; apply BSUB; apply LBKOB; exact Hb) ltac:(apply Forall_cons; [right; cbn; lia| apply Forall_nil])) as (HR4 & HE4 & HPX4).
        assert (HPB : heap_pres AI LB B m1 m4).
        { eapply (heap_pres_seg rsegs AI); [exact LOK| exact HR1| intros b Hb; exact Hb| exact MU4| exact WM4|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
        pose proof (p_hlist_pres AI P ws WSL m1 m4 _ _ B ns hs _ HL1 MU4 WM4 ltac:(cbn; lia) HPB ltac:(intros b Hb; apply BSUB; subst OB; apply in_or_app; left; exact Hb)) as HL4.
        pose proof (p_msg_pres AI P q lo ws len QLO LO0 QP WSL m1 m4 _ _ _ _ B A cap okm bs MSG1 MU4 WM4 ltac:(cbn; lia) HPB
                      ltac:(intros b Hb; rewrite EOK in Hb; cbn in Hb; destruct Hb as [<-|[]]; exact MIN) ltac:(intros b Hb; rewrite EOK in Hb; cbn in Hb; destruct Hb as [<-|[]]; exact MIN)) as MSG4.
        transport_after_call rsegs m1 m4 MU4 WM4.
        apply sreach_ret. unfold ph_post.
        do 14 eexists. exists m4, 3, cur2, meth, 500, pos, ns, hs.
        split; [reflexivity|]. split; [exact MI4|]. split; [exact ST4|]. split; [exact HE4|]. split; [exists e1; exact ERR1|].
        split; [eapply (hpx_trans rsegs AI); [exact HPX| eapply (hpx_trans rsegs AI); [exact HPX1| exact HPX4]]|]. split; [exact HR4|].
        split; [exact SCN|]. split; [lia|]. split; [exact MSG4|]. split; [split; [exact MC| exact METHR]|]. split; [exact METHD|].
        split; [split; [eexists; exact VRC| exact VR]|]. split; [split; [exact CC4| lia]|]. split; [right; reflexivity|].
        split; [eapply p_hlist_mono; [exact HL4| lia]|]. split; [exact BSUB|]. split; [exact ND|]. split; [exact TAB1|]. split; [exists zb; exact ZB1|].
        split; [lia|]. split; intros; exfalso; lia. }

      destruct BR as (HPOS & HAL & _ & HCE & HFA). rewrite Forall_forall in HFA.
      pose proof (HFA _ IMGW2) as HW2. pose proof (HFA _ Hwe) as HWE. cbn in HW2, HWE. clear HFA.
      assert (H16 : (16 <= H)%Z) by (Z.div_mod_to_equations; lia).
      set (bHn := (kH, H, 88) : BLK) in *.
      assert (HIN1 : In bHn ((kH, H, 88) :: LB)) by (left; reflexivity).
      pose proof (ai_blocks_nodup rsegs AI _ _ _ HR1) as NDX1.
      assert (OBH : forall b0, In b0 OB -> In b0 (bHn :: LB) /\ b0 <> bHn).
      { intros b0 Hb0. split; [right; apply BSUB; exact Hb0|]. intros ->. cbn in NDX1. inversion NDX1 as [|xx l0 NI ND']; subst.
        apply NI. apply base.list_elem_of_In. exact (in_map blk_id _ _ (BSUB _ Hb0)). }
      pose proof (ai_blocks_disjoint rsegs AI _ _ _ _ _ HR1 HIN1 (or_intror (BSUB _ MOB)) ltac:(intros E; exact (proj2 (OBH _ MOB) (eq_sym E)))) as DJM. cbn in DJM.
      cbn [Z.to_nat Pos.to_nat] in HBLK.

      eapply sreach_evt. { eapply (ph_new2 P q lo) with (H := H) (T := (A + cur)%Z) (tl := tl) (l := l) (hb := (A + o)%Z) (junk := junk); try eassumption; try LiaTuning.alia.
                           intros _. split; [exact HBLK| split; [exact HAL| lia]]. }
      intros ms' (m2 & [(E0 & _)|(hb' & l' & j0' & t0' & t1' & t2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & _ & -> & MU2 & WM2 & MI2 & HB0 & VC0 & NC0 & Q16b & HBV)]); [exfalso; lia|].
      assert (FR2 : RHEAP rsegs AI s1 (bHn :: LB) m2 /\ RENV rsegs AI m2 B /\ hpx AI (WH okm A cap) LBK (q + 240) m1 m2).
      { split. { eapply (ai_heap_frame rsegs AI); [exact HR1| exact MU2| exact WM2|]. apply Forall_cons. { right; right; right. exists bHn. split; [exact HIN1| cbn; lia]. } apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
        split. { eapply (ai_env_frame rsegs AI); [exact HR1| exact HE1| exact MU2| exact WM2|]. apply Forall_cons. { right; right; right. exists bHn. split; [exact HIN1| cbn; lia]. } apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
        eapply (hpx_seg rsegs AI); [exact LOK| exact HR1| intros b Hb; right; apply BSUB; apply LBKOB; exact Hb| exact MU2| exact WM2|].
        apply Forall_cons. { right; left. cbn. intros a Ha. eapply (fresh_block_not_client rsegs AI); [exact LOK| exact HR1| exact HIN1| intros b0 Hb0; apply OBH; apply LBKOB; exact Hb0| lia| cbn; lia]. }
        apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
      destruct FR2 as (HR2 & HE2 & HPX2).
      assert (HPB2 : heap_pres AI OB B m1 m2).
      { eapply (heap_pres_seg rsegs AI); [exact LOK| exact HR1| intros b Hb; exact (proj1 (OBH b Hb))| exact MU2| exact WM2|].
        apply Forall_cons. { right. cbn. intros a Ha. eapply (fresh_block_not_client rsegs AI); [exact LOK| exact HR1| exact HIN1| exact OBH| lia| cbn; lia]. }
        apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
      pose proof (p_hlist_pres AI P ws WSL m1 m2 _ _ B ns hs _ HL1 MU2 WM2 ltac:(cbn; lia) HPB2 ltac:(intros b Hb; subst OB; apply in_or_app; left; exact Hb)) as HL2.
      pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPB2 MBLK1 ltac:(eapply client_range_block; [exact MOB| cbn; lia| cbn [cells_size csize Nat.add blk_addr blk_size fst snd]; lia])) as MBLK2.
      pose proof (heap_pres_u64arr _ _ _ _ _ _ HPB2 TAB1 (tab_client _ _)) as TAB2.
      pose proof (heap_pres_bytes_at rsegs AI _ _ _ _ _ _ HPB2 ZB1 (zero_client _ _)) as ZB2.
      clear HL1 MSG1 MBLK1 TAB1 ZB1 DL1 HS1.
      transport_after_call rsegs m1 m2 MU2 WM2. clear MI1.
      unfold mbuf_cells in VC0, NC0.

      assert (TOKB : bytes_at rsegs m2 (A + cur) (firstn (Z.to_nat tl) (skipn (Z.to_nat cur) bs))).
      { pose proof (rw_cells_bytes_at rsegs _ _ _ MBLK2) as BB. cbn [cells_bytes cbytes] in BB. rewrite app_nil_r in BB.
        replace (A + cur)%Z with (A + Z.of_nat (Z.to_nat cur))%Z by lia. apply bytes_sub; [exact BB| lia]. }
      eapply sreach_bind.
      { eapply (membuffer_assign_spec AI AC LOK REALLOCPC) with (lo := lo) (B := B) (MB := (H + 56)%Z) (SRC := (A + cur)%Z) (n := tl)
          (A := 0) (len := 0) (cap := 0) (ok := None) (bs := []) (LB := bHn :: LB) (s := s1);
          rewrite ?EQ; try eassumption; try reflexivity; try lia.
        all: try (cbn; repeat split; reflexivity).
        all: try (intros X; exfalso; apply X; reflexivity).
        all: try (cbn [lb_keep]; eapply (mbloc_block rsegs AI); [exact HIN1| cbn; lia| cbn; lia]).
        all: try (rewrite length_firstn, length_skipn; lia).
        all: try (cbn [lb_keep]; eapply client_range_block; [right; exact (BSUB _ MOB)| cbn; lia| cbn; lia]).
        }
      intros s2 LB2 ms2 Q2. unfold membuffer_assign_post in Q2. rewrite !EQ in Q2. destruct_exs Q2.
      destruct Q2 as (-> & MI3 & ST3 & HE3 & [e3 ERR3] & HPX3 & HR3 & KSUB3 & NC3 & NLC & NCAP32 & NCAPB & OWNn & FRESHn & Rn).
      lazymatch type of MI3 with mem_inv _ ?mm => rename mm into m3 end.
      lazymatch type of OWNn with mown _ _ _ ?a ?c ?o ?b => rename a into nA; rename c into ncap; rename o into okn; rename b into nbs end.
      lazymatch type of NC3 with rw_cells _ _ _ (mbuf_cells _ ?l _) => rename l into nlen end.
      lazymatch goal with |- SREACH _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?r) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) _ _ => rename r into r7 end.
      replace (ret_pc (Z_to_bv 64 0x14ed8)) with (Z_to_bv 64 0x14ed8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      cbn [lb_keep] in HPX3, KSUB3, FRESHn. unfold mfresh in FRESHn. cbn [lb_keep] in FRESHn.
      rewrite length_firstn, length_skipn in Rn || idtac.
      assert (OBH2 : forall b0, In b0 OB -> In b0 (bHn :: LB) /\ b0 <> bHn) by exact OBH.
      assert (HPk3 : heap_pres AI OB q m2 m3).
      { eapply (hp_keep s1 (bHn :: LB) m2 bHn); [exact HPX3| exact HR2| exact HIN1| exact OBH| intros b Hb; right; apply BSUB; exact Hb| lia|]. constructor; [cbn; lia| constructor]. }
      pose proof (hpx_rw_cells rsegs AI _ _ _ _ _ _ _ HPX3 HB0 ltac:(eapply client_range_block; [exact HIN1| cbn; lia| cbn; lia]) ltac:(cbn; lia)) as HB3.
      pose proof (hpx_rw_cells rsegs AI _ _ _ _ _ _ _ HPX3 VC0 ltac:(eapply client_range_block; [exact HIN1| cbn; lia| cbn; lia]) ltac:(cbn; lia)) as VC3.
      hp_cells HPk3.
      pose proof (heap_pres_u64arr _ _ _ _ _ _ HPk3 TAB2 (tab_client _ _)) as TAB3.
      pose proof (heap_pres_bytes_at rsegs AI _ _ _ _ _ _ HPk3 ZB2 (zero_client _ _)) as ZB3.
      pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPk3 MBLK2 ltac:(eapply client_range_block; [exact MOB| cbn; lia| cbn [cells_size csize Nat.add blk_addr blk_size fst snd]; lia])) as MBLK3.
      assert (HL3 : p_hlist AI m3 P ns hs (X0 + 2 * (cur - cur0))).
      { destruct HL2 as (_ & _ & _ & DL2 & HS2 & _). split; [exact LC|]. split; [exact FLC|]. split; [exact FF|].
        split. { eapply (dlseg_heap_pres AI); [exact DL2| exact HPk3|]. intros b it Hb. subst OB. apply in_or_app. left. apply in_or_app. left. exact (in_map fst _ _ Hb). }
        split. { eapply (hdrs_mem_heap_pres AI); [exact HS2| exact HPk3|]. intros b Hb. subst OB. apply in_or_app. left. apply in_or_app. right. exact Hb. }
        auto. }
      assert (HPX03 : hpx AI (WH okm A cap) LBK (q + 240) m0 m3).
      { eapply (hpx_trans rsegs AI); [exact HPX|]. eapply (hpx_trans rsegs AI); [exact HPX1|]. eapply (hpx_trans rsegs AI); [exact HPX2|].
        eapply (hpx_inblock s1 (bHn :: LB) m2 bHn); [exact HPX3| exact HR2| exact HIN1| intros b0 Hb0; apply OBH; apply LBKOB; exact Hb0| intros b Hb; right; apply BSUB; apply LBKOB; exact Hb| lia|]. constructor; [cbn; lia| constructor]. }
      clear HPX HPX1 HPX2 HPX3 HPB2 HPk3 HL2 MBLK2 TAB2 ZB2 HB0 VC0 MI2.
      assert (R7 : (r7 = 0 \/ r7 = -104)%Z) by (destruct Rn as [(E & _)|(E & _)]; lia).
      assert (HLB' : ((0 <= A + o /\ A + o < 2^64) /\ (0 <= hb' < 2^64) /\ (0 <= l' < 2^64))%Z) by (destruct HBV as [(? & -> & ->)|(? & -> & ->)]; lia).
      eapply sreach_evt. { eapply (ph_new5 P q ws WSL r7 H hb' l'); try eassumption; lia. }
      intros ms' [[R7NZ ->]|[-> ->]].
      {
        destruct Rn as [(E & _)|(_ & -> & -> & -> & -> & -> & ->)]; [exfalso; lia|].
        eapply (ph_cleanup cur cur2 meth ns hs H 0 0 0 0 0 0 kH None None [] []); try eassumption; try LiaTuning.alia.
        all: try (exists e3; exact ERR3).
        all: try (exists zb; exact ZB3).
        all: try (apply (proj2 (phFX_Y q cur0 len CUR0 m3)); split; [| do 2 eexists; exact Q16b];
                  unfold phFY; split; [eexists; exact Q0|]; split; [eexists; exact Q12|]; split; [do 2 eexists; exact Q32|]; split; [do 2 eexists; exact Q48| eexists; exact Q68]).
        all: try (unfold p_msg; rewrite EOK; cbn; split; [exact MBC|]; split; [split; [apply KSUB3; right; exact (BSUB _ MOB)| exact MBLK3]|]; repeat split; try assumption; lia).
        all: try exact (conj MC METHR).
        all: try exact (conj (ex_intro _ padw VRC) VR).
        all: try exact (conj CC CR).
        all: try (intros b Hb; apply KSUB3; right; apply BSUB; exact Hb).
        all: try (apply KSUB3; exact HIN1).
        all: try (intros b Hb; exact (proj2 (OBH b Hb))).
        all: try (cbn; repeat split; reflexivity).
        all: try (intros k Ek; discriminate).
        all: try (unfold mbuf_cells; exact VC3).
        }

      destruct Rn as [(_ & -> & NPFX)|(E & _)]; [| exfalso; lia].
      destruct okn as [nk|]; [| exfalso; cbn in OWNn; lia]. cbn in OWNn, FRESHn. destruct OWNn as [NIN NBLK].
      assert (NN : nth_error nbs (Z.to_nat tl) = Some (Z_to_bv 8 0)).
      { eapply nul_of_firstn; [exact (NPFX ltac:(lia))| rewrite length_firstn, length_skipn; lia| lia]. }
      destruct (ai_block_range rsegs AI _ _ _ _ HR3 NIN) as (NR1 & NR2 & NR3 & NR4 & _). cbn in NR1, NR2, NR3, NR4.
      assert (HIN3 : In bHn LB2) by (apply KSUB3; exact HIN1).
      assert (NEHN : (nk, nA, ncap + 1) <> bHn) by (intros E; exact (FRESHn _ HIN1 (eq_sym E))).
      pose proof (ai_blocks_disjoint rsegs AI _ _ _ _ _ HR3 NIN HIN3 NEHN) as DJNH. cbn in DJNH.
      pose proof (ai_blocks_disjoint rsegs AI _ _ _ _ _ HR3 NIN (KSUB3 _ (or_intror (BSUB _ MOB))) ltac:(intros E; exact (FRESHn _ (or_intror (BSUB _ MOB)) (eq_sym E)))) as DJNM. cbn in DJNM.

      set (vsrc := if (l =? 0)%Z then [zb] else firstn (Z.to_nat l) (skipn (Z.to_nat o) bs)).
      assert (VSRC : bytes_at rsegs m3 hb' vsrc /\ Z.of_nat (length vsrc) = l' /\ (0 < hb')%Z /\ (hb' + l' <= alloc_ceiling)%Z
                     /\ client_range AI LB2 q hb' l' /\ (hb' + l' <= H + 24 \/ H + 24 + 32 <= hb')%Z /\ (1 <= l')%Z /\ (l' = Z.max l 1)%Z).
      { subst vsrc. destruct HBV as [(-> & -> & ->)|(LNZ & -> & ->)].
        - rewrite Z.eqb_refl. split; [exact ZB3|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [apply zero_client|]. lia.
        - replace (l =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact LNZ).
          split. { pose proof (rw_cells_bytes_at rsegs _ _ _ MBLK3) as BB. cbn [cells_bytes cbytes] in BB. rewrite app_nil_r in BB.
                   replace (A + o)%Z with (A + Z.of_nat (Z.to_nat o))%Z by lia. apply bytes_sub; [exact BB| lia]. }
          split; [rewrite length_firstn, length_skipn; lia|]. split; [lia|]. split; [lia|].
          split; [eapply client_range_block; [apply KSUB3; right; exact (BSUB _ MOB)| cbn; lia| cbn; lia]|]. lia. }
      destruct VSRC as (VS1 & VS2 & VS3 & VS4 & VS5 & VS6 & VS7 & VS8). clear HW2 MSGWIN.
      eapply sreach_bind.
      { eapply (membuffer_assign_spec AI AC LOK REALLOCPC) with (lo := lo) (B := B) (MB := (H + 24)%Z) (SRC := hb') (n := l')
          (A := 0) (len := 0) (cap := 0) (ok := None) (bs := []) (LB := LB2) (s := s2) (src := vsrc);
          rewrite ?EQ; try eassumption; try reflexivity; try lia.
        all: try (cbn; repeat split; reflexivity).
        all: try (intros X; exfalso; apply X; reflexivity).
        all: try (cbn [lb_keep]; eapply (mbloc_block rsegs AI); [exact HIN3| cbn; lia| cbn; lia]).
        }
      intros s3 LB3 ms3 Q3. unfold membuffer_assign_post in Q3. rewrite !EQ in Q3. destruct_exs Q3.
      destruct Q3 as (-> & MI4 & ST4 & HE4 & [e4 ERR4] & HPX4 & HR4 & KSUB4 & VC4 & VLC & VCAP32 & VCAPB & OWNv & FRESHv & Rv).
      lazymatch type of MI4 with mem_inv _ ?mm => rename mm into m4 end.
      lazymatch type of OWNv with mown _ _ _ ?a ?c ?o ?b => rename a into vA; rename c into vcap; rename o into okv; rename b into vbs end.
      lazymatch type of VC4 with rw_cells _ _ _ (mbuf_cells _ ?l _) => rename l into vlen end.
      lazymatch goal with |- SREACH _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?r) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) _ _ => rename r into r8 end.
      replace (ret_pc (Z_to_bv 64 0x14eec)) with (Z_to_bv 64 0x14eec) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      cbn [lb_keep] in HPX4, KSUB4, FRESHv. unfold mfresh in FRESHv. cbn [lb_keep] in FRESHv.

      assert (OBH3 : forall b0, In b0 ((nk, nA, ncap + 1) :: OB) -> In b0 LB2 /\ b0 <> bHn).
      { intros b0 [<-|Hb0]; [split; [exact NIN| exact NEHN]|]. split; [apply KSUB3; right; apply BSUB; exact Hb0| exact (proj2 (OBH b0 Hb0))]. }
      assert (HPk4 : heap_pres AI ((nk, nA, ncap + 1) :: OB) q m3 m4).
      { eapply (hp_keep s2 LB2 m3 bHn); [exact HPX4| exact HR3| exact HIN3| exact OBH3| intros b Hb; exact (proj1 (OBH3 b Hb))| lia|]. constructor; [cbn; lia| constructor]. }
      pose proof (hpx_rw_cells rsegs AI _ _ _ _ _ _ _ HPX4 HB3 ltac:(eapply client_range_block; [exact HIN3| cbn; lia| cbn; lia]) ltac:(cbn; lia)) as HB4.
      pose proof (hpx_rw_cells rsegs AI _ _ _ _ _ _ _ HPX4 NC3 ltac:(eapply client_range_block; [exact HIN3| cbn; lia| unfold mbuf_cells; cbn; lia]) ltac:(unfold mbuf_cells; cbn; lia)) as NC4.
      hp_cells HPk4.
      pose proof (heap_pres_u64arr _ _ _ _ _ _ HPk4 TAB3 (tab_client _ _)) as TAB4.
      pose proof (heap_pres_bytes_at rsegs AI _ _ _ _ _ _ HPk4 ZB3 (zero_client _ _)) as ZB4.
      pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPk4 MBLK3 ltac:(eapply client_range_block; [right; exact MOB| cbn; lia| cbn [cells_size csize Nat.add blk_addr blk_size fst snd]; lia])) as MBLK4.
      pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPk4 NBLK ltac:(eapply client_range_block; [left; reflexivity| cbn; lia| cbn [cells_size csize Nat.add blk_addr blk_size fst snd]; lia])) as NBLK4.
      assert (HL4 : p_hlist AI m4 P ns hs (X0 + 2 * (cur - cur0))).
      { destruct HL3 as (_ & _ & _ & DL3 & HS3 & _). split; [exact LC|]. split; [exact FLC|]. split; [exact FF|].
        split. { eapply (dlseg_heap_pres AI); [exact DL3| exact HPk4|]. intros b it Hb. right. subst OB. apply in_or_app. left. apply in_or_app. left. exact (in_map fst _ _ Hb). }
        split. { eapply (hdrs_mem_heap_pres AI); [exact HS3| exact HPk4|]. intros b Hb. right. subst OB. apply in_or_app. left. apply in_or_app. right. exact Hb. }
        auto. }
      assert (HPX04 : hpx AI (WH okm A cap) LBK (q + 240) m0 m4).
      { eapply (hpx_trans rsegs AI); [exact HPX03|].
        eapply (hpx_inblock s2 LB2 m3 bHn); [exact HPX4| exact HR3| exact HIN3| intros b0 Hb0; apply OBH3; right; apply LBKOB; exact Hb0| intros b Hb; apply KSUB3; right; apply BSUB; apply LBKOB; exact Hb| lia|]. constructor; [cbn; lia| constructor]. }
      clear HPX03 HPX4 HPk4 HL3 MBLK3 TAB3 ZB3 HB3 NC3 NBLK MI3 ST3 HE3 ERR3.
      assert (R8 : (r8 = 0 \/ r8 = -104)%Z) by (destruct Rv as [(E & _)|(E & _)]; lia).

      eapply sreach_evt. { eapply (ph_new6 P q lo ws WSL r8 H nA tl ncap id j0'); try eassumption; try LiaTuning.alia. all: Z.div_mod_to_equations; lia. }
      intros ms' (m5 & [(R8NZ & -> & ->)|(pad & -> & -> & MU5 & WM5 & MI5 & HC5 & NC5)]).
      {
        destruct Rv as [(E & _)|(_ & -> & -> & -> & -> & -> & ->)]; [exfalso; lia|].
        eapply (ph_cleanup cur cur2 meth ns hs H nA tl ncap 0 0 0 kH (Some nk) None nbs []); try eassumption; try LiaTuning.alia.
        all: try (exists e4; exact ERR4).
        all: try (exists zb; exact ZB4).
        all: try (apply (proj2 (phFX_Y q cur0 len CUR0 m4)); split; [| do 2 eexists; exact Q16b];
                  unfold phFY; split; [eexists; exact Q0|]; split; [eexists; exact Q12|]; split; [do 2 eexists; exact Q32|]; split; [do 2 eexists; exact Q48| eexists; exact Q68]).
        all: try (unfold p_msg; rewrite EOK; cbn; split; [exact MBC|]; split; [split; [apply KSUB4; apply KSUB3; right; exact (BSUB _ MOB)| exact MBLK4]|]; repeat split; try assumption; lia).
        all: try exact (conj MC METHR).
        all: try exact (conj (ex_intro _ padw VRC) VR).
        all: try exact (conj CC CR).
        all: try (intros b Hb; apply KSUB4; apply KSUB3; right; apply BSUB; exact Hb).
        all: try (apply KSUB4; exact HIN3).
        all: try (intros b Hb; exact (proj2 (OBH b Hb))).
        all: try (cbn; split; [apply KSUB4; exact NIN| exact NBLK4]).
        all: try (intros k Ek; injection Ek as <-; split; [intros b Hb E; exact (FRESHn b (or_intror (BSUB _ Hb)) E)| exact NEHN]).
        all: try (unfold mbuf_cells; exact VC4).
        all: try (cbn; repeat split; reflexivity).
        all: try (intros k Ek; discriminate).
        }

      destruct Rv as [(_ & -> & VPFX)|(E & _)]; [| exfalso; lia].
      destruct okv as [vk|]; [| exfalso; cbn in OWNv; lia]. cbn in OWNv, FRESHv. destruct OWNv as [VIN VB].
      assert (VN : nth_error vbs (Z.to_nat l') = Some (Z_to_bv 8 0)) by (eapply nul_of_firstn; [exact (VPFX ltac:(lia))| exact VS2| lia]).
      destruct (ai_block_range rsegs AI _ _ _ _ HR4 VIN) as (VR1 & VR2 & VR3 & VR4 & _). cbn in VR1, VR2, VR3, VR4.
      assert (HIN4 : In bHn LB3) by (apply KSUB4; exact HIN3).
      assert (NIN4 : In (nk, nA, ncap + 1) LB3) by (apply KSUB4; exact NIN).
      assert (NEVH : (vk, vA, vcap + 1) <> bHn) by (intros E; exact (FRESHv _ HIN3 (eq_sym E))).
      assert (NEVN : (vk, vA, vcap + 1) <> (nk, nA, ncap + 1)) by (intros E; exact (FRESHv _ NIN (eq_sym E))).
      pose proof (ai_blocks_disjoint rsegs AI _ _ _ _ _ HR4 VIN HIN4 NEVH) as DJVH. cbn in DJVH.

      assert (OBH4 : forall b0, In b0 ((vk, vA, vcap + 1) :: (nk, nA, ncap + 1) :: OB) -> In b0 LB3 /\ b0 <> bHn).
      { intros b0 [<-|Hb0]; [split; [exact VIN| exact NEVH]|]. destruct (OBH3 b0 Hb0) as [H1 H2]. split; [apply KSUB4; exact H1| exact H2]. }
      assert (FR5 : RHEAP rsegs AI s3 LB3 m5 /\ RENV rsegs AI m5 B /\ hpx AI (WH okm A cap) LBK (q + 240) m4 m5 /\ heap_pres AI ((vk, vA, vcap + 1) :: (nk, nA, ncap + 1) :: OB) B m4 m5).
      { split. { eapply (ai_heap_frame rsegs AI); [exact HR4| exact MU5| exact WM5|]. apply Forall_cons; [| apply Forall_nil]. right; right; right. exists bHn. split; [exact HIN4| cbn; lia]. }
        split. { eapply (ai_env_frame rsegs AI); [exact HR4| exact HE4| exact MU5| exact WM5|]. apply Forall_cons; [| apply Forall_nil]. right; right; right. exists bHn. split; [exact HIN4| cbn; lia]. }
        split. { eapply (hpx_seg rsegs AI); [exact LOK| exact HR4| intros b Hb; apply KSUB4; apply KSUB3; right; apply BSUB; apply LBKOB; exact Hb| exact MU5| exact WM5|].
                 apply Forall_cons; [| apply Forall_nil]. right; left. cbn. intros a Ha.
                 eapply (fresh_block_not_client rsegs AI); [exact LOK| exact HR4| exact HIN4| intros b0 Hb0; apply OBH4; right; right; apply LBKOB; exact Hb0| lia| cbn; lia]. }
        eapply (heap_pres_seg rsegs AI); [exact LOK| exact HR4| intros b Hb; exact (proj1 (OBH4 b Hb))| exact MU5| exact WM5|].
        apply Forall_cons; [| apply Forall_nil]. right. cbn. intros a Ha. eapply (fresh_block_not_client rsegs AI); [exact LOK| exact HR4| exact HIN4| exact OBH4| lia| cbn; lia]. }
      destruct FR5 as (HR5 & HE5 & HPX5 & HPB5).
      pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPB5 VB ltac:(eapply client_range_block; [left; reflexivity| cbn; lia| cbn [cells_size csize Nat.add blk_addr blk_size fst snd]; lia])) as VB5.
      pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPB5 NBLK4 ltac:(eapply client_range_block; [right; left; reflexivity| cbn; lia| cbn [cells_size csize Nat.add blk_addr blk_size fst snd]; lia])) as NB5.
      pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HPB5 MBLK4 ltac:(eapply client_range_block; [right; right; exact MOB| cbn; lia| cbn [cells_size csize Nat.add blk_addr blk_size fst snd]; lia])) as MBLK5.
      pose proof (heap_pres_u64arr _ _ _ _ _ _ HPB5 TAB4 (tab_client _ _)) as TAB5.
      pose proof (heap_pres_bytes_at rsegs AI _ _ _ _ _ _ HPB5 ZB4 (zero_client _ _)) as ZB5.
      pose proof (p_hlist_pres AI P ws WSL m4 m5 _ _ B ns hs _ HL4 MU5 WM5 ltac:(cbn; lia) HPB5 ltac:(intros b Hb; right; right; subst OB; apply in_or_app; left; exact Hb)) as HL5.
      clear VB NBLK4 MBLK4 TAB4 ZB4 HL4.
      transport_after_call rsegs m4 m5 MU5 WM5. clear MI4.
      pose proof HL5 as HLc. destruct HLc as (LC5 & FLC5 & FF5 & DL5 & HS5 & _ & _ & _ & _).
      replace (P + 312)%Z with (P + 288 + 24)%Z in LC5, DL5 by lia. replace (P + 344)%Z with (P + 288 + 56)%Z in FLC5 by lia.
      set (NEWB := [bHn; (vk, vA, vcap + 1); (nk, nA, ncap + 1)]).
      set (LBK' := (hdrs_blocks AI hs ++ LBK) ++ NEWB).
      assert (EOB : map fst ns ++ LBK' = OB ++ NEWB) by (subst LBK' OB; unfold hl_blocks; repeat rewrite <- app_assoc; reflexivity).
      assert (ND3 : NoDup (map blk_id ((vk, vA, vcap + 1) :: (nk, nA, ncap + 1) :: bHn :: OB))).
      { eapply (fresh_ids_cons s3 LB3 m4); [exact HR4| exact VIN| | |].
        - intros b [<-|[<-|Hb]]; [exact NIN4| exact HIN4| apply KSUB4; apply KSUB3; right; apply BSUB; exact Hb].
        - intros b Hb E. refine (FRESHv b _ E). destruct Hb as [<-|[<-|Hb]]; [exact NIN| exact HIN3| apply KSUB3; right; apply BSUB; exact Hb].
        - eapply (fresh_ids_cons s2 LB2 m3); [exact HR3| exact NIN| | |].
          + intros b [<-|Hb]; [exact HIN3| apply KSUB3; right; apply BSUB; exact Hb].
          + intros b Hb E. refine (FRESHn b _ E). destruct Hb as [<-|Hb]; [left; reflexivity| right; apply BSUB; exact Hb].
          + eapply (fresh_nodup AI); [exact HR1| exact BSUB| exact ND]. }
      assert (NDK : NoDup (map blk_id (map fst ns ++ LBK'))).
      { rewrite EOB. subst NEWB. rewrite (Permutation_map blk_id (perm3 OB bHn (vk, vA, vcap + 1) (nk, nA, ncap + 1))). exact ND3. }
      assert (KSUBK : bsub AI LBK' LB3).
      { subst LBK' NEWB. intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|[<-|[<-|[<-|[]]]]]; [| exact HIN4| exact VIN| exact NIN4].
        apply KSUB4. apply KSUB3. right. apply BSUB. subst OB. unfold hl_blocks. rewrite <- app_assoc. apply in_or_app. right. exact Hb. }
      eapply sreach_bind.
      { eapply (ListAddTail_spec AI AC LOK MALPC) with (lo := lo) (B := B) (L := (P + 288)%Z) (IT := H) (fk := 0) (ns := ns) (LBK := LBK') (LB := LB3) (s := s3);
          rewrite ?EQ; try eassumption; try reflexivity; unfold zlength in *; try lia.
        intros b Hb. apply KSUB4. apply KSUB3. right. apply BSUB. subst OB. apply in_or_app. left. apply in_or_app. left. exact Hb. }
      intros s4 LB4 ms4 Q4. unfold ListAddTail_post in Q4. rewrite !EQ in Q4. destruct_exs Q4.
      destruct Q4 as (-> & MI6 & ST6 & HE6 & [e6 ERR6] & HPX6 & HR6 & KSUB6 & NSUB6 & ND6 & LC6 & FLC6 & DL6 & RES).
      lazymatch type of MI6 with mem_inv _ ?mm => rename mm into m6 end.
      lazymatch type of LC6 with rw_cells _ _ _ (lhead_cells (hd_addr _ ?n _) _ _) => rename n into ns' end.
      lazymatch goal with |- SREACH _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?r) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) _ _ => rename r into r9 end.
      replace (ret_pc (Z_to_bv 64 0x14f10)) with (Z_to_bv 64 0x14f10) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      replace (P + 288 + 24)%Z with (P + 312)%Z in LC6, DL6 by lia. replace (P + 288 + 56)%Z with (P + 344)%Z in FLC6 by lia.

      assert (HP6 : heap_pres AI LBK' (P + 344) m5 m6).
      { eapply (heap_pres_of_hpx rsegs AI [(P + 288, P + 288 + 56)]%Z). { eapply (hpx_weaken rsegs AI); [exact HPX6| intros xx Hxx; exact Hxx| lia| intros b Hb; exact Hb]. }
        intros a Ha Hc. cbn. split; [| exact I].
        destruct Hc as [Hc|[(lo' & hi' & STc & Hr)|(b & Hb & Hr)]]; [lia| |].
        - destruct (lo_static_img rsegs AI LOK lo' hi' STc) as (w & Hw & W1 & W2). pose proof (lo_img_ceiling rsegs AI LOK w Hw). lia.
        - destruct (ai_block_range rsegs AI _ _ _ _ HR4 (KSUBK b Hb)) as (_ & _ & _ & R4 & _). lia. }
      Ltac mv6 HPX6 H := let H' := fresh in pose proof (hpx_rw_cells rsegs AI _ _ _ _ _ _ _ HPX6 H ltac:(apply client_range_above; generalize QP; clear - q P; cbn; intros; lia) ltac:(generalize QP; clear - q P; cbn; intros; lia)) as H'; clear H; rename H' into H.
      mv6 HPX6 FSH. mv6 HPX6 Q0. mv6 HPX6 Q12. mv6 HPX6 Q16b. mv6 HPX6 Q32. mv6 HPX6 Q48. mv6 HPX6 Q68. mv6 HPX6 MC. mv6 HPX6 VRC.
      pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HP6 FF5 ltac:(apply client_range_above; cbn; lia)) as FF6.
      pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HP6 SCN ltac:(apply client_range_above; cbn; lia)) as SCN6.
      pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HP6 MBC ltac:(apply client_range_above; cbn; lia)) as MBC6.
      pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HP6 CC ltac:(apply client_range_above; cbn; lia)) as CC6.
      assert (INK_H : In bHn LBK') by (subst LBK' NEWB; apply in_or_app; right; left; reflexivity).
      assert (INK_V : In (vk, vA, vcap + 1) LBK') by (subst LBK' NEWB; apply in_or_app; right; right; left; reflexivity).
      assert (INK_N : In (nk, nA, ncap + 1) LBK') by (subst LBK' NEWB; apply in_or_app; right; right; right; left; reflexivity).
      assert (INK_M : In (km, A, cap + 1) LBK') by (subst LBK'; apply in_or_app; left; apply in_or_app; right; apply MSGK; exact EOK).
      pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HP6 HC5 ltac:(eapply client_range_block; [exact INK_H| cbn; lia| cbn; lia])) as HC6.
      pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HP6 NC5 ltac:(eapply client_range_block; [exact INK_H| cbn; lia| unfold mbuf_cells; cbn; lia])) as NC6.
      pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HP6 VC4 ltac:(eapply client_range_block; [exact INK_H| cbn; lia| unfold mbuf_cells; cbn; lia])) as VC6.
      pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HP6 VB5 ltac:(eapply client_range_block; [exact INK_V| cbn; lia| cbn [cells_size csize Nat.add blk_addr blk_size fst snd]; lia])) as VB6.
      pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HP6 NB5 ltac:(eapply client_range_block; [exact INK_N| cbn; lia| cbn [cells_size csize Nat.add blk_addr blk_size fst snd]; lia])) as NB6.
      pose proof (heap_pres_rw_cells rsegs AI _ _ _ _ _ _ HP6 MBLK5 ltac:(eapply client_range_block; [exact INK_M| cbn; lia| cbn [cells_size csize Nat.add blk_addr blk_size fst snd]; lia])) as MBLK6.
      pose proof (heap_pres_u64arr _ _ _ _ _ _ HP6 TAB5 (tab_client _ _)) as TAB6.
      pose proof (heap_pres_bytes_at rsegs AI _ _ _ _ _ _ HP6 ZB5 (zero_client _ _)) as ZB6.
      assert (HS6 : hdrs_mem AI m6 hs).
      { eapply (hdrs_mem_heap_pres AI); [exact HS5| exact HP6|]. intros b Hb. subst LBK'. apply in_or_app. left. apply in_or_app. left. exact Hb. }
      assert (HPX06 : hpx AI (WH okm A cap) LBK (q + 240) m0 m6).
      { eapply (hpx_trans rsegs AI); [exact HPX04|]. eapply (hpx_trans rsegs AI); [exact HPX5|].
        eapply (hpx_weaken rsegs AI); [exact HPX6| | lia| intros b Hb; subst LBK'; apply in_or_app; left; apply in_or_app; right; exact Hb].
        unfold WH. intros xo OX. cbn [outside] in OX |- *. split; [lia| exact I]. }
      clear FF5 SCN MBC CC HC5 NC5 VC4 VB5 NB5 MBLK5 TAB5 ZB5 HS5 HL5 LC5 FLC5 DL5 HPX04 HPX5 HPX6 HP6 HPB5 MI5.
      assert (R9 : (0 <= r9 < 2^64)%Z).
      { destruct RES as [(-> & _)|(k & NZ & -> & ->)]; [lia|]. destruct (ai_block_range rsegs AI _ _ _ _ HR6 (or_introl eq_refl)) as (R1 & _ & _ & R4 & _). cbn in R1, R4. lia. }
      eapply sreach_evt. { eapply (ph_new7 P q ws WSL r9); lia. }
      intros ms' ->.
      destruct RES as [(-> & -> & ->)|(knd & R9NZ & -> & ->)].
      {
        cbn [Z.eqb].
        eapply (ph_cleanup cur cur2 meth ns hs H nA tl ncap vA l' vcap kH (Some nk) (Some vk) nbs vbs); try eassumption; try LiaTuning.alia.
        all: try (exists e6; exact ERR6).
        all: try (exists zb; exact ZB6).
        all: try (apply (proj2 (phFX_Y q cur0 len CUR0 m6)); split; [| do 2 eexists; exact Q16b];
                  unfold phFY; split; [eexists; exact Q0|]; split; [eexists; exact Q12|]; split; [do 2 eexists; exact Q32|]; split; [do 2 eexists; exact Q48| eexists; exact Q68]).
        all: try (unfold p_msg; rewrite EOK; cbn; split; [exact MBC6|]; split; [split; [apply KSUB6; exact INK_M| exact MBLK6]|]; repeat split; try assumption; lia).
        all: try exact (conj MC METHR).
        all: try exact (conj (ex_intro _ padw VRC) VR).
        all: try exact (conj CC6 CR).
        all: try (split; [exact LC6| split; [exact FLC6| split; [exact FF6| split; [exact DL6| split; [exact HS6| destruct HL as (_ & _ & _ & _ & _ & REST); exact REST]]]]]).
        all: try (apply KSUB6; exact INK_H).
        all: try (intros b Hb; apply KSUB4; apply KSUB3; right; apply BSUB; exact Hb).
        all: try (intros b Hb; exact (proj2 (OBH b Hb))).
        all: try (cbn; split; [apply KSUB6; exact INK_N| exact NB6]).
        all: try (cbn; split; [apply KSUB6; exact INK_V| exact VB6]).
        all: try (intros k Ek; injection Ek as <-; split; [intros b Hb E; exact (FRESHn b (or_intror (BSUB _ Hb)) E)| exact NEHN]).
        all: try (intros k Ek; injection Ek as <-; split; [intros b Hb E; refine (FRESHv b _ E); apply KSUB3; right; apply BSUB; exact Hb| split; [exact NEVH| intros k' Ek'; injection Ek' as <-; exact NEVN]]).
        }

      replace (r9 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact R9NZ).
      set (hnew := {| hA := H; hk := kH; hid := id; nA := nA; nlen := tl; ncap := ncap; nk := nk; vA := vA; vlen := l'; vcap := vcap; vk := vk |} : hdr).
      set (ns' := ns ++ [(knd, r9, 24, H)]) in *.
      assert (HLn : p_hlist AI m6 P ns' (hs ++ [hnew]) (X0 + 2 * (cur2 - cur0))).
      { split; [exact LC6|]. split; [exact FLC6|]. split; [exact FF6|]. split; [exact DL6|].
        split. { apply hdrs_mem_app. split; [exact HS6|]. cbn [hdrs_mem]. split; [| split; [| exact I]].
                 - unfold hdro_mem. subst hnew. cbn [H_obj.hA H_obj.hk H_obj.hid H_obj.nA H_obj.nlen H_obj.ncap H_obj.nk H_obj.vA H_obj.vlen H_obj.vcap H_obj.vk].
                   split; [exists pad; exact HC6|]. split; [exact VC6|]. split; [exists vbs; split; [exact VB6| exact VN]|]. split; [exact NC6|]. exists nbs. split; [exact NB6| exact NN].
                 - unfold hdro_pure. subst hnew. cbn. lia. }
        split. { subst ns' hnew. rewrite !map_app. cbn [map snd H_obj.hA]. rewrite ITEMS. reflexivity. }
        split. { intros h0 Hh0. apply in_app_or in Hh0. destruct Hh0 as [Hh0|[<-|[]]].
                 - destruct (HB h0 Hh0). lia.
                 - subst hnew. cbn. lia. }
        subst ns'. unfold zlength in *. rewrite length_app. cbn [length]. lia. }
      assert (EHL : hl_blocks AI ns' (hs ++ [hnew]) ++ LBK = (map fst ns ++ [(knd, r9, 24)]) ++ (hdrs_blocks AI hs ++ NEWB) ++ LBK).
      { subst ns' hnew NEWB. unfold hl_blocks. rewrite map_app, hdrs_blocks_app, hdrs_blocks_cons.
        cbn [map fst hdrs_blocks concat hblocks H_obj.hA H_obj.hk H_obj.vA H_obj.vk H_obj.vcap H_obj.nA H_obj.nk H_obj.ncap app]. unfold bHn.
        repeat rewrite <- app_assoc. cbn [app]. reflexivity. }
      assert (BSn : bsub AI (hl_blocks AI ns' (hs ++ [hnew]) ++ LBK) ((knd, r9, 24) :: LB3)).
      { rewrite EHL. intros b Hb. apply in_app_or in Hb. destruct Hb as [Hb|Hb].
        - apply NSUB6. subst ns'. rewrite map_app. exact Hb.
        - apply KSUB6. subst LBK'. apply in_app_or in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [| left; apply in_or_app; right; exact Hb].
          apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [left; apply in_or_app; left; exact Hb| right; exact Hb]. }
      assert (NDn : NoDup (map blk_id (hl_blocks AI ns' (hs ++ [hnew]) ++ LBK))).
      { rewrite EHL. subst ns' LBK'.
        assert (PM : Permutation (map blk_id (map fst (ns ++ [(knd, r9, 24, H)]) ++ ((hdrs_blocks AI hs ++ LBK) ++ NEWB)))
                                 (map blk_id ((map fst ns ++ [(knd, r9, 24)]) ++ (hdrs_blocks AI hs ++ NEWB) ++ LBK))).
        { apply Permutation_map. rewrite map_app. cbn [map fst]. apply Permutation_app_head. repeat rewrite <- app_assoc. apply Permutation_app_head. apply Permutation_app_comm. }
        rewrite <- PM. exact ND6. }
      eapply (IH s4 ((knd, r9, 24) :: LB3) m6 cur2 meth ns' (hs ++ [hnew])); [lia|]. unfold ph_inv.
      split; [exact HR6|]. split; [exact HE6|]. split; [exact MI6|]. split; [exact ST6|]. split; [exists e6; exact ERR6|].
      split; [exact FSH|]. split.
      { apply (proj2 (phFX_Y q cur0 len CUR0 m6)). split; [| do 2 eexists; exact Q16b].
        unfold phFY. split; [eexists; exact Q0|]. split; [eexists; exact Q12|]. split; [do 2 eexists; exact Q32|]. split; [do 2 eexists; exact Q48| eexists; exact Q68]. }
      split; [exact SCN6|]. split; [lia|].
      split. { unfold p_msg. rewrite EOK. cbn. split; [exact MBC6|]. split; [split; [apply KSUB6; exact INK_M| exact MBLK6]|]. repeat split; try assumption; lia. }
      split; [split; [exact MC| exact METHR]|]. split; [exact METHD|]. split; [split; [eexists; exact VRC| exact VR]|]. split; [split; [exact CC6| exact CR]|].
      split; [exact HLn|]. split; [exact BSn|]. split; [exact NDn|]. split; [exact TAB6|]. split; [exists zb; exact ZB6|].
      split; [exact HPX06|]. exact MSGK.
    Qed.
  End NEW.

  #[using="LOK ZST ws QLO LO0 CEIL QP P8 WSL"] Lemma front_keep : forall (A cap : Z) (okm : option K) s LB m m' e zb,
    RHEAP rsegs AI s LB m -> (forall k, okm = Some k -> In (k, A, cap + 1) LB) ->
    munch ((lo, q + 240) :: (P + 4, P + 8) :: (P + 448, P + 452) :: (P + 488, P + 496) :: mwin AI okm A cap)%Z m m' -> wmono rsegs m m' ->
    rw_cells rsegs m (al_errno L_) [C4 e] -> bytes_at rsegs m ZERO_ADDR [zb] ->
    rw_cells rsegs m' (al_errno L_) [C4 e] /\ bytes_at rsegs m' ZERO_ADDR [zb].
  Proof.
    intros A cap okm s LB m m' e zb HR HK MU WM ERR ZB. pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
    destruct (lo_errno_img rsegs AI LOK) as (we & Hwe & WE1 & WE2). pose proof (lo_img_ceiling rsegs AI LOK we Hwe) as WE3.
    destruct ZST as (l2 & h2 & ST2 & Z1 & Z2). destruct (lo_static_img rsegs AI LOK l2 h2 ST2) as (w2 & Hw2 & Y1 & Y2). pose proof (lo_img_ceiling rsegs AI LOK w2 Hw2) as Y3.
    pose proof (rw_cells_bound rsegs _ _ _ ERR) as EB. cbn [cells_size csize Nat.add] in EB.
    assert (MW : forall k, okm = Some k -> ((A + (cap + 1) <= al_errno L_ \/ al_errno L_ + 4 <= A) /\ (A + (cap + 1) <= ZERO_ADDR \/ ZERO_ADDR + 1 <= A))%Z).
    { intros k Ek. destruct (ai_block_range rsegs AI _ _ _ _ HR (HK k Ek)) as (_ & _ & _ & _ & FA). rewrite Forall_forall in FA.
      pose proof (FA _ Hwe) as X1. pose proof (FA _ Hw2) as X2. cbn in X1, X2. lia. }
    destruct okm as [k|].
    - destruct (MW k eq_refl) as [M1 M2]. split.
      + eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. cbn. lia.
      + eapply bytes_at_transport; [exact ZB| exact MU|]. cbn. lia.
    - split.
      + eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. cbn. lia.
      + eapply bytes_at_transport; [exact ZB| exact MU|]. cbn. lia.
  Qed.

  Section LOOP.
    Variables (A cap : Z) (okm : option K) (bs : list byte) (LBK : list BLK) (err hack pos entp clen csz esp : Z) (m0 : mem).
    Variables (ra s0w s1w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w gp : word) (F : bvmap 5 word) (fc : bv 32).
    Notation POST := (ph_post ra s0w s1w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w gp F fc A cap okm bs LBK err hack pos entp clen csz esp m0).
    Notation INV := (ph_inv ra s0w s1w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w A cap okm bs LBK err hack pos entp clen csz esp m0).
    Notation TP := (wz (al_tp L_)).

    #[using="AC LOK MALPC FREEPC REALLOCPC IMGW1 IMGW2 TABST ZST QLO QLO2 STK0 LO0 CEIL QP PB BHI P8 WSL CUR0 XMAX METHE"] Lemma ph_cont : forall (cur meth X : Z) (ns : list (BLK * Z)) (hs : list hdr) (LB : list BLK) s m e zb ms',
      (forall s' LB' m' (cur' meth' : Z) ns' hs' x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s6' s7' s9' t3' t4' t5' t6',
         (cur + 2 <= cur')%Z -> INV s' LB' m' cur' meth' ns' hs' ->
         SREACH AI POST (PRS 0x14cd4 x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s6' s7' s9' t3' t4' t5' t6' gp TP F fc m') s' LB') ->
      front_post AI P q lo ws isreq maj min len ra s0w s1w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w gp TP F fc A cap okm bs cur meth err hack pos entp clen csz esp ns hs X LB m ms' ->
      (X = X0 + 2 * (cur - cur0))%Z -> (cur0 <= cur <= len)%Z -> (meth = methE \/ meth = 11) ->
      RHEAP rsegs AI s LB m -> RENV rsegs AI m B -> rw_cells rsegs m (al_errno L_) [C4 e] -> bytes_at rsegs m ZERO_ADDR [zb] ->
      p_ctl m P err hack pos entp clen csz esp ->
      bsub AI (hl_blocks AI ns hs ++ LBK) LB -> NoDup (map blk_id (hl_blocks AI ns hs ++ LBK)) ->
      hpx AI (WH okm A cap) LBK (q + 240) m0 m -> (forall k, okm = Some k -> In (k, A, cap + 1) LBK) ->
      SREACH AI POST ms' s LB.
    Proof.
      intros until ms'. intros IH FP EX CUR METHD HR HE ERR ZB CTL BSUB ND HPX MSGK. subst X.
      pose proof alloc_ceiling_bounds as CE. pose proof alloc_ceiling_aligned8 as CE8.
      unfold front_post in FP. destruct FP as (m' & FP). destruct_exs FP. destruct FP as (MU & WM & MI' & TAB' & MSG' & VER' & HL' & CASES).
      assert (HK : forall k, okm = Some k -> In (k, A, cap + 1) LB) by (intros k Ek; apply BSUB; apply in_or_app; right; apply MSGK; exact Ek).
      destruct (front_keep A cap okm s LB m m' e zb HR HK MU WM ERR ZB) as [ERR' ZB'].
      destruct (seg_frames s LB m m' _ LBK A cap okm HR HE MU WM HK ltac:(intros b Hb; apply BSUB; apply in_or_app; right; exact Hb)) as (HR' & HE' & HPX').
      { unfold WH. repeat (apply Forall_cons; [first [left; cbn; lia | right; cbn; lia]|]).
        destruct okm; cbn; [| apply Forall_nil]. apply Forall_cons; [right; cbn; lia| apply Forall_nil]. }
      destruct CASES as [EX|[EXI|NW]].
      -
        destruct EX as (r & cur' & meth' & pos' & -> & ST' & SC' & ME' & CT' & CURR & MD & RR & PR & RP & RO).
        apply sreach_ret. unfold ph_post. do 14 eexists. exists m', r, cur', meth', err, pos', ns, hs.
        split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HE'|]. split; [exists e; exact ERR'|].
        split; [eapply (hpx_trans rsegs AI); [exact HPX| exact HPX']|]. split; [exact HR'|].
        split; [exact SC'|]. split; [lia|]. split; [exact MSG'|]. split; [exact ME'|]. split; [destruct MD as [-> | ->]; [exact METHD| right; reflexivity]|].
        split; [exact VER'|]. split; [exact CT'|]. split; [left; reflexivity|].
        split; [eapply p_hlist_mono; [exact HL'| lia]|]. split; [exact BSUB|]. split; [exact ND|]. split; [exact TAB'|]. split; [exists zb; exact ZB'|].
        split; [exact RR|]. split; [exact RP| exact RO].
      -
        destruct EXI as (h & o & l & cur2 & meth' & x1e & a0e & s6e & s7e & s9e & -> & Hh & ST' & FS' & FY' & Q16' & SC' & ME' & CT' & MD & C2 & LR & OR & OL & OKM).
        eapply (ph_exist A cap okm bs LBK err hack pos entp clen csz esp m0 ra s0w s1w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w gp F fc cur cur2 o l meth' h ns hs LB s);
          try eassumption; try LiaTuning.alia.
        all: try (destruct MD as [-> | ->]; [exact METHD| right; reflexivity]).
        all: try (exists e; exact ERR').
        all: try (exists zb; exact ZB').
        all: try (eapply (hpx_trans rsegs AI); [exact HPX| exact HPX']).
      -
        destruct NW as (id & o & l & cur2 & meth' & tl & x1e & a0e & s6e & s7e & -> & ST' & FS' & FY' & Q16' & Q32' & SC' & ME' & CT' & MD & C2 & LR & OR & OL & OKM & TL1 & TLT & IDR).
        eapply (ph_newhdr A cap okm bs LBK err hack pos entp clen csz esp m0 ra s0w s1w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w gp F fc cur cur2 o l tl meth' id ns hs LB s);
          try eassumption; try LiaTuning.alia.
        all: try (destruct MD as [-> | ->]; [exact METHD| right; reflexivity]).
        all: try (exists e; exact ERR').
        all: try (exists zb; exact ZB').
        all: try (eapply (hpx_trans rsegs AI); [exact HPX| exact HPX']).
    Qed.

    Hypothesis Q8 : (q mod 8 = 0)%Z.

    #[using="AC LOK MALPC FREEPC REALLOCPC strncasecmp_spec IMGW1 IMGW2 TABST ZST QLO QLO2 STK0 LO0 CEIL QP PB BHI P8 Q8 WSL HID TS CUR0 XMAX METHE"] Lemma ph_loop : forall (k : nat) s LB m (cur meth : Z) (ns : list (BLK * Z)) (hs : list hdr)
        x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6,
      (len - cur < Z.of_nat k)%Z -> INV s LB m cur meth ns hs ->
      SREACH AI POST (PRS 0x14cd4 x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s9 t3 t4 t5 t6 gp TP F fc m) s LB.
    Proof.
      induction k as [|k IHk]; intros until t6; intros HK INV;
        destruct INV as (HR & HE & MI & ST & [e ERR] & FSH & FX & SCN & CUR & MSG & METH & METHD & VER & CTL & HL & BSUB & ND & TAB & [zb ZB] & HPX & MSGK); [lia|].
      eapply sreach_evt.
      { eapply (ph_front AI LOK strncasecmp_spec IMGW1 IMGW2 P q lo B ws isreq maj min cur0 len QLO LO0 CEIL QP PB BHI P8 Q8 WSL HID TS CUR0 A cap okm bs LBK cur meth err hack pos entp clen csz esp); try eassumption; try LiaTuning.alia. }
      intros ms' FP. eapply ph_cont; try eassumption; try reflexivity.
      intros until t6'. intros HC INV'. eapply IHk. 2: exact INV'. lia.
    Qed.

    #[using="AC LOK MALPC FREEPC REALLOCPC strncasecmp_spec IMGW1 IMGW2 TABST ZST QLO QLO2 STK0 LO0 CEIL QP PB BHI P8 Q8 WSL HID TS CUR0 XMAX METHE"] Theorem ph_main : forall (ns : list (BLK * Z)) (hs : list hdr) (LB : list BLK) s t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (e : word),
      m0 = m0 ->
      RHEAP rsegs AI s LB m0 -> RENV rsegs AI m0 B -> mem_inv rsegs m0 -> stk rsegs m0 lo (q + 240) -> rw_cells rsegs m0 (al_errno L_) [C4 e] ->
      p_scan m0 P cur0 -> p_msg AI m0 LB P A len cap okm bs -> p_meth m0 P methE -> p_ver m0 P isreq maj min -> p_ctl m0 P err hack pos entp clen csz esp ->
      p_hlist AI m0 P ns hs X0 -> bsub AI (hl_blocks AI ns hs ++ LBK) LB -> NoDup (map blk_id (hl_blocks AI ns hs ++ LBK)) ->
      ph_statics m0 -> (forall k, okm = Some k -> In (k, A, cap + 1) LBK) ->
      SREACH AI POST (MS (mkR ra (wz (q + 240)) gp TP t0 t1 t2 s0w s1w (wz P) a1 a2 a3 a4 a5 a6 a7 s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w t3 t4 t5 t6)
                         F (wz parse_headers_entry) fc None m0 (seg_rom rsegs)) s LB.
    Proof.
      intros until e. intros _ HR HE MI ST ERR SCN MSG METH VER CTL HL BSUB ND [TAB [zb ZB]] MSGK.
      eapply sreach_evt.
      { eapply (ph_frontE AI LOK strncasecmp_spec IMGW1 IMGW2 P q lo B ws isreq maj min cur0 len QLO LO0 CEIL QP PB BHI P8 Q8 WSL HID TS CUR0 A cap okm bs LBK cur0 methE err hack pos entp clen csz esp); try eassumption; try LiaTuning.alia. }
      intros ms' FP. eapply (ph_cont cur0 methE X0 ns hs LB s m0 e zb); try eassumption; try LiaTuning.alia.
      all: try (intros until t6'; intros HC INV'; eapply (ph_loop (Datatypes.S (Z.to_nat (len - cur0)))); [| exact INV']; rewrite Nat2Z.inj_succ, Z2Nat.id by lia; lia).
      all: try (left; reflexivity). all: try apply hpx_refl.
    Qed.
  End LOOP.
End W.

Definition parse_headers_stmt {HCEIL : HasCeiling} (AI : alloc_if rsegs) : Prop :=
  forall (P q lo B : Z) (ws : list word) (isreq maj min cur0 X0 len methE : Z)
         (A cap : Z) (okm : option (ai_K rsegs AI)) (bs : list byte) (LBK : list (block (ai_K rsegs AI))) (err hack pos entp clen csz esp : Z)
         (ns : list (block (ai_K rsegs AI) * Z)) (hs : list (hdr AI)) (LB : list (block (ai_K rsegs AI))) (s : ai_PS rsegs AI)
         (ra gp s0w s1w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (e : word),
    (lo + 368 <= q)%Z -> (lo <= q - 64 - al_stack (ai_L rsegs AI))%Z -> (0 <= al_stack (ai_L rsegs AI))%Z -> (0x5d000 <= lo)%Z -> (alloc_ceiling <= lo)%Z ->
    (q + 240 <= P)%Z -> (P + 504 <= B)%Z -> (B < 2^63)%Z -> (P mod 8 = 0)%Z -> (q mod 8 = 0)%Z ->
    length ws = 66%nat -> (forall i, (0 <= i < 33)%Z -> exists id, nth_error ws (Z.to_nat (2 * i + 1)) = Some (wz id) /\ (0 <= id < 64)%Z) -> table_strings ws 33 lo ->
    (0 <= cur0 <= len)%Z -> (0 <= X0)%Z -> (X0 + 2 * (len - cur0) <= VMAX)%Z -> (0 <= methE <= 11)%Z ->
    RHEAP rsegs AI s LB m -> RENV rsegs AI m B -> mem_inv rsegs m -> stk rsegs m lo (q + 240) -> rw_cells rsegs m (al_errno (ai_L rsegs AI)) [C4 e] ->
    p_scan m P cur0 -> p_msg AI m LB P A len cap okm bs -> p_meth m P methE -> p_ver m P isreq maj min -> p_ctl m P err hack pos entp clen csz esp ->
    p_hlist AI m P ns hs X0 -> bsub AI (hl_blocks AI ns hs ++ LBK) LB -> NoDup (map blk_id (hl_blocks AI ns hs ++ LBK)) ->
    ph_statics ws m -> (forall k, okm = Some k -> In (k, A, cap + 1) LBK) ->
    SREACH AI (ph_post AI P q lo B ws isreq maj min cur0 X0 len methE ra s0w s1w s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w gp F fc A cap okm bs LBK err hack pos entp clen csz esp m)
      (MS (mkR ra (wz (q + 240)) gp (wz (al_tp (ai_L rsegs AI))) t0 t1 t2 s0w s1w (wz P) a1 a2 a3 a4 a5 a6 a7 s2w s3w s4w s5w s6w s7w s8w s9w s10w s11w t3 t4 t5 t6)
          F (wz parse_headers_entry) fc None m (seg_rom rsegs)) s LB.

Theorem parser_parse_headers_spec {HCEIL : HasCeiling} : forall (AI : alloc_if rsegs) (AC : alloc_contracts AI),
  layout_ok AI -> al_malloc_pc (ai_L rsegs AI) = 0x180f0 -> al_free_pc (ai_L rsegs AI) = 0x17fb0 -> al_realloc_pc (ai_L rsegs AI) = 0x1995c ->
  strncasecmp_stmt -> In (0x10000, 0x2a000)%Z (al_img (ai_L rsegs AI)) -> In (0x2a000, 0x5d000)%Z (al_img (ai_L rsegs AI)) ->
  (exists lo hi, al_client_static (ai_L rsegs AI) lo hi /\ lo <= TAB_HDR /\ TAB_HDR + 528 <= hi)%Z ->
  (exists lo hi, al_client_static (ai_L rsegs AI) lo hi /\ lo <= ZERO_ADDR /\ ZERO_ADDR + 1 <= hi)%Z ->
  parse_headers_stmt AI.
Proof.
  intros AI AC LOK MALPC FREEPC REALLOCPC SNC IMGW1 IMGW2 TABST ZST. unfold parse_headers_stmt. intros.
  eapply (ph_main AI AC); eauto.
Qed.

