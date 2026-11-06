(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame ITree Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ NodesLZ.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout APrim ATacA ACells LJ LJU PEnv APrimSpec APrimSpec2 APrimLem AFrame APrimPop APrimPopR APrimPopLens APrimQ APrimFrame AFrameM
                        APrimDealloc APrimCover ASec ASecD AQuar AQuarM AHeap AFoot F_prim_refill F_prim_cdealloc F_poison F_quar_Ep F_quar_E F_quar_A AQuarR AQuarS AQuarP ATacFix
                        F_quar_M F_quar_DR F_quar_R F_quar_D F_sec_A F_sec_B F_quar_P AQuarT AQuarU F_gct F_depot F_depot_C F_quar_C F_prim_L0 F_hooks F_dealloc
                        F_ialloc F_unwind F_stacktrace F_free_icpt F_free_null F_alloc_env F_alloc_A F_alloc_B F_alloc_C AAllocInv AAllocCarve AAllocEnvF F_alloc_P F_alloc_M
                        F_malloc_icpt ALedger AHeap2 AHeapB AFreeF AFreeZ AFreeL8 AAllocF AMallocP AFsEnv AFteF.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Section ML8.
Context {HC : HasCeiling}.
Variables (AL : alayout) (E : penv).
Notation L := (al_thread AL).
Notation D := (al_depot AL).
Notation THR := (at_thr (al_thread AL)).
Hypothesis SWIN_LO : 65536 <= SWIN D.

Definition mp_tree (P : prim) (n : Z) : itree nodeL (exc unit) :=
  if p_cnt (get_cls P (class_of (a0_need n))) =? 0 then t_refill AL (class_of (a0_need n)) (get_cls P (class_of (a0_need n))) else t_none.

Definition mp_cpre (X : pstate) (H : word -> bool) (WB : list qbatch) (WC : list qchunk) (hrest : list (Z * Z)) (hs : list Z) (total : Z) (mW : mem) : Prop :=
  dr_inv AL E X H mW WB WC hrest /\ alloc_env mW /\ thread_env2 AL mW /\ hooks_env mW /\ RDEPOT D hs total mW.

Definition mp_cpost (q' lo : Z) (X : pstate) (H : word -> bool) (n : Z) (WB : list qbatch) (WC : list qchunk) (hrest : list (Z * Z)) (hs : list Z) (total : Z) (tr : list Z)
    (mW : mem) (_ : unit) (H' : word -> bool) (a0 : word) (m' : mem) : Prop :=
  exists W hs' total',
    let P := fst X in let c := class_of (a0_need n) in let P' := fst (cache_alloc P c) in let v := snd (cache_alloc P c) in
    let ch := al_chunk_p P n in let X' := (P', snd X) in
    a0 = wz (qc_hdr AL ch + 16)
    /\ H' = (if p_cnt (get_cls P c) =? 0 then H_gfa AL c (get_cls P c) (max_count c / 2) H else H)
    /\ munch W mW m' /\ wmono asegs mW m'
    /\ Forall (fun iv => atouch AL lo q' (fst X) (snd X) [] [] iv \/ chunk_iv AL c v iv \/ chunk_sh_iv AL c v iv \/ dstat iv \/ dreg AL iv) W
    /\ dr_inv AL E X' H' m' WB WC (prim_of ch ++ hrest)
    /\ qchunk_wf ch /\ held_kind X' ch /\ lchunk_rep AL m' ch
    /\ 1 <= c <= 30 /\ c = a0_cls (al_n n) /\ 0 <= v /\ 16 * v + class_size c <= p_au (get_cls P' c) /\ (16 * v) mod class_size c = 0
    /\ RDEPOT D hs' total' m'
    /\ ((dfind hs (depot_hash tr) <> 0 /\ hs' = hs /\ total' = total)
        \/ (dfind hs (depot_hash tr) = 0 /\ hs' = hs ++ [depot_hash tr] /\ total' = total + Z.of_nat (length tr) + 1)).

Hypothesis AO : alayout_ok AL.

#[using="AO"] Lemma mp_callee : forall (gp s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32) (q lo : Z) (ra : word) (ras : list Z)
    (X : pstate) (H : word -> bool) (n : Z) (WB : list qbatch) (WC : list qchunk) (hrest : list (Z * Z)) (hs : list Z) (total : Z),
  0x10007fff8000 <= lo -> alloc_ceiling <= lo -> lo <= q - 2128 - AMALLOC_STACK -> q <= 2^47 -> q mod 16 = 0 ->
  0 <= n <= A0_MAXREQ -> a0_need n <= 65536 ->
  refill_budget (class_of (a0_need n)) (get_cls (fst X) (class_of (a0_need n))) ->
  0 <= pr_calloc (fst X) -> 0 <= pr_cmapped (fst X) -> pr_cmapped (fst X) + K_REGION < 2^63 ->
  (length ras <= 28)%nat -> Forall (fun x => 0 <= x < 2^64) ras ->
  16 * (zlen hs + 2) <= 2^20 -> 8 * (total + Z.of_nat (length (malloc_tr ra ras)) + 1) <= SWIN D -> total + Z.of_nat (length (malloc_tr ra ras)) + 1 < 2^20 ->
  forall (ra' t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 : word) (mW : mem) (ws : list word),
    mclean H mW -> stk asegs mW lo (q - 2128) ->
    rw_cells asegs mW (q - 2128) [C8 (wz (q - 2128 + 16)); C8 (wz (Z.of_nat (length (malloc_tr ra ras))))] -> u64arr asegs mW (q - 2128 + 16) ws -> length ws = 30%nat ->
    firstn (length (malloc_tr ra ras)) ws = map wz (malloc_tr ra ras) ->
    mp_cpre X H WB WC hrest hs total mW ->
    implA H (mp_tree (fst X) n)
      (mcallee_post gp s6 s7 s8 s9 s10 s11 F_ fc q lo unit (mp_cpost (q - 2128) lo X H n WB WC hrest hs total (malloc_tr ra ras)) ra' s0 s1 s2 s3 s4 s5 mW)
      (MS (mkR ra' (wz (q - 2128)) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz n) (wz (q - 2128)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz F_malloc_icpt.asan_malloc_entry) fc None mW (seg_rom asegs)).
Proof.
  intros gp s6 s7 s8 s9 s10 s11 F_ fc q lo ra ras X H n WB WC hrest hs total LOH CLO LOQ QH Q16 NR NP RB CA0 CM0 CM1 LRAS RNG ROOM_N ROOM_F ROOM_T
         ra' t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 mW ws MC ST SOBJ BUF LWS TRW (INV & AE & TE2 & HKE & RD).
  eapply implA_mono.
  - eapply (asan_malloc_prim_spec AL E AO gp F_ fc (q - 2128) lo LOH CLO ltac:(clear - LOQ; lia) ltac:(clear - QH; lia) ltac:(clear - Q16; Z.div_mod_to_equations; lia)
              ra' t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 X H mW n WB WC hrest (q - 2128) (q - 2128 + 16) total hs ws (malloc_tr ra ras));
      [ exact MC | exact ST | exact INV | exact NR | exact NP | exact RB | exact CA0 | exact CM0 | exact CM1 | exact AE | exact TE2 | exact HKE | exact RD
      | exact SOBJ | clear; lia | clear - QH; lia | exact BUF | exact TRW | rewrite LWS; unfold malloc_tr; cbn [length]; clear - LRAS; lia
      | unfold malloc_tr; cbn [length]; clear - LRAS; lia
      | unfold malloc_tr; constructor; [clear; lia| constructor; [pose proof (bv_unsigned_in_range 64 ra) as RR; change (bv_modulus 64) with (2^64) in RR; exact RR| exact RNG]]
      | clear; lia | rewrite LWS; clear - QH; lia | exact ROOM_N | exact ROOM_F | exact ROOM_T ].
  - intros r H' ms' PO. unfold amalloc_post_p in PO. cbv zeta in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & W & hs' & total' & EMS & EH & MU & WM & FW & INV' & WFC & HK & LREP & ST' & C1 & C2 & V0 & V1 & V2 & RD' & DEP & ABOVE).
    unfold mcallee_post. exists u0, u1, u2, (wz (qc_hdr AL (al_chunk_p (fst X) n) + 16)), b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m', W.
    split; [exact EMS|]. split; [exact MU|]. split; [exact ABOVE|]. split; [exact ST'|].
    unfold mp_cpost. exists W, hs', total'. cbv zeta. repeat (split; [first [reflexivity | assumption]|]). exact DEP.
Qed.

#[using="Type"] Lemma malloc_traces_ok : forall r ras, In (PC0_MALLOC :: r :: ras) A0_TRACES ->
  (length ras <= 28)%nat /\ Forall (fun x => x <> PC0_MALLOC) ras /\ 4096 <= r /\ r <> PC0_MALLOC /\ Forall (fun x => 0 <= x < 2^64) ras.
Proof. intros r ras Hin. exact (traces_ok PC0_MALLOC r ras Hin). Qed.

#[using="SWIN_LO AO"] Lemma malloc_prim_walk : forall (gp s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32) (q lo : Z)
    (ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 : word) s LB (m : mem) n ras,
  RHEAP_B AL E s LB m -> mclean (bs_H s) m -> mem_inv asegs m ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 4096 -> q mod 16 = 0 -> q + 16 < at_top L ->
  fpchain m (at_top L) q (bv_unsigned s0) ras -> In (PC0_MALLOC :: bv_unsigned ra :: ras) A0_TRACES ->
  0 <= n <= A0_MAXREQ -> a0_need n <= 65536 ->
  implA (bs_H s) (mp_tree (bs_prim s) n)
    (micpt_post L gp s6 s7 s8 s9 s10 s11 F_ fc q lo ra unit
       (mp_cpost (q - 2128) lo (bs_X s) (bs_H s) n (bs_gl s) (flat_map qb_chunks (bs_gl s)) (heldB s) (bs_depot s) (bs_dtotal s) (malloc_tr ra ras))
       s0 s1 s2 s3 s4 s5 m)
    (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F_ (wz malloc_icpt_entry) fc None m (seg_rom asegs)).
Proof.
  intros gp s6 s7 s8 s9 s10 s11 F_ fc q lo ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 s LB m n ras HR MC MI ST CLO LOQ Q16 QTOP CH TRIN NR NP.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  assert (LOH : 0x10007fff8000 <= lo) by (clear - ACR CLO; lia).
  destruct (malloc_traces_ok _ _ TRIN) as (LRAS & NPC & RA4 & RANE & RNG).
  pose proof (rheap_stats AL E s LB m HR) as (CA0 & CM0 & CM1).
  assert (CR : 1 <= class_of (a0_need n) <= 31).
  { rewrite class_of_a0. assert (1 <= a0_need n) by (unfold a0_need; assert (8 <= (Z.max n 8 + 7) / 8 * 8) by (Z.div_mod_to_equations; lia);
      assert (0 <= Z.shiftl 16 (a0_rzlog n)) by (apply Z.shiftl_nonneg; lia); lia). pose proof (a0_class_of_range (a0_need n) ltac:(lia)). lia. }
  pose proof (rheap_refill_budget AL E s LB m HR _ CR) as RB.
  pose proof HR as (_ & _ & AOx & INVB & _ & _ & _ & _ & _ & _ & RD & DOK & _ & _ & _ & _ & _ & TE2 & HKE & TRE & AENV & _).
  pose proof (dr_inv_of_B AL E _ _ _ _ _ _ INVB MI) as INV. pose proof INV as (_ & _ & _ & _ & _ & TE & _).
  pose proof AO as (_ & _ & _ & TLO & DLO & SWB). pose proof TLO as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9).
  assert (QH : q <= 2^47) by (clear - QTOP T9; lia).
  assert (LTR : (length (malloc_tr ra ras) <= 30)%nat) by (unfold malloc_tr; cbn [length]; clear - LRAS; lia).
  destruct (depot_room AL _ _ _ (malloc_tr ra ras) DOK LTR SWIN_LO) as (RN & RF & RT).
  eapply (malloc_icpt_spec L TLO gp s6 s7 s8 s9 s10 s11 F_ fc q lo LOH CLO LOQ QTOP Q16 ra ras unit (mp_tree (bs_prim s) n) (bs_H s) n
            (mp_cpre (bs_X s) (bs_H s) (bs_gl s) (flat_map qb_chunks (bs_gl s)) (heldB s) (bs_depot s) (bs_dtotal s))
            (mp_cpost (q - 2128) lo (bs_X s) (bs_H s) n (bs_gl s) (flat_map qb_chunks (bs_gl s)) (heldB s) (bs_depot s) (bs_dtotal s) (malloc_tr ra ras)));
    [ | exact MC | exact ST | exact MI | exact TE | exact TRE | exact CH | exact LRAS | exact NPC | exact RA4 | exact RANE | ].
  - exact (mp_callee gp s6 s7 s8 s9 s10 s11 F_ fc q lo ra ras (bs_X s) (bs_H s) n _ _ _ _ _ LOH CLO ltac:(assert (AS : AMALLOC_STACK = 928) by (vm_compute; reflexivity); clear - LOQ AS; lia)
             QH Q16 NR NP RB CA0 CM0 CM1 LRAS RNG RN RF RT).
  -
    intros mW MUW WMW MIW TEW.
    assert (FZ : Forall (izone AL lo) [(lo, q); (THR + 3168, THR + 3169)]).
    { unfold izone. repeat (apply Forall_cons || apply Forall_nil); cbn [fst snd]; [left; clear; lia| right; right; reflexivity]. }
    layout_facts AO 5%nat LDN. destruct LDN as (N1d & N2d & _). layout_facts AO 6%nat LSS. destruct LSS as (S1d & S2d & _).
    layout_apart_fact AO 3%nat 5%nat A35. layout_apart_fact AO 3%nat 6%nat A36. layout_apart_fact AO 2%nat 3%nat A23.
    assert (DJT : forall A k, A + k <= lo -> (A + k <= THR + 3168 \/ THR + 3169 <= A) -> disjoint_from [(lo, q); (THR + 3168, THR + 3169)] A k)
      by (intros A k D1 D3; cbn [disjoint_from]; clear - D1 D3; lia).
    unfold mp_cpre.
    split; [exact (dr_inv_frame_i AL E (bs_X s) (bs_H s) m mW _ _ _ lo _ AO LOH CLO INV MUW WMW MIW TEW FZ)|].
    split; [ae_split AENV; unfold alloc_env; repeat match goal with |- _ /\ _ => split end; (eapply rw_cells_transport_m; [eassumption| exact MUW| cbn [cells_size csize Nat.add]; apply DJT; clear - LOH T3; lia])|].
    split; [eapply (thread_env2_frame_m AL _ m mW TE2 MUW); apply DJT; clear - LOH CLO T1 T2 T3 T4 T5 A23; lia|].
    split; [unfold hooks_env in *; eapply rw_cells_transport_m; [exact HKE| exact MUW| cbn [cells_size csize Nat.add]; apply DJT; clear - LOH T3; lia]|].
    eapply (RDEPOT_frame_m AL _ _ _ m mW DLO SWB RD MUW); apply DJT; clear - LOH CLO N1d N2d S1d S2d A35 A36 T3; lia.
Qed.

#[using="AO"] Lemma alloc_W_ia_dj : forall (lo q' : Z) (X : pstate) (m : mem) (PN : prim) (c v : Z) W A k,
  0x10007fff8000 <= lo -> alloc_ceiling <= lo -> RPRIM AL (fst X) m -> RSEC AL (snd X) m ->
  held1 PN (c, v) -> (forall c0, 1 <= c0 <= 31 -> pclass_wf c0 (get_cls PN c0)) ->
  Forall (fun iv => atouch AL lo q' (fst X) (snd X) [] [] iv \/ chunk_iv AL c v iv \/ chunk_sh_iv AL c v iv \/ dstat iv \/ dreg AL iv) W ->
  743232 <= A -> A + k <= 1327052 -> disjoint_from W A k.
Proof.
  intros lo q' X m PN c v W A k LOH CLO RP RS HN WFN FW HA HK.
  destruct (fresh_bounds AL AO PN c v HN WFN) as (B1 & B2 & B3 & B4 & _).
  layout_facts AO 5%nat LDN. destruct LDN as (N1d & N2d & _ & PL5 & _). layout_facts AO 6%nat LSS. destruct LSS as (S1d & S2d & _ & PL6 & _).
  apply dj_of_Forall. eapply Forall_impl; [| exact FW]. intros [a b] [AT|[CI|[CI|[DS|DR]]]]; cbn [fst snd].
  - pose proof (atouch_img_dj AL X m lo q' [(a, b)] [] [] A k AO LOH CLO RP RS ltac:(constructor) ltac:(intros d []) ltac:(constructor; [exact AT| constructor])
                  ltac:(clear - HA; lia) ltac:(clear - HK; lia)) as DD. cbn [disjoint_from] in DD. exact (proj1 DD).
  - unfold chunk_iv in CI. cbn [fst snd] in CI. left. clear - CI B1 HK. lia.
  - unfold chunk_sh_iv in CI. cbn [fst snd] in CI. left. clear - CI B3 HK. lia.
  - unfold dstat in DS. cbn [fst snd] in DS. left. clear - DS HK. lia.
  - unfold dreg in DR. cbn [fst snd] in DR. destruct DR as [DR|DR]; [clear - DR PL5 HA HK; lia| clear - DR PL6 HA HK; lia].
Qed.

#[using="Type"] Lemma rw_cells_CB0 : forall (m : mem) A k ub, rw_cells asegs m A [CB k ub] -> rw_cells asegs m A [CB 0 []].
Proof.
  intros m A k ub [[WF (B0 & B1 & _)] (W0 & W1 & _)]. cbn [cells_bytes cbytes cells_size csize app length Nat.add] in *.
  split; [split; [cbn; tauto| split; [exact B0| split; [cbn [cells_bytes cbytes app length Z.of_nat]; lia| intros i Hi; cbn in Hi; lia]]]|].
  cbn [cells_size csize Nat.add Z.of_nat]. split; [exact W0| split; [lia| intros i Hi; lia]].
Qed.

Section MCONV.
Variable FI : fs_if.
Variable AI : am_if FI.
Hypothesis FSBE : FSB FI = al_fsb AL.
Hypothesis STAT : forall lo' hi', am_static FI AI lo' hi' -> a0_static lo' hi'.

#[using="AO FSBE STAT"] Lemma malloc_prim_conv : forall (gp s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32) (q lo : Z) (ra s0 s1 s2 s3 s4 s5 : word)
    s LB (m : mem) n ras (st : fsstate FI) H' ms',
  RHEAP_B AL E s LB m -> mem_inv asegs m -> asan_env asegs m -> RFAKE FI st m ->
  alloc_ceiling <= lo -> lo <= q - 4096 -> In (malloc_tr ra ras) A0_TRACES ->
  0 <= n <= A0_MAXREQ -> a0_need n <= 65536 ->
  (lbcZ LB (class_of (a0_need n)) + 1) * a0_csz (class_of (a0_need n)) <= A0_CAP (class_of (a0_need n)) ->
  micpt_post L gp s6 s7 s8 s9 s10 s11 F_ fc q lo ra unit
     (mp_cpost (q - 2128) lo (bs_X s) (bs_H s) n (bs_gl s) (flat_map qb_chunks (bs_gl s)) (heldB s) (bs_depot s) (bs_dtotal s) (malloc_tr ra ras))
     s0 s1 s2 s3 s4 s5 m tt H' ms' ->
  exists s' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (A : Z) (junk : list byte),
    ms' = MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F_ (ret_pc ra) fc None m' (seg_rom asegs)
    /\ bs_ghost s' = (H', bs_pages s) /\ bs_nsec s' = bs_nsec s
    /\ mem_inv asegs m' /\ stk asegs m' lo q /\ asan_env asegs m' /\ RFAKE FI st m'
    /\ (forall LBk : list (block (am_K FI AI)),
          (forall b, In b LBk -> exists r, In r (bs_live s) /\ blk_addr b = lc_user AL (fst r) /\ blk_size b = snd r) -> apres FI AI LBk q m m')
    /\ RHEAP_B AL E s' ((A, A, n) :: LB) m'
    /\ rw_cells asegs m' A [CB (Z.to_nat n) junk] /\ rw_cells asegs m' (sh A) (shadow_cells (block_shadow n))
    /\ wmono asegs m m'.
Proof.
  intros gp s6 s7 s8 s9 s10 s11 F_ fc q lo ra s0 s1 s2 s3 s4 s5 s LB m n ras st H' ms' HR MI AE RF CLO LOQ TRIN NR NP CAP POST.
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  assert (LOH : 0x10007fff8000 <= lo) by (clear - ACR CLO; lia). assert (LQ : lo <= q) by (clear - LOQ; lia).
  destruct POST as (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & mW & m' & W0 & EMS & MUW & WMW & _ & _ & STK' & CP).
  destruct CP as (W & hs' & total' & CP). cbv zeta in CP.
  destruct CP as (EA0 & EH & MU2 & WM2 & FW2 & INV' & WFC & HKN & LREP & C1 & C2 & V0 & V1 & V2 & RD' & DEP).
  set (X := bs_X s) in *. set (c := class_of (a0_need n)) in *. set (P' := fst (cache_alloc (fst X) c)) in *. set (v := snd (cache_alloc (fst X) c)) in *.
  set (ch := al_chunk_p (fst X) n) in *.
  assert (EK : qc_kind ch = QPrim c v) by reflexivity.
  pose proof HR as (PLB & LOK & AOx & INVB & QLG & GC & (TQC & QLL) & MTX & (CST & AFM) & QWF & RD & DOK & WFL & REPL & HKL & PSEC & COV & TE2 & HKE & (TR1 & TR2 & TR3) & AENV & (inited & IA) & CCL & CCQ & SLK & BUD & FTE).
  pose proof (dr_inv_of_B AL E _ _ _ _ _ _ INVB MI) as INV. pose proof INV as (RP & _ & RS & _ & _ & _ & _ & _ & _ & _ & HOK & _).
  pose proof INV' as (RP' & _ & RS' & MI' & _ & _ & _ & _ & _ & _ & HOK' & _).
  destruct (clear_ctx AL (P', snd X) m' RP' RS') as (WFN & _ & _). cbn [fst] in WFN.

  set (hs0 := map bpair (bs_gl s) ++ flat_map prim_of (flat_map qb_chunks (bs_gl s)) ++ heldB s).
  assert (HON : held_ok P' ((c, v) :: hs0)).
  { eapply held_ok_perm'; [| exact HOK']. unfold hs0, prim_of at 2. rewrite EK. cbn [fst app]. apply Permutation_sym.
    rewrite !app_assoc. apply Permutation_middle. }
  pose proof HON as [_ FHN]. apply Forall_cons_iff in FHN as [HN1 _].

  set (FT := [(lo, q); (THR + 3168, THR + 3169)] ++ W).
  assert (MUT : munch FT m m') by (unfold FT; exact (munch_joinP _ _ m mW m' MUW MU2)).
  assert (FTC : Forall (mtouch AL lo q X c v) FT).
  { unfold FT. apply Forall_app. split.
    - repeat (apply Forall_cons || apply Forall_nil); [left; left; unfold sub_iv; cbn [fst snd]; clear; lia| do 6 right; reflexivity].
    - eapply Forall_impl; [| exact FW2]. intros iv [AT|[CI|[CI|[DS|DR]]]].
      + left. eapply (atouch_mono AL lo q (fst X) (snd X) _ _ lo (q - 2128) (fst X) (snd X) _ _); [lia| lia| intros; lia| apply incl_refl| apply incl_refl| apply incl_refl| exact AT].
      + right; left; exact CI.
      + right; right; left; exact CI.
      + right; right; right; left; exact DS.
      + right; right; right; right; left; exact DR. }
  assert (FTZ : Forall (czone AL lo q (snd X)) FT) by (eapply Forall_impl; [| exact FTC]; intros iv MT; exact (mtouch_czone AL AO lo q X m P' c v iv RP RS HN1 WFN MT)).
  destruct (clear_ctx AL X m RP RS) as (_ & SOK & _).
  pose proof (fun W1 A k => mtouch_img_dj AL AO lo q X m P' c v LOH CLO RP RS HN1 WFN W1 A k) as IMGD.
  pose proof (fun A k => mtouch_thr_dj AL AO lo q X m P' c v LOH CLO RP RS HN1 WFN FT A k FTC) as THRD.
  assert (HULL : forall ch', held_kind X ch' -> (forall cv, In cv (prim_of ch') -> In cv hs0) -> forall A k, qc_hull AL ch' A k -> disjoint_from FT A k).
  { intros ch' HK' INH A k HU. apply dj_of_Forall. eapply Forall_impl; [| exact FTC]. intros iv MT.
    pose proof (hull_mtouch_dj AL AO lo q X m P' c v hs0 ch' iv A k LOH CLO RP RS HK' HON WFN INH MT HU) as DD. destruct iv as [a b]. cbn [disjoint_from] in DD. exact (proj1 DD). }
  assert (INHL : forall ch', In ch' (live_chunks s) -> forall cv, In cv (prim_of ch') -> In cv hs0).
  { intros ch' Hc cv Hcv. unfold hs0, heldB. apply in_or_app. right. apply in_or_app. right. apply in_flat_map. exists ch'. split; assumption. }

  destruct (malloc_prim_budget AL E s LB m c ch n H' hs' total' HR ltac:(clear - C1; lia) EK CAP) as [PI1 BUD']. cbv zeta in PI1, BUD'.
  pose proof LREP as (_ & _ & (ub & UB) & _ & _ & SHU & _). cbv zeta in UB, SHU.
  assert (ENQ : qc_n ch = al_n n) by reflexivity.
  exists (mkASB H' (bs_pages s) P' (bs_sec s) (bs_quar s) hs' total' (bs_nsec s) ((ch, n) :: bs_live s) (bs_depot0 s)),
         t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', (qc_hdr AL ch + 16).
  exists (if n =? 0 then [] else ub).
  split; [rewrite EMS, EA0; reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact MI'|]. split; [exact STK'|].
  split; [exact (asan_env_frame_m asegs m m' _ AE MUT (czone_env_safe AL AO lo q (snd X) LOH SOK _ FTZ))|].
  split.
  { eapply (rfake_frame_m FI st m m' _ RF MUT). eapply Forall_impl; [| exact FTZ]. intros iv CZ. left. rewrite FSBE. exact (czone_fs_dj AL AO lo q (snd X) LOH CLO SOK iv CZ). }
  split.
  { intros LBk HB. apply (apres_of_czone AL FI AI FSBE STAT lo q X m m' _ (bs_live s) LBk AO LOH CLO RP RS MUT FTZ); [| exact HB|].
    - intros A k HA. exact (mtouch_above AL AO lo q X m P' c v LOH CLO RP RS HN1 WFN FT A k LQ FTC HA).
    - intros r Hr. assert (INC : In (fst r) (live_chunks s)) by (unfold live_chunks; apply in_map; exact Hr).
      split; [exact (proj1 (Forall_forall _ _) LOK r Hr)|]. split; [exact (proj1 (Forall_forall _ _) HKL _ INC)|].
      split; [exact (proj1 (Forall_forall _ _) WFL _ INC)|]. exact (HULL _ (proj1 (Forall_forall _ _) HKL _ INC) (INHL _ INC)). }
  split.
  {
    pose proof AO as (_ & _ & _ & TLOx & _). pose proof TLOx as (_ & _ & T3x & _).
    unfold RHEAP_B. cbv zeta. unfold bs_X, bs_gl, live_chunks, heldB. cbn [bs_H bs_prim bs_sec bs_quar bs_depot bs_dtotal bs_live bs_depot0 q_glob q_loc map flat_map fst].
    split; [apply perm_skip; exact PLB|].
    split; [constructor; [unfold lr_ok; cbn [fst snd]; rewrite ENQ; unfold al_n; destruct (Z.eqb_spec n 0) as [->|NE]; [right; split; reflexivity| left; reflexivity]| exact LOK]|].
    split; [exact AO|].
    split; [exact (proj1 (dr_invB_of AL E _ _ _ _ _ _ INV'))|].
    assert (HBP : forall b, In b (bs_gl s) -> held1 (fst X) (bpair b) /\ In (bpair b) hs0).
    { intros b Hb. destruct HOK as [_ FH]. split; [apply (proj1 (Forall_forall _ _) FH)|]; apply in_or_app; left; apply in_map; exact Hb. }
    assert (QLF : forall l, incl l (bs_gl s) -> qlist_rep AL m l 0 -> qlist_rep AL m' l 0).
    { intros l INC QL. apply (qlist_rep_hull AL FT m m' l 0 MUT QL). apply Forall_forall. intros b Hb. destruct (HBP b (INC b Hb)) as [HB1 HB2].
      split; [exact (HULL (mkQC (QPrim K_BCLASS (qb_v b)) 16 1) HB1 ltac:(intros cv [<-|[]]; exact HB2) _ _ ltac:(left; split; reflexivity))
             | exact (HULL (mkQC (QPrim K_BCLASS (qb_v b)) 16 1) HB1 ltac:(intros cv [<-|[]]; exact HB2) _ _ ltac:(right; left; split; reflexivity))]. }
    split; [apply QLF; [unfold bs_gl; intros b Hb; apply in_or_app; left; exact Hb| exact QLG]|].
    split; [eapply rw_cells_transport_m; [exact GC| exact MUT| apply IMGD; [exact FTC| cbn [cells_size csize Nat.add qcells]; clear; lia]]|].
    split.
    { split; [eapply rw_cells_transport_m; [exact TQC| exact MUT| apply THRD; cbn [cells_size csize Nat.add]; clear; lia]|].
      apply QLF; [unfold bs_gl; intros b Hb; apply in_or_app; right; exact Hb| exact QLL]. }
    split; [eapply rw_cells_transport_m; [exact MTX| exact MUT| apply IMGD; [exact FTC| cbn [cells_size csize Nat.add]; clear; lia]]|].
    split; [split; (eapply rw_cells_transport_m; [eassumption| exact MUT| apply IMGD; [exact FTC| cbn [cells_size csize Nat.add]; clear; lia]])|].
    split; [exact QWF|]. split; [exact RD'|].
    split. { apply (depot_ok_step _ _ _ (malloc_tr ra ras) hs' total' DOK TRIN); [| exact DEP]. destruct (malloc_traces_ok _ _ TRIN) as (LRAS & _). unfold malloc_tr. cbn [length]. lia. }
    split; [constructor; [exact WFC| exact WFL]|].
    split.
    { constructor; [exact LREP|]. apply Forall_forall. intros ch' Hch'. pose proof (proj1 (Forall_forall _ _) HKL ch' Hch') as HK'.
      exact (lchunk_rep_hull AL X _ m m' ch' AO RP RS HK' (proj1 (Forall_forall _ _) REPL ch' Hch') (proj1 (Forall_forall _ _) WFL ch' Hch') MUT (HULL ch' HK' (INHL ch' Hch'))). }
    split.
    { constructor; [exact HKN|]. apply Forall_forall. intros ch' Hch'. pose proof (proj1 (Forall_forall _ _) HKL ch' Hch') as HK'.
      unfold held_kind in *. destruct (qc_kind ch') as [c' v'|sc] eqn:EK'; [| exact HK'].
      destruct HON as [_ FHA]. apply (proj1 (Forall_forall _ _) FHA). right. apply (INHL ch' Hch'). unfold prim_of. rewrite EK'. left. reflexivity. }
    pose proof PI1 as (_ & _ & COV' & _ & _ & _ & PSEC').
    split; [exact PSEC'|]. split; [exact COV'|].
    split; [eapply (thread_env2_frame_m AL _ m m' TE2 MUT); apply THRD; clear; lia|].
    split; [unfold hooks_env in *; eapply rw_cells_transport_m; [exact HKE| exact MUT| apply IMGD; [exact FTC| cbn [cells_size csize Nat.add]; clear; lia]]|].
    split; [unfold trace_env; split; [| split]; (eapply rw_cells_transport_m; [eassumption| exact MUT| apply IMGD; [exact FTC| cbn [cells_size csize Nat.add]; clear; lia]])|].
    split; [ae_split AENV; unfold alloc_env; repeat match goal with |- _ /\ _ => split end; (eapply rw_cells_transport_m; [eassumption| exact MUT| apply IMGD; [exact FTC| cbn [cells_size csize Nat.add]; clear; lia]])|].
    split.
    { assert (TRC : forall A cs, rw_cells asegs m A cs -> 743232 <= A -> A + Z.of_nat (cells_size cs) <= 1327052 -> rw_cells asegs m' A cs).
      { intros A cs C0 H1 H2. eapply rw_cells_transport_m; [exact C0| exact MUT|]. unfold FT. apply disjoint_from_app. split.
        - cbn [disjoint_from]. clear - H1 H2 LOH T3x. lia.
        - exact (alloc_W_ia_dj lo (q - 2128) X m P' c v W A _ LOH CLO RP RS HN1 WFN FW2 H1 H2). }
      destruct IA as (FL & [j0 C0] & [j2 [C2x Z2]] & [j3 C3] & [j4 C4'] & [j1 C1']). exists inited. unfold ia_cells.
      split; [apply TRC; [exact FL| clear; lia| unfold ia_flag; destruct inited; cbn [cells_size csize Nat.add]; clear; lia]|].
      split; [exists j0; apply TRC; [exact C0| clear; lia| cbn [cells_size csize Nat.add]; clear; lia]|].
      split; [exists j2; split; [| exact Z2]; apply TRC; [exact C2x| clear; lia| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear; lia); clear; lia]|].
      split; [exists j3; apply TRC; [exact C3| clear; lia| cbn [cells_size csize Nat.add]; clear; lia]|].
      split; [exists j4; apply TRC; [exact C4'| clear; lia| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear; lia); clear; lia]|].
      exists j1; apply TRC; [exact C1'| clear; lia| cbn [cells_size csize Nat.add]; clear; lia]. }
    split; [constructor; [unfold ch_cls_ok; rewrite EK; split; [rewrite ENQ; exact C2| clear - C1; lia]| exact CCL]|].
    split; [exact CCQ|]. split; [constructor; [unfold sec_slack_ok; rewrite EK; exact I| exact SLK]|]. split; [exact BUD'|].
    exact (fs_tls_env_frame_m _ _ _ _ _ FT m m' FTE MUT (mtouch_fte AL AO lo q X m P' c v LOH CLO RP RS HN1 WFN FT FTC)). }
  split.
  { unfold al_n in ENQ. destruct (Z.eqb_spec n 0) as [->|NE]; [exact (rw_cells_CB0 m' _ _ ub UB)|]. rewrite ENQ in UB. exact UB. }
  split.
  { unfold al_n in ENQ. destruct (Z.eqb_spec n 0) as [->|NE]; [| rewrite ENQ in SHU; exact SHU].
    change (shadow_cells (block_shadow 0)) with (@nil cell). destruct SHU as [[_ (SB0 & SB1 & _)] (SW0 & SW1 & _)].
    unfold rw_cells, cells_at, bytes_at, wr_at. cbn [cells_wf cells_bytes cells_size length Z.of_nat].
    assert (SH64 : sh (qc_hdr AL ch + 16) <= 2^64) by (clear - SB0 SB1; lia).
    repeat split; try lia; intros i Hi; cbn in Hi; lia. }
  exact (wmono_trans asegs _ _ _ WMW WM2).
Qed.

End MCONV.

End ML8.
