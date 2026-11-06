(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool Permutation.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Mmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState Nodes Decode Lps04.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim STree Malloc MallocCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KStep__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot2__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Cnt__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require FreeRange ProgFullQ.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ITree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Monad MSafe.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres2__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_List__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_TF2 MI_WGroup.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Ledger__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Bound LB_QM.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_WFree.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module KPin.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Nodes Decode Lps04.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim STree Malloc MallocCtrl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KStep__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require FreeRange ProgFullQ. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KStep__Spec.KStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_Contracts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.LB_Tables OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Sum OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Cnt__Spec.LB_Init OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.FreeRange OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.ProgFullQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CE : CEIL}.
Section Main.
Variables (segs : list Segment) (brk0 mbase sp : word) (lim tb : Z).   (* [comment removed for export] *)
Let resvZ := reservedZ segs ++ [(tb, 4096)].
(* [comment removed for export] *)
Variable mo : Model.
Hypothesis Hvm : m_vmmaps mo = mkVmMapsFull (segments_reserved segs) [] [] brk0 brk0 lim mbase sp.
(* [comment removed for export] *)
Hypothesis Hktop : alloc_ceiling = page_round_down_Z (alloc_top (m_vmmaps mo)).
Hypothesis Hminv : minv mo.
Hypothesis Hhalt : m_halted mo = None.
(* [comment removed for export] *)
Hypothesis Hbrk : valid_brk segs brk0.
(* [comment removed for export] *)
Hypothesis Htop_pos : 0 < reserved_top (segments_reserved segs).
Hypothesis Hceil : reserved_top (segments_reserved segs) + brk_aslr_max + 4 * PGSZ <= alloc_ceiling.
Hypothesis Hfloor : reserved_top (segments_reserved segs) + brk_aslr_max + 2 * PGSZ + BLIVE <= bottomup_floor.
Hypothesis Hlim : BLIVE + RMAX <= lim.
(* [comment removed for export] *)
Hypothesis Htb : 0 < tb /\ exists e, In e (segments_reserved segs)
                                    /\ bv_unsigned (fst e) <= tb /\ tb + 4096 <= bv_unsigned (fst e) + bv_unsigned (snd e).

#[using="brk0 mbase sp lim Hvm Hktop Hminv Hhalt Hbrk Htop_pos Hceil Hfloor Hlim Htb"] Theorem KL_main : KL (led_init resvZ) 0 mo.
Proof.
  destruct Hbrk as (Hlo & Hhi & Hal). destruct Htb as (A0 & te & Hte & Tlo & Thi). pose proof alloc_ceiling_lt as Hcl.
  constructor; try exact Hktop; rewrite ?Hvm, ?Hhalt; cbn -[Z.pow Z.mul Z.add Z_to_bv bv_unsigned].
  - exact Hminv.
  - reflexivity.
  - split; [intros e []| apply pwdisj_nil].
  - intros r Hr. subst resvZ. apply in_app_or in Hr as [Hr|[<-|[]]].
    + unfold reservedZ in Hr. apply in_map_iff in Hr as (e & <- & He). exists e.
      split; [unfold elo; cbn; lia|]. split; [unfold ehi; cbn; lia|]. left. exact He.
    + exists te. unfold elo, ehi. cbn [fst snd]. split; [lia|]. split; [lia|]. left. exact Hte.
  - intros e Hin. pose proof (reserved_top_ge' _ _ Hin). unfold ehi. lia.
  - unfold PGSZ in *. unfold page_size in Hal. lia.
  - intros b l [].
  - intros b l k [].
  - apply List.NoDup_nil.
  - intros b l H. discriminate.
  - split; reflexivity.
  - intros e [].
  - intros b l H. discriminate.
  - unfold PGSZ. lia.
  - unfold PGSZ in *. lia.
  - intros b l [[]|[k []]].
  - intros e [].
Qed.

(* [comment removed for export] *)
#[using="brk0 mbase sp lim Hvm Hktop Hminv Hhalt Hbrk Htop_pos Hceil Hfloor Hlim Htb"] Theorem FQ_main {St : Type} {AS : AllocSt St} (P : Z -> Z) (G : St -> Model -> Prop) (s : St) (secret : Z) :
  0 <= secret < 2^64 ->     (* [comment removed for export] *)
  ps_m s = minit secret resvZ -> ps_brk s = 0 -> (forall c, 0 <= P c <= PMAX) -> G s mo ->
  FQ [] P G s mo.
Proof.
  intros Hsec Hm Hb HP HG. split; [| exact HG].
  exists (led_init resvZ), (fun _ => []), []. rewrite Hm, Hb.
  split; [apply INVL_init; exact Hsec|]. split; [apply SINV_minit|]. split; [apply AQ_minit; exact HP|].
  split; [exact KL_main|]. split; [| apply Permutation_refl].
  unfold LI, gm, BB, PINB, PGSZ, vm_live_bytes. rewrite Hvm. cbn. lia.
Qed.
End Main.

End WithCeil.
End KPin.

(* [comment removed for export] *)
Module MI_Calloc.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad MSafe STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KStep__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require ProgFullQ. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MSafe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KLink OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KStep__Spec.KStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Geom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_WMalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_WFree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.MI_Stable OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.LB_Tables OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Sum OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_StmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KStep__Spec.LB_Embed OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.ProgFullQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.

Local Open Scope Z_scope.
Local Open Scope stree_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Section WithCeil.
Context {CE : CEIL}.
#[using="Type"] Lemma fqtree_of_parts {R} B (t : M R) : forall L Post, ftree L t Post -> fbnd8 B L t -> fqtree B L t Post.
Proof.
  induction t as [r|e k IH]; intros L Post FT BD; cbn [fqtree ftree fbnd8] in *; [exact FT|].
  destruct e; try (destruct FT as [He Hk]; destruct BD as [HB Hb]; split; [exact He|]; split; [exact HB|];
                   intros a; specialize (Hk a); case_ans; [apply IH; [exact Hk| apply Hb; assumption]| exact Hk]).
  - intros v Hv. apply IH; [apply FT; exact Hv| apply BD; exact Hv].
  - destruct FT.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fbnd8_get_meta {R} B L st p (k : aptr -> Z -> Z -> M R) bail :
  (forall m off idx, fbnd8 B L (k m off idx)) -> fbnd8 B L bail -> fbnd8 B L (get_meta st p k bail).
Proof.
  intros Hk Hb.
  assert (G : forall tag c (t : M R), fbnd8 B L t -> fbnd8 B L (guard tag c t bail)) by (intros tag c t Ht; unfold guard; destruct c; [exact Ht| exact I]).
  assert (R32 : forall q (k' : Z -> M R), (forall v, fbnd8 B L (k' v)) -> fbnd8 B L (rd32 st q k')).
  { intros q k' H. unfold rd32. repeat (apply fbnd8_rd8; intros). apply H. }
  unfold get_meta. apply G. apply fbnd8_rd16. intros o16. cbv beta. apply fbnd8_rd8. intros b3. cbv beta. apply fbnd8_rd8. intros b4. cbv beta.
  destruct (negb (b4 =? 0)).
  - apply G. apply R32. intros o32. cbv beta. apply G.
    destruct (get_group st _) as [gh|]; [| exact I]. destruct (g_meta gh) as [m|]; [| exact I]. repeat apply G. apply Hk.
  - destruct (get_group st _) as [gh|]; [| exact I]. destruct (g_meta gh) as [m|]; [| exact I]. repeat apply G. apply Hk.
Qed.

#[using="Type"] Theorem calloc_ftq (MQ : malloc_core_fq_stmt) st L BL LS P m n B :
  INVL x0 st L BL LS -> SINV x0 st BL -> AQ st BL P -> 0 <= m -> 0 <= n -> ROOM BL P (m * n) ->
  PHI P + R63 BL + bigb (m * n) <= B + 3 * PGSZ -> bigb (m * n) <= QMAX ->
  ftree L (calloc st m n) (malloc_postQ st L BL P (m * n)) /\ fbnd8 B L (calloc st m n).
Proof.
  intros INV SI HAQ Hm Hn HR HB HQ. unfold calloc.
  destruct (negb (n =? 0) && (SIZE_MAX / n <? m)).
  { split; [| exact I]. apply ftree_ret. unfold malloc_postQ. cbn [fst snd]. split; [reflexivity|]. split; [apply GP_refl|].
    split; [exists LS; exact INV|]. split; [exact SI| exact HAQ]. }
  destruct (malloc_ftq MQ st L BL LS P (m * n) B INV SI HAQ ltac:(nia) HR HB HQ) as [FT BD].
  assert (K : forall L' (r : mstate * optr), malloc_postQ st L BL P (m * n) L' r ->
            ftree L' (let '(st1, p) := r in match p with None => ret (st1, None) | Some q => is_allzero st1 q (fun _ => ret (st1, Some q)) (ret (st1, Some q)) end)
                     (malloc_postQ st L BL P (m * n))
            /\ fbnd8 B L' (let '(st1, p) := r in match p with None => ret (st1, None) | Some q => is_allzero st1 q (fun _ => ret (st1, Some q)) (ret (st1, Some q)) end)).
  { intros L' [st1 [q|]] PQ; [| split; [exact PQ| exact I]].
    pose proof PQ as PQ0. unfold malloc_postQ in PQ. cbn [fst snd] in PQ. destruct PQ as (LIVE & GP1 & c & off & LS1 & Eq & Hoff & INV1 & Hni & SI1 & AQ1).
    destruct (block_facts x0 st1 L' (((c, off), m * n) :: BL) LS1 INV1 c off (m * n) ltac:(left; reflexivity)) as (mm & bm & i & ai & a & ar & ka & BF).
    unfold is_allzero. subst q. rewrite (get_meta_eq st1 c off (m * n) mm bm i ai a ar ka BF).
    split; [exact PQ0| exact I]. }
  split.
  - eapply ftree_bind; [exact FT|]. intros L' r PQ. exact (proj1 (K L' r PQ)).
  - eapply fbnd8_bind; [exact (fqtree_of_parts _ _ _ _ FT BD)|]. intros L' r PQ. exact (proj2 (K L' r PQ)).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma gp_conc_stable X st L BL LS (t : M (mstate * optr)) st' (res : optr) (L' : mled) Post :
  INVL X st L BL LS ->
  fpath L t L' (st', res) ->
  ftree L t Post -> (forall L1 r, Post L1 r -> GP st (fst r)) ->
  forall k d, In k BL -> conc st' (aadd (bslot k) d) = conc st (aadd (bslot k) d).
Proof.
  intros INV FP FT HGP k d Hk.
  pose proof (HGP _ _ (fpath_post _ _ _ _ _ FT FP)) as [G _]. cbn [fst] in G.
  destruct (blk_region _ INV Hk) as (r & Hr & K).
  rewrite !conc_aadd. unfold get_region. rewrite Hr, (G _ _ Hr K). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section RawCalloc.
Context {St : Type} {AS : OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.AllocSt St}.
Hypothesis MQ : malloc_core_fq_stmt.

#[using="MQ"] Theorem raw_callocF_Q_pt X P G m n s0 mo0 : frame_ok G -> 0 <= m -> 0 <= n -> bigb (m * n) <= QMAX ->
  FQ X P G s0 mo0 -> ROOMN (map snd X) P (m * n) ->
  mspec (fun s mo => s = s0 /\ mo = mo0) (raw_callocF peekG m n)
        (fun r s mo => match r with Some p => FQ ((p, m * n) :: X) P G s mo | None => FQ X P G s mo end
                       /\ (forall q sz, In (q, sz) X -> conc (ps_m s) q = conc (ps_m s0) q)
                       /\ ps_rest s = ps_rest s0 /\ vm_only mo0 mo).
Proof.
  intros HG Hm Hn HQ HF HR. unfold raw_callocF.
  eapply mspec_bind; [apply mspec_get|]. intros s1.
  apply mspec_pointwise. intros ? ? [-> [-> ->]].
  destruct HF as [(L & LS & BL & INV & SI & HAQ & HK & HL & HP) HGs].
  apply (ROOMN_eq X BL P (m * n) HP) in HR.
  destruct (calloc_ftq MQ (ps_m s0) L BL LS P m n (PHI P + R63 BL + bigb (m * n)) INV SI HAQ Hm Hn HR ltac:(unfold PGSZ; lia) HQ) as [FT _].
  eapply mspec_bind.
  { eapply mspec_pre; [apply (membedF_LI (calloc (ps_m s0) m n) _ (Gsince G s0 mo0) L s0 (Gsince_frame G s0 mo0 HG) FT)|].
    intros s mo [-> ->]. split; [reflexivity|]. split; [exact HK|]. split; [exact HL|]. split; [exact HGs|]. split; [reflexivity| apply vm_only_refl]. }
  intros [st' p]. cbn beta iota.
  apply mspec_pointwise. intros s2 mo2 (L' & Hp & HPost & HK' & HL' & (HG' & Hr' & Hvo') & Hm' & Hx).
  pose proof HPost as HPost0. unfold malloc_postQ in HPost. cbn [fst snd] in HPost. destruct HPost as (LIVE & GPx & RES).
  assert (STAB : forall q sz, In (q, sz) X -> conc st' q = conc (ps_m s0) q).
  { intros q sz Hin. assert (Hin' : In (q, sz) (map blk_ptr BL)) by (eapply Permutation_in; [exact HP| exact Hin]).
    apply in_map_iff in Hin' as ([[c0 off0] n0] & Ebp & Hk0). unfold blk_ptr in Ebp. cbn [bslot boff bsize fst snd] in Ebp.
    assert (Eq : q = aadd c0 (UNIT * off0)) by congruence. rewrite Eq.
    change c0 with (bslot (c0, off0, n0)). eapply (gp_conc_stable _ _ _ _ _ _ _ _ _ _ INV Hp FT); [| exact Hk0]. intros L1 r (_ & G1 & _). exact G1. }
  eapply mspec_seq with (R := fun s mo => s = set_m st' s2 /\ mo = mo2).
  { apply mspec_upd'. intros s mo [-> ->]. auto. }
  intros _. apply mspec_ret. intros s mo [-> ->]. unfold FQ. autorewrite with alloc_lens.
  assert (HG2 : G (set_m st' s2) mo2). { apply (HG s2 _ mo2 _); [apply ps_rest_set_m| apply vm_only_refl| exact HG']. }
  split; [| split; [exact STAB| split; [exact Hr'| exact Hvo']]].
  destruct p as [p|].
  - destruct RES as (c & off & LS' & Hp' & Hoff & INV' & Hni & SI' & HAQ').
    split; [| exact HG2]. exists L', LS', (((c, off), m * n) :: BL). split; [exact INV'|]. split; [exact SI'|]. split; [exact HAQ'|]. split; [exact HK'|]. split; [exact HL'|].
    cbn [map]. unfold blk_ptr at 1. cbn [bslot boff bsize fst snd]. rewrite <- Hp'. apply perm_skip. exact HP.
  - destruct RES as ((LS' & INV') & SI' & HAQ'). split; [| exact HG2]. exists L', LS', BL. split; [exact INV'|]. split; [exact SI'|]. split; [exact HAQ'|]. split; [exact HK'|]. split; [exact HL'| exact HP].
Qed.

#[using="MQ"] Theorem raw_callocF_Q X P G m n : frame_ok G -> 0 <= m -> 0 <= n -> bigb (m * n) <= QMAX ->
  mspec (fun s mo => FQ X P G s mo /\ ROOMN (map snd X) P (m * n)) (raw_callocF peekG m n)
        (fun r s mo => match r with Some p => FQ ((p, m * n) :: X) P G s mo | None => FQ X P G s mo end).
Proof.
  intros HG Hm Hn HQ. apply mspec_pointwise. intros s0 mo0 [HF HR].
  eapply mspec_post; [apply (raw_callocF_Q_pt X P G m n s0 mo0 HG Hm Hn HQ HF HR)|]. intros a s mo [H _]. exact H.
Qed.
End RawCalloc.

End WithCeil.
End MI_Calloc.

(* [comment removed for export] *)
Module LB_WRealloc.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_List__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Pres2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_TF2 MI_WGroup MI_WSlot. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Ledger__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_XferF__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Quant. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Bound LB_QM. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_Cnt__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require LB_WFree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require ProgFullQ. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KArith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MI_Arith OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_List OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Geom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_List__Spec.MI_Ext2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_Pres2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_TF2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WGroup OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_WMalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_WFree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Pres2__Spec.MI_WFree2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.MI_Cnt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Ledger__Spec.MI_Ledger OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.MI_Stable OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.MI_Realloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.MI_Realloc2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.MI_Realloc3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.LB_Tables OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Cnt__Spec.LB_Sum OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Quant OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_Tree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Bound OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_QM OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Cnt__Spec.LB_Cnt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_XferF__Spec.LB_StmtA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Cnt__Spec.LB_WSlot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Cnt__Spec.LB_WMalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_WFree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.LB_Cnt__Spec.LB_Raw OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.ProgFullQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KPin__Spec.MI_Calloc.
(* [comment removed for export] *) Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.zify_cheap_cleanup ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.zify_split_ranges; OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaTuning.zify_spec_trivial.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope stree_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section WithCeil.
Context {CEc : CEIL}.   (* [comment removed for export] *)
Definition least_f (k : Z) : bool := forallb (fun c => negb (k + 1 <=? size_class c) || (stc_k k <=? c)) (zrange 0 48).
(* [comment removed for export] *)
Fixpoint lbw_zr_go (x : Z) (k : nat) : list Z := match k with O => [] | S k' => x :: lbw_zr_go (x + 1) k' end.
#[using="Type"] Lemma lbw_zr_go_seq lo k s : map (fun i => lo + Z.of_nat i) (seq s k) = lbw_zr_go (lo + Z.of_nat s) k.
Proof. revert s. induction k as [|k IH]; intros s; [reflexivity|]. cbn [seq map lbw_zr_go]. f_equal. rewrite IH. f_equal. lia. Qed.
#[using="Type"] Lemma lbw_zrange_go lo n : zrange lo n = lbw_zr_go lo (Z.to_nat n).
Proof. unfold zrange. rewrite lbw_zr_go_seq. f_equal. lia. Qed.
#[using="Type"] Lemma least_b_true : forallb least_f (zrange 0 8191) = true.
Proof.
  assert (E : forall l, forallb least_f l
            = forallb (fun k => let s := stc_k k in forallb (fun c => negb (k + 1 <=? size_class c) || (s <=? c)) (lbw_zr_go 0 48)) l).
  { induction l as [|k l IH]; [reflexivity|]. cbn [forallb]. rewrite IH. unfold least_f. rewrite lbw_zrange_go. reflexivity. }
  rewrite E, lbw_zrange_go. vm_cast_no_check (@eq_refl bool true).
Qed.

#[using="Type"] Lemma fit_class_le n c : 0 <= n -> 0 <= c < 48 -> n + IB <= UNIT * size_class c -> size_to_class n <= c.
Proof.
  intros Hn Hc Hfit. pose proof (size_class_bound c Hc) as SB.
  rewrite size_to_class_k. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
  set (k := (n + IB - 1) / 16).
  assert (Hk : 0 <= k < 8191). { subst k. unfold IB, UNIT in *. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  assert (Hk1 : k + 1 <= size_class c). { enough (k < size_class c) by lia. subst k. unfold IB, UNIT in *. apply Z.div_lt_upper_bound; lia. }
  pose proof (forallb_zrange least_f 0 8191 k least_b_true ltac:(lia) ltac:(lia)) as H. unfold least_f in H.
  pose proof (forallb_zrange _ 0 48 c H ltac:(lia) ltac:(lia)) as H2. cbn beta in H2.
  rewrite (proj2 (Z.leb_le _ _) Hk1) in H2. cbn [negb orb] in H2. apply Z.leb_le in H2. exact H2.
Qed.

(* [comment removed for export] *)
Definition over1_f (c : Z) : bool := (c <? 34) || (47 <=? c) || (round_up_pg (UNIT * size_class c + UNIT) - UNIT <=? UNIT * size_class (c + 1)).
#[using="Type"] Lemma over1_b_true : forallb over1_f (zrange 0 48) = true. Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma over1 c : 34 <= c <= 46 -> round_up_pg (UNIT * size_class c + UNIT) - UNIT <= UNIT * size_class (c + 1).
Proof.
  intros Hc. pose proof (forallb_zrange over1_f 0 48 c over1_b_true ltac:(lia) ltac:(lia)) as H. unfold over1_f in H.
  replace (c <? 34) with false in H by (symmetry; apply Z.ltb_ge; lia). replace (47 <=? c) with false in H by (symmetry; apply Z.leb_gt; lia).
  cbn [orb] in H. apply Z.leb_le in H. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma inplace_class_hi (mr : meta) (sc n' off : Z) :
  m_sizeclass mr = sc -> 0 <= sc < 48 -> 0 <= off -> 0 <= n' < MMAP_THRESHOLD ->
  UNIT * off + n' <= get_stride mr - IB ->
  (m_last_idx mr = 0 -> m_maplen mr <> 0 ->
     m_maplen mr * 4096 <= S_ sc + UNIT \/ (34 <= sc /\ m_maplen mr * 4096 <= round_up_pg (S_ sc + UNIT))) ->
  size_to_class n' <= sc + 1.
Proof.
  intros Hsc Hc Ho Hn Hfit ONE. unfold get_stride in Hfit. unfold S_ in ONE.
  destruct (Z.eqb_spec (m_last_idx mr) 0) as [L0|L0]; destruct (Z.eqb_spec (m_maplen mr) 0) as [M0|M0]; cbn [andb negb] in Hfit; rewrite ?Hsc in Hfit.
  - pose proof (fit_class_le n' sc ltac:(lia) Hc ltac:(unfold UNIT, IB in *; lia)). lia.
  - destruct (ONE L0 M0) as [A|[A B]].
    + pose proof (fit_class_le n' sc ltac:(lia) Hc ltac:(unfold UNIT, IB in *; lia)). lia.
    + destruct (Z_lt_le_dec sc 47) as [LT|GE].
      * pose proof (over1 sc ltac:(lia)) as OV. apply (fit_class_le n' (sc + 1) ltac:(lia) ltac:(lia)). unfold UNIT, IB in *. lia.
      * pose proof (size_to_class_ok n' ltac:(lia)) as [R _]. lia.
  - pose proof (fit_class_le n' sc ltac:(lia) Hc ltac:(unfold UNIT, IB in *; lia)). lia.
  - pose proof (fit_class_le n' sc ltac:(lia) Hc ltac:(unfold UNIT, IB in *; lia)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma SINVx_ctrl X st st1 BL ex : ctrl_eq st st1 -> SINVx X st BL ex -> SINVx X st1 BL ex.
Proof.
  intros CE S.
  assert (MR1 : forall x, MR st1 x = MR st x) by (intros; apply MR_ext; exact (ce_metas _ _ CE)).
  assert (NC : ncarved st1 = ncarved st) by (unfold ncarved; rewrite (ce_metas _ _ CE); reflexivity).
  assert (AP : apages st1 = apages st).
  { unfold apages, regions_l, frontier. rewrite (ce_regions _ _ CE), (ce_ctx _ _ CE). reflexivity. }
  assert (STD : forall x, stdg st1 x = stdg st x) by (intros x; unfold stdg, cls; rewrite !MR1; reflexivity).
  destruct S. constructor; rewrite ?(ce_slots _ _ CE), ?(ce_groups _ _ CE), ?(ce_metas _ _ CE), ?(ce_regions _ _ CE), ?(ce_ctx _ _ CE), ?NC, ?AP; auto.
  - intros k Hk. destruct (sx_cls k Hk) as (m0 & i0 & H0 & H1 & H2). exists m0, i0. rewrite !MR1. auto.
  - intros b m' ai Hg. rewrite !MR1. intros A0 A1 A2. exact (sx_one _ _ _ Hg A0 A1 A2).
  - intros b m' ai Hg. rewrite !MR1. intros A1 A2. exact (sx_map _ _ _ Hg A1 A2).
  - intros b m' ai Hg. rewrite STD, !MR1. intros SG. destruct (sx_std _ _ _ Hg SG) as (Q1 & Q2 & Q3). split; [exact Q1|]. split; [| exact Q3].
    intros Z0. destruct (Q2 Z0) as (p' & i' & Hs' & E'). exists p', i'. rewrite (MR1 p'). auto.
  - intros c' Hc'. replace (nsc st1 c') with (nsc st c'); [apply sx_small; exact Hc'|].
    unfold nsc, gmetas, groups_l, cls. rewrite (ce_groups _ _ CE). apply zsum_map_ext. intros mb _. rewrite STD, MR1. reflexivity.
  - intros b m' ai Hg. rewrite !MR1. intros C63 NE. exact (sx_63 _ _ _ Hg C63 NE).
  - intros b m' ai p' i' Hg. rewrite !MR1. intros Z0 Hs'. exact (sx_host _ _ _ _ _ Hg Z0 Hs').
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma SINVx_add X st BL ex c off n' m i :
  SINVx X st BL ex -> s_slots st !! c = Some (m, i) ->
  (m_sizeclass (MR st m) < 48 -> 0 <= n' < MMAP_THRESHOLD /\ m_sizeclass (MR st m) - 1 <= size_to_class n' <= m_sizeclass (MR st m) + 1) ->
  (m_sizeclass (MR st m) = 63 -> MMAP_THRESHOLD <= n' /\ round_up_pg (n' + IB + UNIT) <= m_maplen (MR st m) * 4096 <= round_up_pg (n' + IB + UNIT) + PGSZ) ->
  (forall x, ex = Some x -> x = m /\ c = slot_start' (MR st m) 0) ->
  SINV X st (((c, off), n') :: BL).
Proof.
  intros S Hs C48 C63 HEX. destruct S. constructor; auto.
  - intros k [<-|Hk]; [| exact (sx_cls k Hk)]. exists m, i. cbn [bslot bsize fst snd]. split; [exact Hs|].
    split; [intros H; destruct (C48 H) as [[A B] C]; auto| exact C63].
  - intros b x ai Hb H63. cbn [map bslot fst]. destruct ex as [x0|] eqn:EX.
    + destruct (aptr_eq_dec x0 x) as [->|NE].
      * destruct (HEX x eq_refl) as [-> Ec]. left. first [exact Ec| symmetry; exact Ec].
      * right. apply (sx_63 b x ai Hb H63). congruence.
    + right. apply (sx_63 b x ai Hb H63). discriminate.
Qed.

#[using="Type"] Lemma n63_remove_big BL c off n : List.NoDup (map bslot BL) -> In ((c, off), n) BL -> MMAP_THRESHOLD <= n ->
  n63 (bl_remove c BL) + 1 = n63 BL.
Proof.
  intros ND Hk GB. unfold n63. induction BL as [|k l IH]; [destruct Hk|]. cbn [bl_remove map] in ND |- *.
  inversion ND as [|? ? NI ND']; subst. destruct Hk as [->|Hk].
  - cbn [bslot fst]. rewrite aptr_eqb_refl. rewrite (zcount_cons isbig). unfold isbig at 2. cbn [bsize snd]. rewrite (proj2 (Z.leb_le _ _) GB). lia.
  - destruct (aptr_eqb_spec (bslot k) c) as [E|NE].
    + exfalso. apply NI. rewrite E. change c with (bslot ((c, off), n)). apply in_map. exact Hk.
    + rewrite !zcount_cons. specialize (IH ND' Hk). lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma AQ_readd st BL P c off n n' :
  AQ st BL P -> List.NoDup (map bslot BL) -> In ((c, off), n) BL -> 0 <= n' -> ROOM BL P n' ->
  (MMAP_THRESHOLD <= n' -> MMAP_THRESHOLD <= n) ->
  forall off', AQ st (((c, off'), n') :: bl_remove c BL) P.
Proof.
  intros A ND Hk Hn' [R1 R2] BIG off'. pose proof (AQ_sub st BL P c A) as A'. destruct A' as [A1 A2 A3 A4 A5]. constructor; auto.
  - intros c' Hc'. unfold LR. rewrite zcount_cons. fold (LR (bl_remove c BL) c'). cbn [bsize snd]. unfold isbig. cbn [bsize snd].
    destruct (Z.leb_spec MMAP_THRESHOLD n') as [GE|LT]; cbn [negb andb]; [exact (A1 c' Hc')|].
    destruct (Z.eqb_spec (size_to_class n') c') as [<-|NE]; [| exact (A1 c' Hc')].
    specialize (R1 LT). pose proof (LR_sub BL (size_to_class n') c). lia.
  - unfold n63. rewrite zcount_cons. fold (n63 (bl_remove c BL)). unfold isbig. cbn [bsize snd].
    destruct (Z.leb_spec MMAP_THRESHOLD n') as [GE|LT]; [| exact A3].
    (* [comment removed for export] *)
    pose proof (BIG GE) as GB. destruct A as [B1 B2 B3 B4 B5]. pose proof (n63_remove_big BL c off n ND Hk GB). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma zlen_mtl_insert_some {A} (M : gmap aptr A) k v w : M !! k = Some w -> zlen (map_to_list (<[k := v]> M)) = zlen (map_to_list M).
Proof. intros H. unfold zlen. rewrite !length_map_to_list. rewrite (map_size_insert_Some _ _ _ _ H) || (rewrite map_size_insert, H). reflexivity. Qed.

Section RG63Q.
Variables (st : mstate) (L : mled) (BL1 : list blk) (LS : lhead -> list aptr).
Variables (m : aptr) (rid : N) (ai : Z) (r : region) (nb needed : Z).
Let c : cptr := (rid, UNIT).
Let X1 : extras := mkX [] [] (Some c) None None.
Hypothesis INV1 : INVL X1 st L BL1 LS.
Hypothesis Hg : s_groups st !! (rid, 0) = Some (mkGhdr (Some m) ai).
Hypothesis H63 : m_sizeclass (MR st m) = 63.
Hypothesis Hr : s_regions st !! rid = Some r.
Hypothesis Hnb : 0 < nb /\ nb mod PGSZ = 0.
Hypothesis Hnd : PGSZ <= needed /\ needed mod PGSZ = 0 /\ needed < LEN_MAX /\ nb + needed <= alloc_ceiling.
Let st' := wr8 (rid, needed - IB) 0 (upd_meta m (fun rg => m_set_maplen (needed / 4096) rg) (upd_region rid (fun rg => mkRegion (r_kind rg) nb needed) st)).

#[using="CEc st L BL1 LS m rid ai nb needed c X1 INV1 Hg H63 Hr"] Lemma rg_KG : r_kind r = RKGroup. Proof. exact (proj1 (r_group st L BL1 LS m rid ai r nb needed INV1 Hg H63 Hr)). Qed.

#[using="CEc L BL1 LS ai c X1 INV1 Hg"] Lemma rg_ncarved : ncarved st' = ncarved st.
Proof.
  unfold ncarved. unfold st'. rewrite (st'_metas st m rid nb needed).
  destruct (s_metas st !! m) as [w|] eqn:E; [exact (zlen_mtl_insert_some _ _ _ _ E)|].
  exfalso. exact (g_present _ _ _ _ _ _ (GO st L BL1 LS m rid ai INV1 Hg) E).
Qed.

#[using="CEc L BL1 LS ai r c X1 INV1 Hg H63 Hr"] Lemma rg_apages : apages st' = apages st.
Proof.
  unfold apages, regions_l. pose proof rg_KG as KG.
  assert (FR : forall q rq, frontier st' q rq = frontier st q rq) by (intros; apply frontier_ext; unfold st'; rewrite (st'_ctx st m rid nb needed); reflexivity).
  erewrite (map_ext _ (fun kr : N * region => if is_metakind_b (snd kr) then frontier st (fst kr) (snd kr) / PGSZ - 1 else 0)) by (intros [q rq]; cbn; rewrite FR; reflexivity).
  unfold st'. rewrite (st'_regions st m rid r nb needed Hr).
  assert (PN : Permutation (map_to_list (<[rid := mkRegion (r_kind r) nb needed]> (s_regions st))) ((rid, mkRegion (r_kind r) nb needed) :: map_to_list (delete rid (s_regions st)))).
  { rewrite <- insert_delete_eq. apply map_to_list_insert. apply lookup_delete_eq. }
  pose proof (map_to_list_delete (s_regions st) rid r Hr) as PD.
  rewrite (zsum_map_perm _ _ _ PN), <- (zsum_map_perm _ _ _ PD).
  cbn [map]. rewrite !zsum_cons. cbn [snd fst]. unfold is_metakind_b at 1 3. cbn [r_kind]. rewrite KG. reflexivity.
Qed.

#[using="Type"] Lemma rg_S63 : S_ 63 = 0. Proof. reflexivity. Qed.
#[using="CEc L BL1 LS ai c X1 INV1 Hg H63 Hnb Hnd"] Lemma rg_stdg_m : stdg st' m = false.
Proof.
  unfold stdg, cls. unfold st'. rewrite (R'_sc st m rid nb needed), H63, (R'_stride_m st L BL1 LS m rid ai nb needed INV1 Hg H63 Hnb Hnd), rg_S63.
  destruct Hnd as (N1 & _). unfold PGSZ, UNIT in *. replace (needed - 16 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). apply andb_false_r.
Qed.
#[using="Type"] Lemma rg_stdg_other x : x <> m -> stdg st' x = stdg st x.
Proof. intros NE. unfold stdg, cls. unfold st'. rewrite (R'_other st m rid nb needed x NE). reflexivity. Qed.
#[using="CEc L BL1 LS rid ai nb needed c X1 INV1 Hg H63 Hnb"] Lemma rg_stdg_old : stdg st m = false.
Proof.
  unfold stdg, cls. rewrite H63, rg_S63. destruct (g_facts st L BL1 LS m rid ai nb needed INV1 Hg H63) as (L0 & ML & _).
  unfold get_stride. rewrite L0. cbn [Z.eqb andb]. replace (m_maplen (MR st m) =? 0) with false by (symmetry; apply Z.eqb_neq; exact ML). cbn [negb].
  pose proof (g_maplen _ _ _ _ _ _ (GO st L BL1 LS m rid ai INV1 Hg)). unfold UNIT. replace (m_maplen (MR st m) * 4096 - 16 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). apply andb_false_r.
Qed.

#[using="CEc L LS ai r c X1 INV1 Hg H63 Hr Hnb Hnd"] Theorem SINVx_regroup63 (X : extras) : SINVx X st BL1 (Some m) -> SINVx X st' BL1 (Some m).
Proof.
  intros S. pose proof rg_KG as KG. destruct Hnd as (N1 & N2 & N3 & N4).
  pose proof (fun x (NE : x <> m) => R'_other st m rid nb needed x NE) as RO. fold st' in RO.
  pose proof (R'_sc st m rid nb needed) as RS. fold st' in RS.
  pose proof (st'_slots st m rid nb needed) as SS. pose proof (st'_groups st m rid nb needed) as SGp. fold st' in SS, SGp.
  destruct S. constructor; rewrite ?SS, ?SGp, ?rg_ncarved, ?rg_apages; unfold st'; rewrite ?(st'_ctx st m rid nb needed); fold st'.
  - intros k Hk. destruct (sx_cls k Hk) as (x & i & Hs & C1 & C2). exists x, i. split; [exact Hs|].
    destruct (blocks_other st L BL1 LS m rid ai nb needed INV1 Hg H63 Hnb k x i Hk Hs) as [NE _]. rewrite (RO x NE). auto.
  - intros b x aix Hb Hl Hml Hc. destruct (aptr_eq_dec x m) as [->|NE]; [rewrite RS, H63 in Hc; lia|]. rewrite (RO x NE) in *. exact (sx_one _ _ _ Hb Hl Hml Hc).
  - intros b x aix Hb Hc Hml. destruct (aptr_eq_dec x m) as [->|NE]; [rewrite RS, H63 in Hc; lia|]. rewrite (RO x NE) in *. exact (sx_map _ _ _ Hb Hc Hml).
  - intros b x aix Hb SD. destruct (aptr_eq_dec x m) as [->|NE]; [rewrite rg_stdg_m in SD; discriminate|]. rewrite (rg_stdg_other x NE) in SD. rewrite (RO x NE).
    destruct (sx_std _ _ _ Hb SD) as (Q1 & Q2 & Q3). split; [exact Q1|]. split; [| exact Q3].
    intros Z0. destruct (Q2 Z0) as (p & i & Hs & Ep). exists p, i. split; [exact Hs|]. rewrite RS. exact Ep.
  - intros c0 Hc0. replace (nsc st' c0) with (nsc st c0); [exact (sx_small c0 Hc0)|].
    unfold nsc, gmetas, groups_l. rewrite SGp. apply zsum_map_ext. intros [x b] Hin. cbn [fst]. unfold cls. rewrite RS.
    destruct (aptr_eq_dec x m) as [->|NE]; [rewrite H63; replace (63 =? c0) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity|].
    rewrite (rg_stdg_other x NE), (RO x NE). reflexivity.
  - intros b x aix Hb Hc NE. assert (NEm : x <> m) by congruence. rewrite (RO x NEm). rewrite (RO x NEm) in Hc. exact (sx_63 _ _ _ Hb Hc NE).
  - intros b x aix p i Hb Z0 Hs. rewrite RS. destruct (aptr_eq_dec x m) as [->|NE].
    + unfold st' in Z0. rewrite (R'_maplen_m st m rid nb needed (conj N1 (conj N2 (conj N3 N4)))) in Z0. pose proof (needed_div nb needed Hnb (conj N1 (conj N2 (conj N3 N4)))) as [_ D]. lia.
    + rewrite (RO x NE) in Z0. exact (sx_host _ _ _ _ _ Hb Z0 Hs).
  - intros x mr Hx. unfold st' in Hx. rewrite (st'_metas st m rid nb needed) in Hx. destruct (aptr_eq_dec x m) as [->|NE].
    + rewrite lookup_insert_eq in Hx. injection Hx as <-. unfold m_set_maplen. cbn [m_mem]. rewrite (mem_m st L BL1 LS m rid ai INV1 Hg). discriminate.
    + rewrite lookup_insert_ne in Hx by congruence. exact (sx_leak x mr Hx).
  - exact sx_pages.
  - intros q rq Hq K. unfold st' in Hq. apply (st'_region_some st m rid r nb needed Hr) in Hq as [[-> ->]|[_ Hq]]; [cbn in K; rewrite KG in K; discriminate| exact (sx_brk q rq Hq K)].
  - intros q rq Hq K. unfold st' in Hq. apply (st'_region_some st m rid r nb needed Hr) in Hq as [[-> ->]|[_ Hq]]; [cbn in K; rewrite KG in K; discriminate| exact (sx_len q rq Hq K)].
  - intros q1 q2 r1 r2 H1 H2 K1 K2 NE. unfold st' in H1, H2.
    apply (st'_region_some st m rid r nb needed Hr) in H1 as [[-> ->]|[_ H1]]; [cbn in K1; rewrite KG in K1; discriminate|].
    apply (st'_region_some st m rid r nb needed Hr) in H2 as [[-> ->]|[_ H2]]; [cbn in K2; rewrite KG in K2; discriminate|]. exact (sx_dist q1 q2 r1 r2 H1 H2 K1 K2 NE).
  - exact sx_shift.
Qed.

#[using="CEc L BL1 LS ai c X1 INV1 Hg"] Theorem AQ_regroup63 P BL0 : AQ st BL0 P -> AQ st' BL0 P.
Proof.
  intros A. destruct A as [A1 A2 A3 A4 A5]. constructor; auto.
  - intros c0 Hc0. unfold st'. rewrite (gcnt' st m rid nb needed c0). exact (A2 c0 Hc0).
  - rewrite rg_ncarved. exact A4.
Qed.
End RG63Q.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma fqtree_aleaf {R} B (t : M R) (P : mled -> R -> Prop) (Q : R -> Prop) : forall L,
  fqtree B L t P -> aleaf Q t -> fqtree B L t (fun L' r => P L' r /\ Q r).
Proof.
  induction t as [r|e k IH]; intros L FT AL; cbn [fqtree aleaf] in *; [split; assumption|].
  destruct e; try (destruct FT as (He & HB & Hk); split; [exact He|]; split; [exact HB|]; intros a; specialize (Hk a);
    case_ans; [apply IH; [exact Hk| apply AL]| exact Hk]).
  - intros v Hv. apply IH; [apply FT; exact Hv| apply AL].
  - destruct FT.
Qed.

#[using="Type"] Lemma round_up_pg_add_le x d : 0 <= d <= PGSZ -> round_up_pg x <= round_up_pg (x + d) <= round_up_pg x + PGSZ.
Proof.
  intros Hd. pose proof (round_up_pg_spec x) as [[A1 A2] A3]. pose proof (round_up_pg_spec (x + d)) as [[B1 B2] B3].
  pose proof (Z_div_mod_eq_full (round_up_pg x) 4096) as E1. pose proof (Z_div_mod_eq_full (round_up_pg (x + d)) 4096) as E2.
  unfold PGSZ in *. nia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma lbytes_event_post_mremap L a ol nl z : (forall g, In g (ld_groups L) -> 0 <= snd g) -> 0 <= nl ->
  gm (event_post L (EMremap a ol nl) z) + BB (event_post L (EMremap a ol nl) z) <= gm L + BB L + mmap_len nl.
Proof.
  intros POS Hnl. assert (NN : 0 <= mmap_len nl) by (rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KArith.mmap_len_rup; pose proof (round_up_pg_ge nl); lia).
  cbn [event_post]. destruct (is_err z); [lia|]. rewrite BB_set_groups.
  assert (H : forall l, (forall g, In g l -> 0 <= snd g) ->
    fold_right Z.add 0 (map (fun g : Z * Z => mmap_len (snd g)) (g_remove a l)) <= fold_right Z.add 0 (map (fun g : Z * Z => mmap_len (snd g)) l)).
  { induction l as [|[b l0] l IH]; intros P0; cbn; [lia|]. pose proof (P0 (b, l0) (or_introl eq_refl)) as Hl0. cbn in Hl0.
    destruct (b =? a); cbn.
    - assert (0 <= mmap_len l0) by (unfold mmap_len, page_round_up_Z; rewrite page_size_eq; apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia| lia]).
      lia.
    - specialize (IH ltac:(intros g Hg; apply P0; right; exact Hg)). lia. }
  unfold gm. cbn [ld_groups ld_metas set_groups map fold_right]. specialize (H (ld_groups L) POS). cbn [snd]. lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma ctrl_eq_set_size p e n b st : ctrl_eq st (set_size p e n b st).
Proof.
  unfold set_size.
  set (st1 := if negb (snd e - snd p - n =? 0) then wr8 (aadd e (- (snd e - snd p - n))) 0 st else st).
  assert (C1 : ctrl_eq st st1) by (subst st1; destruct (negb _); [apply ctrl_eq_wr8| apply ctrl_eq_refl]).
  destruct (5 <=? snd e - snd p - n).
  - eapply ctrl_eq_trans; [| apply ctrl_eq_wr8]. eapply ctrl_eq_trans; [exact C1|]. eapply ctrl_eq_trans; [apply ctrl_eq_wr32| apply ctrl_eq_wr8].
  - eapply ctrl_eq_trans; [exact C1| apply ctrl_eq_wr8].
Qed.

#[using="Type"] Lemma ctrl_eq_resize63 st rid needed p n i : ctrl_eq st (resize63 st rid needed p n i).
Proof.
  rewrite resize63_havoc_last. eapply ctrl_eq_trans; [| apply ctrl_eq_havoc]. eapply ctrl_eq_trans; [apply ctrl_eq_wr8| apply ctrl_eq_set_size].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cstable (st : mstate) (BLr : list blk) (st' : mstate) : Prop :=
  forall k d, In k BLr -> conc st' (aadd (bslot k) d) = conc st (aadd (bslot k) d).

#[using="Type"] Lemma cstable_ctrl st st' BLr : ctrl_eq st st' -> cstable st BLr st'.
Proof. intros CE k d _. rewrite !conc_aadd. unfold get_region. rewrite (ce_regions _ _ CE). reflexivity. Qed.

#[using="Type"] Lemma cstable_trans st1 st2 st3 BLr : cstable st1 BLr st2 -> cstable st2 BLr st3 -> cstable st1 BLr st3.
Proof. intros A B k d Hk. rewrite (B k d Hk). apply A. exact Hk. Qed.

#[using="Type"] Lemma cstable_sub st st' BL BLr : cstable st BL st' -> (forall k, In k BLr -> In k BL) -> cstable st BLr st'.
Proof. intros A S k d Hk. apply A. apply S. exact Hk. Qed.

#[using="Type"] Lemma cstable_GP X st L BL LS st' : INVL X st L BL LS -> GP st st' -> cstable st BL st'.
Proof.
  intros INV [G _] k d Hk. destruct (blk_region _ INV Hk) as (r & Hr & K).
  rewrite !conc_aadd. unfold get_region. rewrite Hr, (G _ _ Hr K). reflexivity.
Qed.

#[using="Type"] Lemma cstable_rsub X st L BL LS st' BLr : INVL X st' L BL LS -> rsub st st' -> (forall k, In k BLr -> In k BL) -> cstable st BLr st'.
Proof.
  intros INV RS S k d Hk. destruct (blk_region _ INV (S k Hk)) as (r & Hr & K).
  rewrite !conc_aadd. unfold get_region. rewrite Hr, (RS _ _ Hr). reflexivity.
Qed.

#[using="Type"] Lemma In_bl_remove_w k c BL : In k (bl_remove c BL) -> In k BL.
Proof. exact (In_bl_remove k c BL). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition realloc_postQ (st : mstate) (BL : list blk) (P : Z -> Z) (c : cptr) (n' : Z) (L' : mled) (r : mstate * optr) : Prop :=
  match snd r with
  | None => ((exists LS', INVL x0 (fst r) L' BL LS') /\ SINV x0 (fst r) BL /\ AQ (fst r) BL P) /\ cstable st BL (fst r)
  | Some q => (exists c' off' LS', q = aadd c' (UNIT * off') /\ 0 <= off' <= 255
      /\ INVL x0 (fst r) L' (((c', off'), n') :: bl_remove c BL) LS' /\ (c' = c \/ ~ In c' (map bslot BL))
      /\ SINV x0 (fst r) (((c', off'), n') :: bl_remove c BL) /\ AQ (fst r) (((c', off'), n') :: bl_remove c BL) P)
      /\ cstable st (bl_remove c BL) (fst r)
  end.

#[using="Type"] Lemma realloc_postQ_ctrl st0 st BL P c n' L' r : ctrl_eq st0 st -> realloc_postQ st BL P c n' L' r -> realloc_postQ st0 BL P c n' L' r.
Proof.
  intros CE. unfold realloc_postQ. destruct (snd r); intros [A C]; split; [exact A| | exact A|];
    (eapply cstable_trans; [apply cstable_ctrl; exact CE| exact C]).
Qed.

Section REALLOCQ.
Hypothesis MQ : malloc_core_fq_stmt.
Variables (P : Z -> Z) (B : Z).

(* [comment removed for export] *)
#[using="MQ"] Lemma fallback_fq st L BL LS c off n n' :
  INVL x0 st L BL LS -> SINV x0 st BL -> AQ st BL P -> In ((c, off), n) BL -> 0 <= n' -> ROOM BL P n' ->
  PHI P + R63 BL + bigb n' <= B + 3 * PGSZ -> bigb n' <= QMAX ->
  fqtree B L ('(st2, q) <-- malloc st n' ;;
              match q with
              | None => ret (st2, None)
              | Some q => st3 <-- free st2 (Some (aadd c (UNIT * off))) ;; ret (st3, Some q)
              end)
        (realloc_postQ st BL P c n').
Proof.
  intros INV SI HAQ Hk Hn' HR HB HQ.
  destruct (malloc_ftq MQ st L BL LS P n' B INV SI HAQ Hn' HR HB HQ) as [FT FB].
  eapply fqtree_bind; [exact (fqtree_of_parts B _ L _ FT FB)|].
  intros L1 [st2 [q|]] (LIVE & GP1 & RES); cbn [fst snd] in RES, GP1.
  - destruct RES as (c' & off' & LS1 & Eq & Hoff & INV1 & Hni & SI1 & HAQ1).
    assert (NE : c' <> c) by (intros ->; apply Hni; change c with (bslot ((c, off), n)); apply in_map; exact Hk).
    assert (HB1 : PHI P + R63 (((c', off'), n') :: BL) <= B + 3 * PGSZ) by (rewrite R63_cons; lia).
    eapply fqtree_bind.
    { apply fqtree_aleaf; [exact (free_fq st2 L1 (((c', off'), n') :: BL) LS1 P c off n B INV1 SI1 HAQ1 ltac:(right; exact Hk) HB1)| apply free_regions]. }
    intros L2 st3 [[LS2 (INV2 & SI2 & HAQ2)] RS]. cbn beta in RS. apply fqtree_ret. unfold realloc_postQ. cbn [fst snd].
    rewrite (bl_remove_cons_ne c c' off' n' BL NE) in INV2, SI2, HAQ2. split.
    + exists c', off', LS2. repeat (split; [eauto; fail|]). auto 10.
    + eapply cstable_trans.
      * eapply cstable_sub; [exact (cstable_GP x0 st L BL LS st2 INV GP1)| intros k Hk0; exact (In_bl_remove _ _ _ Hk0)].
      * eapply (cstable_rsub x0 st2 L2 _ LS2 st3 _ INV2 RS). intros k Hk0. right. exact Hk0.
  - destruct RES as ((LS1 & INV1) & SI1 & HAQ1). apply fqtree_ret. unfold realloc_postQ. cbn [fst snd]. split; [| exact (cstable_GP x0 st L BL LS st2 INV GP1)].
    split; [exists LS1; exact INV1| split; assumption].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ledger_groups_nonneg X st L BL LS : INVL X st L BL LS -> forall g, In g (ld_groups L) -> 0 <= snd g.
Proof.
  intros INV g Hg. pose proof (proj1 INV) as IR. apply (Permutation_in _ (ir_groups _ _ _ IR)) in Hg. apply in_map_iff in Hg as ([rid r] & <- & Hin). cbn.
  apply filter_In in Hin as [Hin _]. apply mtl_in in Hin. pose proof (ir_shape _ _ _ IR _ _ Hin) as (_ & _ & L0 & _). lia.
Qed.

#[using="MQ"] Theorem realloc_fq st0 L BL LS c off n n' :
  INVL x0 st0 L BL LS -> SINV x0 st0 BL -> AQ st0 BL P -> In ((c, off), n) BL ->
  0 <= n' -> size_overflows n' = false -> n' + 3 * PGSZ < LEN_MAX -> ROOM BL P n' ->
  PHI P + R63 BL + bigb n' <= B + 3 * PGSZ -> bigb n' <= QMAX ->
  fqtree B L (realloc st0 (Some (aadd c (UNIT * off))) n') (realloc_postQ st0 BL P c n').
Proof.
  intros INV0 SI0 HAQ0 Hk Hn' Hov Hnx HR HB HQ.
  set (st := set_tick (N.succ (s_tick st0)) st0).
  assert (CE0 : ctrl_eq st0 st) by apply ctrl_eq_set_tick.
  assert (INV : INVL x0 st L BL LS) by (apply INVL_set_tick; [cbn; lia| exact INV0]).
  assert (TF : TF0 st) by (apply TF0_tick_new; [exact (TKS_of _ _ _ _ _ INV0)| cbn; lia]).
  assert (SI : SINV x0 st BL) by (apply (SINV_ctrl x0 st0 st); [exact CE0| exact SI0]).
  assert (HAQ : AQ st BL P) by (apply (AQ_ctrl st0 st); [exact CE0| exact HAQ0]).
  pose proof (INVL_nodup_slots _ _ _ _ _ INV) as ND.
  apply (fqtree_mono B _ _ (fun L' r => realloc_postQ_ctrl st0 st BL P c n' L' r CE0)).
  destruct (block_facts x0 st L BL LS INV c off n Hk) as (m & bm & i & ai & a & ar & ka & BF).
  rewrite (realloc_eq st0 c off n m bm i ai a ar ka n' BF Hov). fold st.
  pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [S16 _]. pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF) as Ho.
  pose proof (bf_slot _ _ _ _ _ _ _ _ _ _ _ BF) as Hs. pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as Hg.
  pose proof (ip_ea_snd st c off m bm i (gbase_bm st c off n m bm i ai a ar ka BF) (bf_c _ _ _ _ _ _ _ _ _ _ _ BF) n') as EAS. cbn zeta in EAS.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  (* [comment removed for export] *)
  destruct (qb_cls _ _ _ SI ((c, off), n) Hk) as (m_ & i_ & Hs_ & Q48 & Q63). cbn [bslot bsize fst snd] in Hs_, Q48, Q63.
  rewrite Hs in Hs_. assert (m_ = m /\ i_ = i) as [-> ->] by (split; congruence). clear Hs_.
  unfold realloc_body.
  match goal with |- fqtree _ _ (if ?cnd then _ else _) _ => destruct cnd eqn:EC end.
  - (* [comment removed for export] *)
    apply andb_prop in EC as [EC E3]. apply andb_prop in EC as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. apply Z.leb_le in E3.
    rewrite EAS in E1. cbn [aadd snd] in E1.
    assert (Hsc : 0 <= m_sizeclass (MR st m) < 48).
    { pose proof (size_to_class_ok n' ltac:(lia)) as [ST _]. destruct (bf_sc _ _ _ _ _ _ _ _ _ _ _ BF) as [(H48 & _)|H63]; lia. }
    pose proof (stride_small x0 st L BL LS c off n m bm i ai a ar ka INV BF ltac:(lia)) as SS.
    set (stX := havoc _ n' (set_size _ _ n' i st)).
    assert (CEX : ctrl_eq st stX) by (eapply ctrl_eq_trans; [apply ctrl_eq_set_size| apply ctrl_eq_havoc]).
    assert (MRX : forall x, MR stX x = MR st x) by (intros x; apply MR_ext; exact (ce_metas _ _ CEX)).
    apply fqtree_ret. unfold realloc_postQ. cbn [fst snd]. split; [| apply cstable_ctrl; exact CEX].
    exists c, off, LS. split; [reflexivity|]. split; [exact Ho|]. split; [| split; [left; reflexivity|]].
    { apply (inplace_INVL x0 st L BL LS c off n m bm i ai a ar ka INV eq_refl Hk BF TF n' Hn'); unfold IB, UNIT in *; lia. }
    split.
    + apply (SINVx_add x0 stX (bl_remove c BL) None c off n' m i).
      * apply (SINVx_prefix x0 x0 st stX L BL LS c m i None INV CEX eq_refl Hs); [intros H63; lia| exact SI].
      * rewrite (ce_slots _ _ CEX). exact Hs.
      * rewrite MRX. intros _. split; [lia|]. split; [lia|].
        apply (inplace_class_hi (MR st m) (m_sizeclass (MR st m)) n' off eq_refl Hsc ltac:(lia) ltac:(lia)).
        -- unfold UNIT, IB in *. lia.
        -- intros L0 ML. exact (qg_one _ _ _ SI bm m ai Hg L0 ML ltac:(lia)).
      * rewrite MRX. intros H63. lia.
      * intros x Hx. discriminate.
    + apply (AQ_readd stX BL P c off n n' (AQ_ctrl st stX BL P CEX HAQ) ND Hk Hn' HR ltac:(intros; lia) off).
  - match goal with |- fqtree _ _ (if ?cnd then _ else _) _ => destruct cnd eqn:EB end.
    + (* [comment removed for export] *)
      apply andb_prop in EB as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2.
      assert (H63 : m_sizeclass (MR st m) = 63) by (destruct (bf_sc _ _ _ _ _ _ _ _ _ _ _ BF) as [(H48 & _)|H]; [lia| exact H]).
      apply fqtree_guard; [apply Z.eqb_eq; exact H63|].
      rewrite (start_eq st c off n m bm i ai a ar ka BF). cbn [aadd fst snd].
      replace (snd c + UNIT * off - snd c) with (UNIT * off) by lia.
      destruct (b_facts st L BL LS c off n m bm i ai a ar ka INV BF H63 n') as (L0 & ML & NL & I0).
      destruct (b_region st L BL LS c off n m bm i ai a ar ka INV BF H63 n') as (r & Hr & KG & OL).
      pose proof (needed_facts st c off n m bm i ai a ar ka BF n' B2 Hov Hnx) as (NF & NM & NP & NX). cbv zeta in NF, NM, NP, NX.
      set (needed := round_up_pg (n' + UNIT * off + UNIT + IB)) in *.
      set (oldlen := m_maplen (MR st m) * 4096) in *.
      assert (Ebase : conc st (fst c, 0) = r_base r) by (rewrite (conc_eq st (fst c, 0) r Hr); cbn; lia).
      rewrite Ebase.
      pose proof (ir_shape _ _ _ IR _ _ Hr) as (RS1 & RS2 & RS3 & RS4 & RS5 & _).
      destruct (Q63 H63) as [GBn _].
      (* [comment removed for export] *)
      assert (Hc0 : c = slot_start' (MR st m) 0).
      { destruct (is_valid _ _ _ IS _ _ _ Hs) as (_ & _ & E). rewrite I0 in E. exact E. }
      (* [comment removed for export] *)
      assert (NB : round_up_pg (n' + IB + UNIT) <= needed <= round_up_pg (n' + IB + UNIT) + PGSZ).
      { subst needed. replace (n' + UNIT * off + UNIT + IB) with (n' + IB + UNIT + UNIT * off) by lia. apply round_up_pg_add_le. unfold UNIT, PGSZ in *. lia. }
      assert (BIGB : bigb n' = round_up_pg (n' + IB + UNIT) + PGSZ) by (unfold bigb; rewrite (proj2 (Z.leb_le _ _) B2); reflexivity).
      destruct (Z.eqb_spec oldlen needed) as [EQ|NEQ].
      * set (stX := resize63 st (fst c) needed _ n' i).
        assert (CEX : ctrl_eq st stX) by apply ctrl_eq_resize63.
        assert (MRX : forall x, MR stX x = MR st x) by (intros x; apply MR_ext; exact (ce_metas _ _ CEX)).
        apply fqtree_ret. unfold realloc_postQ. cbn [fst snd]. split; [| apply cstable_ctrl; exact CEX].
        exists c, off, LS. split; [reflexivity|]. split; [exact Ho|]. split; [| split; [left; reflexivity|]].
        { exact (resize63_INVL st L BL LS c off n m bm i ai a ar ka INV Hk BF H63 TF n' B2 Hov Hnx EQ). }
        split.
        -- apply (SINVx_add x0 stX (bl_remove c BL) (Some m) c off n' m i).
           ++ apply (SINVx_prefix x0 x0 st stX L BL LS c m i (Some m) INV CEX eq_refl Hs); [intros _; reflexivity| exact SI].
           ++ rewrite (ce_slots _ _ CEX). exact Hs.
           ++ rewrite MRX. intros H48. lia.
           ++ rewrite MRX. intros _. split; [exact B2|]. fold oldlen. rewrite EQ. exact NB.
           ++ intros x Hx. injection Hx as <-. split; [reflexivity|]. rewrite MRX. exact Hc0.
        -- apply (AQ_readd stX BL P c off n n' (AQ_ctrl st stX BL P CEX HAQ) ND Hk Hn' HR ltac:(intros _; exact GBn) off).
      * (* [comment removed for export] *)
        assert (LB0 : gm L + BB L + 3 * PGSZ <= PHI P + R63 BL).
        { pose proof (regions_bound x0 st L BL LS P INV SI HAQ eq_refl) as R1. pose proof (ledger_bound x0 st L BL LS INV) as R2.
          unfold ORPH in R1. cbn [x_orph x0] in R1. lia. }
        apply fqtree_vis; [reflexivity| reflexivity| | | | | exact I].
        -- (* [comment removed for export] *)
           split; [exact (brk_quiet_of _ _ _ IR)|]. split; [exists (r_len r); split; [exact (group_region_in_ledger _ _ _ _ _ IR Hr KG)| symmetry; exact OL]|].
           split; [split; [unfold PGSZ in NP; lia| exact NX]|]. split; [exact NM| exact NEQ].
        -- (* [comment removed for export] *)
           intros z Hz. etransitivity; [apply (lbytes_event_post_mremap L (r_base r) oldlen needed z (ledger_groups_nonneg x0 st L BL LS INV)); lia|].
           rewrite (mmap_len_of_aligned needed) by (unfold PGSZ in *; lia). lia.
        -- intros z OKz. cbn [answer_ok] in OKz. rewrite (mremap_answer_ok_eq x0 st L IR (fst c) r Hr KG oldlen needed z) in OKz.
           rewrite OKz. cbn [negb event_post]. destruct (is_err z) eqn:ERR.
           ++ apply (fallback_fq st L BL LS c off n n' INV SI HAQ Hk Hn' HR HB HQ).
           ++ (* [comment removed for export] *)
              pose proof OKz as OK. unfold mremap_answer_ok in OK. rewrite (is_err_false_not_errno z ERR) in OK. cbn [orb] in OK.
              assert (PLACE : (0 < z /\ z mod PGSZ = 0 /\ z + needed <= alloc_ceiling)
                      /\ (forall rid' r', s_regions st !! rid' = Some r' -> rid' <> fst c -> let '(b', l') := region_live_range r' in z + needed <= b' \/ b' + l' <= z)).
              { split.
                ** apply Bool.orb_true_iff in OK. destruct OK as [OK1|OK1].
                   +++ apply andb_prop in OK1 as [Ez OK1]. apply Z.eqb_eq in Ez. subst z. split; [lia|]. split; [exact RS2|].
                       apply Bool.orb_true_iff in OK1. destruct OK1 as [LE|OK1]; [apply Z.leb_le in LE; rewrite OL in *; fold needed in LE |- *; lia|].
                       apply andb_prop in OK1 as [CE1 _]. apply Z.leb_le in CE1. exact CE1.
                   +++ apply andb_prop in OK1 as [OK1 RFz]. apply andb_prop in OK1 as [OK1 CE1]. apply andb_prop in OK1 as [OK1 AL]. apply andb_prop in OK1 as [NEz POS].
                       apply Z.ltb_lt in POS. apply Z.eqb_eq in AL. apply Z.leb_le in CE1. repeat split; assumption.
                ** intros rid' r' Hr' NE'. apply Bool.orb_true_iff in OK. destruct OK as [OK1|OK1].
                   +++ apply andb_prop in OK1 as [Ez OK1]. apply Z.eqb_eq in Ez. subst z.
                       pose proof (ir_disj _ _ _ IR (fst c) rid' r r' Hr Hr' ltac:(congruence)) as D. unfold region_live_range at 1 in D. rewrite KG in D. rewrite <- OL in D.
                       destruct (region_live_range r') as [b' l'] eqn:ER.
                       apply Bool.orb_true_iff in OK1. destruct OK1 as [LE|OK1]; [apply Z.leb_le in LE; lia|].
                       apply andb_prop in OK1 as [_ RF]. pose proof (ranges_free_regions_wo st (fst c) _ _ rid' r' RF Hr' NE') as D2. rewrite ER in D2.
                       pose proof (region_live_range_pos x0 st L rid' r' IR Hr') as P2. rewrite ER in P2. lia.
                   +++ apply andb_prop in OK1 as [OK1 RFz]. pose proof (ranges_free_regions st _ _ rid' r' RFz Hr') as D2. destruct (region_live_range r') as [b' l']. exact D2. }
              destruct PLACE as [PL1 DISJ].
              (* [comment removed for export] *)
              set (st' := wr8 (fst c, needed - IB) 0 (upd_meta m (fun rg => m_set_maplen (needed / 4096) rg) (upd_region (fst c) (fun rg => mkRegion (r_kind rg) z needed) st))).
              set (stX := big_resize st m (fst c) z needed _ n' i).
              assert (EX : stX = resize63 (upd_meta m (m_set_maplen (needed / 4096)) (upd_region (fst c) (fun rg => mkRegion (r_kind rg) z needed) st)) (fst c) needed (aadd c (UNIT * off)) n' i) by reflexivity.
              assert (CEX : ctrl_eq st' stX).
              { rewrite EX. eapply ctrl_eq_trans; [apply ctrl_eq_sym; apply (ctrl_eq_wr8 _ (fst c, needed - IB) 0)| apply ctrl_eq_resize63]. }
              assert (MRX : forall x, MR stX x = MR st' x) by (intros x; apply MR_ext; exact (ce_metas _ _ CEX)).
              pose proof (b_c st L BL LS c off n m bm i ai a ar ka INV BF H63 n') as Ec. cbv zeta in Ec.
              pose proof (b_bm st L BL LS c off n m bm i ai a ar ka INV BF H63 n') as Ebm. cbv zeta in Ebm.
              assert (HNB : 0 < z /\ z mod PGSZ = 0) by (split; [exact (proj1 PL1)| exact (proj1 (proj2 PL1))]).
              assert (HND : PGSZ <= needed /\ needed mod PGSZ = 0 /\ needed < LEN_MAX /\ z + needed <= alloc_ceiling) by (repeat split; try assumption; exact (proj2 (proj2 PL1))).
              (* [comment removed for export] *)
              assert (INV1 : INVL (mkX [] [] (Some c) None None) st L (bl_remove c BL) LS).
              { change c with (bslot ((c, off), n)) at 1 2.
                apply (INVL_remove_block x0 st st L BL LS ((c, off), n) INV Hk eq_refl (ctrl_eq_refl st) eq_refl).
                - intros; reflexivity.
                - exact (DOMS_of _ _ _ _ _ INV).
                - exact (TKS_of _ _ _ _ _ INV). }
              assert (INV1c : INVL (mkX [] [] (Some (fst c, UNIT)) None None) st L (bl_remove c BL) LS) by (rewrite <- Ec; exact INV1).
              assert (Hg0 : s_groups st !! (fst c, 0) = Some (mkGhdr (Some m) ai)) by (rewrite <- Ebm; exact Hg).
              apply fqtree_ret. unfold realloc_postQ. cbn [fst snd]. split.
              ** exists c, off, LS. split; [reflexivity|]. split; [exact Ho|]. split; [| split; [left; reflexivity|]].
                 { exact (big_resize_INVL st L BL LS c off n m bm i ai a ar ka INV Hk BF H63 TF n' B2 Hov Hnx r Hr z PL1 DISJ). }
                 split.
                 --- apply (SINV_X (mkX [] [] (Some (fst c, UNIT)) None None) x0 _ _ eq_refl).
                     apply (SINVx_add _ stX (bl_remove c BL) (Some m) c off n' m i).
                     +++ apply (SINVx_ctrl _ st' stX _ _ CEX).
                         apply (SINVx_regroup63 st L (bl_remove c BL) LS m (fst c) ai r z needed INV1c Hg0 H63 Hr HNB HND).
                         apply (SINVx_prefix x0 (mkX [] [] (Some (fst c, UNIT)) None None) st st L BL LS c m i (Some m) INV (ctrl_eq_refl st) eq_refl Hs); [intros _; reflexivity| exact SI].
                     +++ rewrite (ce_slots _ _ CEX). unfold st'. rewrite (st'_slots st m (fst c) z needed). exact Hs.
                     +++ rewrite MRX. unfold st'. rewrite (R'_sc st m (fst c) z needed), H63. intros; lia.
                     +++ rewrite MRX. intros _. split; [exact B2|]. unfold st'. rewrite (R'_maplen_m st m (fst c) z needed HND).
                         rewrite (proj1 (needed_div z needed HNB HND)). exact NB.
                     +++ intros x Hx. injection Hx as <-. split; [reflexivity|]. rewrite MRX. unfold st'.
                         rewrite (R'_slot_start'_m0 st L (bl_remove c BL) LS m (fst c) ai z needed INV1c Hg0). exact Hc0.
                 --- apply (AQ_readd stX BL P c off n n'); [| exact ND| exact Hk| exact Hn'| exact HR| intros _; exact GBn].
                     apply (AQ_ctrl st' stX BL P CEX). apply (AQ_regroup63 st L (bl_remove c BL) LS m (fst c) ai z needed INV1c Hg0 P BL HAQ).
              ** (* [comment removed for export] *)
                 intros k d Hk1. rewrite !conc_aadd. unfold get_region. rewrite (ce_regions _ _ CEX). unfold st'.
                 pose proof (is_blocks _ _ _ (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV1c)))))) k Hk1) as (x & ix & Hsx & _).
                 destruct (blocks_other st L (bl_remove c BL) LS m (fst c) ai z needed INV1c Hg0 H63 HNB k x ix Hk1 Hsx) as [_ NEr].
                 rewrite (st'_region_other st m (fst c) r z needed Hr (fst (bslot k)) NEr). reflexivity.
        -- intros z OKz. cbn [answer_ok] in OKz. rewrite (mremap_answer_ok_eq x0 st L IR (fst c) r Hr KG oldlen needed z) in OKz.
           rewrite OKz. cbn [negb]. apply rejects_bad_answer.
    + apply (fallback_fq st L BL LS c off n n' INV SI HAQ Hk Hn' HR HB HQ).
Qed.

#[using="MQ"] Corollary realloc_ftq st0 L BL LS c off n n' :
  INVL x0 st0 L BL LS -> SINV x0 st0 BL -> AQ st0 BL P -> In ((c, off), n) BL ->
  0 <= n' -> size_overflows n' = false -> n' + 3 * PGSZ < LEN_MAX -> ROOM BL P n' ->
  PHI P + R63 BL + bigb n' <= B + 3 * PGSZ -> bigb n' <= QMAX ->
  ftree L (realloc st0 (Some (aadd c (UNIT * off))) n') (realloc_postQ st0 BL P c n')
  /\ fbnd8 B L (realloc st0 (Some (aadd c (UNIT * off))) n').
Proof.
  intros. pose proof (realloc_fq st0 L BL LS c off n n') as FQ. repeat (specialize (FQ ltac:(assumption))).
  split; [exact (fqtree_ftree _ _ _ _ FQ)| exact (fbnd8_of_fqtree _ _ _ _ FQ)].
Qed.

End REALLOCQ.


End WithCeil.
End LB_WRealloc.
