(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import ExecF ITreeA StepF Shadow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg RtCells AProto ABase ABytes AQConst AKitQ AMalloc_iface ADepot_iface APoisonR_iface ARep ARepQ ARepQP ALayout AHeapP AKit AKit2 ASec F_amalloc_arep F_afree_arep. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aalloc1. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.F_aalloc1. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import F_adepot AFake_iface. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFake_arep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_arep.AFake_arep. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import F_apoison_remap AInstance AInstanceM AInstanceF AFreeAll.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import ADeallocate AEmbedBind F_arealloc_iseg F_arealloc_pre. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFreeNull. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeNull.AReallocFront. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AReallocRead.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AFrameD AHolesD. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ASF_kit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASF_kit.ASF_kit. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AEmbRep AExh ARefill_iface_x ARefillP_x. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AMallocPG_x. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMallocPG_x.AMallocPG_x. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AMalloc_x AInstanceD AInstanceX F_arealloc_null.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC2. Context {rc : runConstT} {ov : annOV} {gb : GcBit}.

Definition aia_on (m : amem) : Prop :=
  rw_cells asegs m AIA_FLAG [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Definition AQF (L : alayout) (st : astate) (X : aconc) (m : amem) : Prop := AQUAR L st X m /\ aia_on m.
Definition AHF : aholes := F_amalloc_arep.AH adepot_iface AQF ASEC_of AFAKE.

Lemma AHF_laws : ahole_laws AHF.
Proof.
  pose proof AH_laws as HL. constructor.
  - intros L st st' X X' m m' W [HQ FLG] MU WM UT QS. split.
    + exact (hq_frame _ HL L st st' X X' m m' W HQ MU WM UT QS).
    + unfold aia_on in *. eapply rw_cells_transport; [exact FLG| exact MU| exact WM|].
      apply ARepQP.disjoint_from_Forall. eapply Forall_impl; [| exact UT]. intros iv (_ & _ & _ & A & _).
      unfold AIA_FLAG. cbn [cells_size csize Nat.add]. cbn in A |- *. lia.
  - exact (hs_frame _ HL).
  - exact (hd_frame _ HL).
  - exact (hf_frame _ HL).
  - exact (hf_blocks _ HL).
Qed.

Lemma AHF_lawsD : ahole_lawsD AHF.
Proof.
  pose proof AH_lawsD as HLD. constructor.
  - intros L st st' X X' m m' W [HQ FLG] MU UT QS. split.
    + exact (hqD _ HLD L st st' X X' m m' W HQ MU UT QS).
    + unfold aia_on in *. eapply rw_cells_transportD; [exact FLG| exact MU|].
      apply ARepQP.disjoint_from_Forall. eapply Forall_impl; [| exact UT]. intros iv (_ & _ & _ & A & _).
      unfold AIA_FLAG. cbn [cells_size csize Nat.add]. cbn in A |- *. lia.
  - exact (hx_get _ HLD).
  - exact (hsD _ HLD).
  - exact (hdD _ HLD).
  - exact (hfD _ HLD).
Qed.

Lemma AHF_of_AHI : forall L RNG st LB m, AHEAP_P AHI L RNG st LB m -> aia_on m -> AHEAP_P AHF L RNG st LB m.
Proof.
  intros L RNG st LB m (ALO & ARNG & [X [AR BL]] & HFK) FLG.
  destruct AR as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  split; [exact ALO|]. split; [exact ARNG|]. split; [| exact HFK].
  exists X. split; [| exact BL].
  split; [exact WF|]. split; [exact RT|]. split; [exact INST|]. split; [exact THR|]. split; [exact CLS|].
  split; [exact (conj HQ FLG)|]. split; [exact HS|]. split; [exact HD|]. split; [exact HRO|]. split; [exact RT2|]. split; [exact AVL| exact RT3].
Qed.

Lemma AHI_of_AHF : forall L RNG st LB m, AHEAP_P AHF L RNG st LB m -> AHEAP_P AHI L RNG st LB m /\ aia_on m.
Proof.
  intros L RNG st LB m (ALO & ARNG & [X [AR BL]] & HFK).
  destruct AR as (WF & RT & INST & THR & CLS & [HQ FLG] & HS & HD & HRO & RT2 & AVL & RT3).
  split; [| exact FLG].
  split; [exact ALO|]. split; [exact ARNG|]. split; [| exact HFK].
  exists X. split; [| exact BL].
  split; [exact WF|]. split; [exact RT|]. split; [exact INST|]. split; [exact THR|]. split; [exact CLS|].
  split; [exact HQ|]. split; [exact HS|]. split; [exact HD|]. split; [exact HRO|]. split; [exact RT2|]. split; [exact AVL| exact RT3].
Qed.

Hypothesis EXHW : exh_first_stmt.
Theorem AHF_allocate_h : aallocate_stmt_h aci_I (AHEAP_P AHF).
Proof. exact (aallocate_all_h adepot_iface AQF AFAKE AHF_laws AHF_lawsD EXHW poison_remap_proof aci_I aci_ok aci_ok2 aci_ok3). Qed.

Definition AREALLOC_STACK : Z := 8192.

Definition arealloc (RESV : list (Z * Z)) (st : astate) (p : aptr) (n : Z) : AM (astate * option aptr) :=
  sbind (amalloc ATOP RESV st n) (fun r =>
    match snd r with
    | Some q => sbind (afree (fst r) (Some p)) (fun st2 => aret (st2, Some q))
    | None => aret r
    end).

Section Stmt.
Variable CI : list (Z * Z).
Variable AHEAP : alayout -> footprint -> astate -> list ablock -> amem -> Prop.

Definition arealloc_post (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (p : aptr) (A nold n lo : Z) (m : amem)
    (r : astate * option aptr) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI (lb_remove p LB) (bv_unsigned sp) m m'
    /\ match snd r with
       | None => False
       | Some q => exists UB (src junk : list byte),
           a0 = Z_to_bv 64 UB /\ ablock_range UB n
           /\ AHEAP L RNG' (fst r) (HB q UB n :: lb_remove p LB) m'

           /\ bytes_at asegs m A src /\ length src = Z.to_nat (Z.min n nold)
           /\ rw_cells asegs m' UB [CB (Z.to_nat (Z.min n nold)) src; CB (Z.to_nat (n - Z.min n nold)) junk]
           /\ rng RNG' UB n /\ rng RNG' (shad UB) (shlen (n + 7))
       end.

Definition arealloc_post_h (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (p : aptr) (A nold n lo : Z) (m : amem)
    (r : astate * option aptr) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' =>
    match snd r with
    | Some _ => arealloc_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p A nold n lo m r RNG' ms'
    | None => fp_le RNG RNG' /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None m' (seg_rom asegs)
        /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
        /\ aheap_pres_e CI LB (bv_unsigned sp) m m'
        /\ AHEAP L RNG' (fst r) LB m'
        /\ rw_cells asegs m' AERRNO [C4 (Z_to_bv 64 12)]
    end.
Definition arealloc_stmt_h : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (st : astate) (LB : list ablock) (p : aptr) (A nold n lo : Z) (tr : list Z) (RESV : list (Z * Z)),
  ann_ov (a_next st) = None ->
  AHEAP L RNG st LB m -> In (HB p A nold) LB ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AREALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> 1 <= n <= AREQMAX ->
  aunw m L RNG lo AREALLOC_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AREALLOC_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  aresv_ok L RESV ->

  bv_unsigned fc < 32 -> c6m RESV RNG st -> (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23) ->
  (exists e0 : word, rw_cells asegs m AERRNO [C4 e0]) ->
  implS asegs RNG (aembed ATOP (arealloc RESV st p n))
        (epostF (arealloc_post_h L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p A nold n lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AREALLOC_SYM) fc None m (seg_rom asegs)).
End Stmt.

Lemma aheap_pres_u64arr : forall CI LB SP m m' A ws,
  aheap_pres CI LB SP m m' -> u64arr asegs m A ws -> aclient_range CI LB SP A (8 * Z.of_nat (length ws)) -> u64arr asegs m' A ws.
Proof.
  intros CI LB SP m m' A ws HP [BA WR] CR. split.
  - eapply aheap_pres_bytes_at; [exact HP| exact BA|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact CR.
  - eapply aheap_pres_wr_at; [exact HP| exact WR| exact CR].
Qed.

Lemma cb_split2 : forall m A (n k : nat) bs, length bs = n -> (k <= n)%nat ->
  rw_cells asegs m A [CB n bs] ->
  rw_cells asegs m A [CB k (firstn k bs)] /\ rw_cells asegs m (A + Z.of_nat k) [CB (n - k) (skipn k bs)].
Proof.
  intros m A n k bs LN K H.
  pose proof (rw_cells_split_CB asegs m A [] _ _ [] [k; (n - k)%nat] H ltac:(cbn; lia)) as SP. cbn [app mk_CB_cells] in SP.
  rewrite (firstn_all2 (n := (n - k)%nat) (skipn k bs)) in SP by (rewrite length_skipn; lia).
  change [CB k (firstn k bs); CB (n - k) (skipn k bs)] with ([CB k (firstn k bs)] ++ [CB (n - k) (skipn k bs)]) in SP.
  apply rw_cells_app in SP. destruct SP as [H1 H2]. cbn [cells_size csize] in H2. rewrite Nat.add_0_r in H2. split; assumption.
Qed.

Lemma pres_head_write : forall L RNG st LB m m' (q : aptr) UB n k LBk SP,
  AHEAP_I L RNG st (HB q UB n :: LB) m -> munch [(UB, UB + k)]%Z m m' -> wmono asegs m m' -> 0 <= k <= n -> ablock_range UB n ->
  (forall b, In b LBk -> In b LB) -> ATOP <= SP ->
  aheap_pres aci_I LBk SP m m'.
Proof.
  intros L RNG st LB m m' q UB n k LBk SP AH MU WM K BR SUB HSP a Ha CLA.
  split; [| intros Hw; apply WM; exact Hw].
  apply MU. rewrite wa_unsigned by exact Ha. cbn [outside]. split; [| exact I].
  pose proof BR as (BK & _ & HI & _). pose proof atop_range as ATR.
  assert (NI : ~ In (HB q UB n) LB) by (pose proof (AHI_blocks_nodup L RNG st _ m AH) as ND; inversion ND; assumption).
  assert (BB : forall b, In b LB -> AIMG_HI <= ab_addr b /\ ab_addr b + ab_size b <= ATOP /\ (UB + n <= ab_addr b \/ ab_addr b + ab_size b <= UB)).
  { intros b Hb. pose proof (AHI_block_bounds L RNG st _ m b AH ltac:(right; exact Hb)) as (B1 & B2 & B3).
    assert (NE : HB q UB n <> b) by (intros E; apply NI; rewrite E; exact Hb).
    pose proof (AHI_blocks_disjoint L RNG st _ m (HB q UB n) b AH ltac:(left; reflexivity) ltac:(right; exact Hb) NE) as D. cbn [ab_addr ab_size] in D. lia. }
  destruct CLA as [SK | [CIa | [BLK | SH]]].
  - pose proof (ablk_lin _ _ BK) as (_ & _ & G3 & _). lia.
  - destruct CIa as (iv & Hiv & R). pose proof (aci_ok1 iv Hiv) as (Q1 & Q2). pose proof (ablk_lin _ _ BK) as (G1 & _). lia.
  - destruct BLK as (b & Hb & R). destruct (BB b (SUB b Hb)) as (_ & _ & D). lia.
  - destruct SH as (a' & Ha' & ->). rewrite shad_div in Ha |- *. unfold ASHOFF in *.
    assert (A47 : 0 <= a' < 2^47).
    { destruct Ha' as [SK | [CIa | FK]].
      - lia.
      - destruct CIa as (iv & Hiv & R). pose proof (aci_ok1 iv Hiv) as (Q1 & Q2). unfold AIMG_HI in *. lia.
      - destruct FK as (cls & FA & sz & Hin & R). destruct (BB _ (SUB _ Hin)) as (B1 & B2 & _). cbn [ab_addr ab_size] in B1, B2. unfold AIMG_HI in *. lia. }
    unfold ablk, AIMG_HI, KLS in BK. Z.div_mod_to_equations. lia.
Qed.

Lemma errno_client : forall LB SP, aclient_range aci_I LB SP AERRNO 4.
Proof.
  intros LB SP. left. right. left. exists (0x5fc110, 0x60cc28). split; [unfold aci_I, msg_img_ranges; cbn [In]; tauto|].
  unfold AERRNO, ATP. cbn [fst snd]. lia.
Qed.

Theorem AHI_realloc_h : arealloc_stmt_h aci_I AHEAP_I.
Proof.
  unfold arealloc_stmt_h. intros until RESV. intros OVF AH HIN MI ST BOT LO TP Ha0 Ha1 NR AUNW S0NE RA4 RANE SP16 RSTK RESVOK FCB C6M CAPB [e0 ERR0].
  pose proof (AHI_block L RNG st LB m p A nold AH HIN) as (NOLD & BRo & RNGo & RNGso & SHo & WRo & CHo & ARENAo).
  pose proof BRo as (BKo & _ & HIo & ALo). pose proof (ablk_lin _ _ BKo) as (GL1 & GL2 & GL3 & GL4).
  pose proof atop_range as ATR. unfold AIMG_HI in GL1.
  assert (SP47 : bv_unsigned sp < 2^47).
  { destruct AUNW as [(X1 & _)|(_ & X2 & _)]; [| exact X2]. pose proof (AHI_layout L RNG st LB m AH) as (_ & _ & TOP47 & _). lia. }
  word_range sp SPR. unfold AREALLOC_STACK in LO.
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -2208)) = bv_unsigned sp + -2208) by (apply unsigned_lit; lia).

  eapply implF_evtF.
  { eapply (arealloc_frontP adepot_iface ASEC_of AFAKE AH_laws aci_I aci_okQ L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB A n lo tr);
      try eassumption; unfold AFREE_STACK, AREALLOC_STACK, AREQMAX in *; lia. }
  cbv beta. intros ms3 (trc & sj & PRE & TRU & LTRC & PRES3 & AH3).
  unfold realloc_pre_post in PRE.
  destruct PRE as (t0c & t1c & t2c & a7c & t3c & t4c & t5c & t6c & m3 & sj' & tb & junk0 & junk2 & junkR & -> & MU3 & WM3 & MI3 & ST3 & FRR & FRa & FRp0 & SS & TB & LTB & TRF & FRS
                   & UNW3 & STATS3 & LSJ3 & FL3 & IAS3 & IAM3).
  cbn [ms_mem] in PRES3, AH3.

  eapply implF_evtF with (P := fun ms' => ms' = _).
  { step. apply evtF_done. reflexivity. }
  cbv beta. intros ms4 ->.

  pose proof SS as SS0. rw_split SS0 1%nat FRp SZT. apply rw_cells_C4C4_to_C8 in SZT. 2: { clear -LTRC; lia. }
  rw_join FRp SZT SSA.
  unfold arealloc. eapply implS_sbind.
  { eapply (AHF_allocate_h L RNG _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ F fc m3 st LB n lo (bv_unsigned sp + -2136) AREALLOC_PC trc tb RESV).
    all: try lazymatch goal with
         | |- AHEAP_P AHF _ _ _ _ _ => apply AHF_of_AHI; [exact AH3| exact FL3]
         | |- mem_inv _ _ => exact MI3
         | |- stk _ _ _ _ => rewrite USP; exact ST3
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- rw_cells _ _ _ _ => exact SSA
         | |- u64arr _ _ _ _ => exact TB
         | |- In _ _ => exact TRU
         | |- aresv_ok _ _ => exact RESVOK
         | |- map _ _ = _ => exact TRF
         | |- rng _ _ _ => rewrite ?USP; eapply rng_sub; [exact RSTK| lia| lia]
         end.
    all: rewrite ?USP; unfold AMALLOC_STACK, AREQMAX in *; try lia; try assumption.
    all: match goal with |- ?G => idtac "REMAL" G end. }

  intros [st1 oq] RNG1 ms5 POST5. unfold aallocate_post_h in POST5. cbn [snd fst] in POST5 |- *. destruct oq as [q|].
  2: {
       destruct POST5 as (LE1 & t0d & t1d & t2d & a1d & a2d & a3d & a4d & a5d & a6d & a7d & t3d & t4d & t5d & t6d & m5 & -> & MI5 & ST5 & PRES5 & AHF5).
       destruct (AHI_of_AHF _ _ _ _ _ AHF5) as [AH5 FL5].
       rewrite USP in ST5, PRES5.
       replace (ret_pc (Z_to_bv 64 251752)) with (Z_to_bv 64 251752) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
       assert (CRS : forall A' n', bv_unsigned sp + -2208 <= A' -> A' + n' <= 2^47 -> aclient_range aci_I LB (bv_unsigned sp + -2208) A' n')
         by (intros A' n' H1 H2; left; left; split; assumption).
       eapply (aheap_pres_rw_cells _ _ _ _ _ _ _ PRES5) in FRR; [| apply CRS; cbn [cells_size csize Nat.add]; lia].
       eapply (aheap_pres_rw_cells _ _ _ _ _ _ _ PRES5) in FRa; [| apply CRS; cbn [cells_size csize Nat.add]; lia].
       eapply (aheap_pres_rw_cells _ _ _ _ _ _ _ PRES5) in FRp0; [| apply CRS; cbn [cells_size csize Nat.add]; lia].
       eapply (aheap_pres_rw_cells _ _ _ _ _ _ _ PRES5) in SS; [| apply CRS; cbn [cells_size csize Nat.add]; lia].
       eapply (aheap_pres_rw_cells _ _ _ _ _ _ _ PRES5) in FRS; [| apply CRS; cbn [cells_size csize Nat.add]; lia].
       eapply (aheap_pres_u64arr _ _ _ _ _ _ _ PRES5) in TB; [| apply CRS; rewrite ?LTB; lia].
       pose proof (F_afree_icpt.rw_cells_of_u64arr m5 _ tb TB) as TBC. rewrite LTB in TBC.
       replace (bv_unsigned sp + -2136 + 16) with (bv_unsigned sp + -2120) in TBC by lia.

       assert (ERR5 : rw_cells asegs m5 AERRNO [C4 e0]).
       { eapply aheap_pres_rw_cells; [exact PRES5| | cbn [cells_size csize Nat.add]; apply errno_client].
         eapply aheap_pres_rw_cells; [exact PRES3| exact ERR0| cbn [cells_size csize Nat.add]; apply errno_client]. }
       pose proof AH5 as (_ & ARNG5 & _). destruct ARNG5 as (RIMG5 & _).
       assert (RSTK1 : rng RNG1 lo (bv_unsigned sp - lo)) by (eapply rng_fp_le; [exact LE1| exact RSTK]).
       apply implS_ret.
       eapply evtF_mono.
       { eapply (ricptN_spec RNG1 _ sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ ra s0 s1 s2 s3 s4 s5 s6 sp _ _ _ _ _ F fc m5 lo junk2 junkR e0).
         all: try lazymatch goal with
              | |- stk _ _ _ _ => exact ST5
              | |- mem_inv _ _ => exact MI5
              | |- @eq word _ _ => exact TP
              | |- rw_cells _ _ AERRNO _ => exact ERR5
              | |- rw_cells _ _ _ _ => first [exact FRR | exact FRa | exact FRS]
              | |- exists _, rw_cells _ _ _ _ /\ _ => first [eexists; split; [exact FRp0| reflexivity] | eexists; split; [exact SS| reflexivity] | eexists; split; [exact TBC| reflexivity]]
              | |- rng_aimg _ => exact RIMG5
              | |- rng _ _ _ => exact RSTK1
              end.
         all: try lia.
         all: match goal with |- ?G => idtac "REMN" G end. }
       cbv beta. intros ms8 (t0g & t1g & t2g & a1g & a2g & a3g & a4g & a5g & a6g & a7g & t3g & t4g & t5g & t6g & m8 & -> & MU8 & WM8 & MI8 & ST8 & ERR8).
       unfold arealloc_post_h. cbn [snd fst]. split; [exact LE1|].
       exists t0g, t1g, t2g, a1g, a2g, a3g, a4g, a5g, a6g, a7g, t3g, t4g, t5g, t6g, m8.
       split; [reflexivity|]. split; [exact MI8|]. split; [exact ST8|].

       assert (CW8 : Forall (fun iv => aclient_range aci_I LB (ATOP + 4096) (fst iv) (snd iv - fst iv))
                            [(bv_unsigned sp - 2176, bv_unsigned sp - 2160); (AERRNO, AERRNO + 4)]%Z).
       { constructor; [| constructor; [| constructor]]; cbn [fst snd].
         - left. left. split; lia.
         - replace (AERRNO + 4 - AERRNO) with 4 by lia. apply errno_client. }
       split; [| split; [exact (AHI_frame L RNG1 st1 LB m5 m8 _ AH5 MU8 WM8 CW8)| exact ERR8]].
       intros a Ha CLA NERR.
       assert (E8 : m8 (wa a) = m5 (wa a) /\ (wview asegs m5 (wa a) <> None -> wview asegs m8 (wa a) <> None)).
       { split; [| intros Hw; apply WM8; exact Hw]. apply MU8. rewrite wa_unsigned by exact Ha. cbn [outside]. split; [| split; [exact NERR| exact I]].

         assert (BB : forall b, In b LB -> AIMG_HI <= ab_addr b /\ ab_addr b + ab_size b <= ATOP).
         { intros b Hb. pose proof (AHI_block_bounds L RNG1 st1 _ m5 b AH5 Hb) as (B1 & B2 & B3). lia. }
         destruct CLA as [SK | [CIa | [BLK | SH]]].
         - lia.
         - destruct CIa as (iv & Hiv & R). pose proof (aci_ok1 iv Hiv) as (Q1 & Q2). unfold AIMG_HI in *. lia.
         - destruct BLK as (b & Hb & R). destruct (BB b Hb) as (B1 & B2). lia.
         - destruct SH as (a' & Ha' & ->). rewrite shad_div in Ha |- *. unfold ASHOFF in *.
           assert (A47 : 0 <= a' < 2^47).
           { destruct Ha' as [SK | [CIa | FK]].
             - lia.
             - destruct CIa as (iv & Hiv & R). pose proof (aci_ok1 iv Hiv) as (Q1 & Q2). unfold AIMG_HI in *. lia.
             - destruct FK as (cls & FA & sz & Hin & R). destruct (BB _ Hin) as (B1 & B2). cbn [ab_addr ab_size] in B1, B2. unfold AIMG_HI in *. lia. }
           Z.div_mod_to_equations. lia. }
       destruct E8 as [E8 W8].
       destruct (PRES3 a Ha CLA) as [E3 W3]. cbn [ms_mem MS] in E3, W3.
       assert (CLA5 : aclient_addr aci_I LB (bv_unsigned sp + -2208) a).
       { destruct CLA as [SK | [CIa | [BLK | SH]]]; [left; lia| right; left; exact CIa| right; right; left; exact BLK| right; right; right; exact SH]. }
       destruct (PRES5 a Ha CLA5) as [E5 W5].
       split; [congruence| intros Hw; apply W8, W5, W3; exact Hw]. }
  destruct POST5 as (LE1 & t0d & t1d & t2d & a0d & a1d & a2d & a3d & a4d & a5d & a6d & a7d & t3d & t4d & t5d & t6d & m5 & -> & MI5 & ST5 & PRES5 & MATCH).
  cbn [snd fst] in MATCH.
  destruct MATCH as (UB & junk & -> & BRn & AHF5 & NEWC & RNGn & RNGsn & SECn).
  destruct (AHI_of_AHF _ _ _ _ _ AHF5) as [AH5 FL5].
  rewrite USP in ST5, PRES5.
  replace (ret_pc (Z_to_bv 64 251752)) with (Z_to_bv 64 251752) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  pose proof BRn as (BKn & _ & HIn & ALn). pose proof (ablk_lin _ _ BKn) as (GN1 & GN2 & GN3 & GN4). unfold AIMG_HI in GN1.
  assert (HIN5 : In (HB p A nold) (HB q UB n :: LB)) by (right; exact HIN).
  assert (QNE : HB q UB n <> HB p A nold).
  { intros E. pose proof (AHI_blocks_nodup L RNG1 st1 _ m5 AH5) as ND. inversion ND as [|x l NI _]; subst. apply NI. rewrite E. exact HIN. }
  pose proof (AHI_blocks_disjoint L RNG1 st1 _ m5 (HB q UB n) (HB p A nold) AH5 ltac:(left; reflexivity) HIN5 QNE) as DISJ. cbn [ab_addr ab_size] in DISJ.

  destruct (rw_cells_of_wr_at asegs m A nold WRo (no_image_asan A (A + nold) ltac:(lia)) ltac:(lia)) as (bs & LBS & CBo).
  set (k := Z.to_nat (Z.min n nold)).
  assert (KN : (k <= Z.to_nat nold)%nat) by (subst k; lia).
  destruct (cb_split2 m A (Z.to_nat nold) k bs LBS KN CBo) as [SRC0 _].
  set (src := firstn k bs) in *.
  assert (LSRC : length src = k) by (subst src; rewrite length_firstn; lia).
  assert (CRo : forall SPx, aclient_range aci_I LB SPx A (Z.of_nat k)).
  { intros SPx. right. left. exists (HB p A nold). split; [exact HIN|]. cbn [ab_addr ab_size]. subst k. lia. }
  assert (SRC5 : rw_cells asegs m5 A [CB k src]).
  { eapply aheap_pres_rw_cells; [exact PRES5| | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r; apply CRo].
    eapply aheap_pres_rw_cells; [exact PRES3| exact SRC0| cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r; apply CRo]. }
  assert (BSRC0 : bytes_at asegs m A src) by (destruct SRC0 as [[_ BA] _]; cbn [cells_bytes cbytes app] in BA; rewrite app_nil_r in BA; exact BA).
  assert (BSRC5 : bytes_at asegs m5 A src) by (destruct SRC5 as [[_ BA] _]; cbn [cells_bytes cbytes app] in BA; rewrite app_nil_r in BA; exact BA).

  assert (KN2 : (k <= Z.to_nat n)%nat) by (subst k; lia).
  assert (LJ : length junk = Z.to_nat n) by (destruct NEWC as [[WFc _] _]; cbn in WFc; tauto).
  destruct (cb_split2 m5 UB (Z.to_nat n) k junk LJ KN2 NEWC) as [DST5 REST5].

  destruct (live_header adepot_iface AFAKE L RNG1 st1 _ m5 p A nold AH5 HIN5) as (b1 & actx & HD5 & B1 & NO & A16 & RH5).
  pose proof (AFake_arep.AFake_arep.relro_word m5 0xd1540 0xd3420 (AHI_relro L RNG1 st1 _ m5 AH5) ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as GOT5.
  pose proof (AHI_rtcells L RNG1 st1 _ m5 AH5) as (_ & _ & _ & REAL5 & _).
  pose proof AH5 as (_ & ARNG5 & _). destruct ARNG5 as (RIMG5 & _).
  assert (RSTK1 : rng RNG1 lo (bv_unsigned sp - lo)) by (eapply rng_fp_le; [exact LE1| exact RSTK]).
  assert (MINK : Z.of_nat k = Z.min n nold) by (subst k; lia).

  replace (Z_to_bv 64 A) with (Z_to_bv 64 (A - 16 + 16)) by (f_equal; lia).
  eapply implF_evtF.
  { eapply (ricptC_spec RNG1 _ sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ F fc m5 (A - 16) n nold UB b1 actx src (firstn k junk)).
    all: try lazymatch goal with
         | |- mem_inv _ _ => exact MI5
         | |- rw_cells _ _ _ _ => first [exact HD5 | exact GOT5 | exact REAL5 | (fold k; exact DST5)]
         | |- bytes_at _ _ _ _ => replace (A - 16 + 16) with A by lia; exact BSRC5
         | |- length _ = _ => exact LSRC
         | |- rng_aimg _ => exact RIMG5
         | |- rng _ _ _ => first [exact RH5
                                 | (replace (A - 16 + 16) with A by lia; eapply rng_sub; [eapply rng_fp_le; [exact LE1| exact RNGo]| lia| lia])
                                 | (eapply rng_sub; [exact RNGn| lia| lia])]
         end.
    all: unfold AREQMAX in *; try lia.
    all: match goal with |- ?G => idtac "REMC" G end. }
  cbv beta. intros ms6 (t0e & t1e & t2e & a6e & a7e & t3e & t4e & t5e & t6e & m6 & -> & MU6 & WM6 & MI6 & DST6 & BSRC6).

  assert (AH6 : AHEAP_I L RNG1 st1 (HB q UB n :: LB) m6).
  { eapply AHI_frame; [exact AH5| exact MU6| exact WM6|].
    constructor; [| constructor]. cbn [fst snd]. right. left. exists (HB q UB n). split; [left; reflexivity|]. cbn [ab_addr ab_size]. lia. }

  assert (CRS : forall A' n', bv_unsigned sp + -2208 <= A' -> A' + n' <= 2^47 -> aclient_range aci_I LB (bv_unsigned sp + -2208) A' n')
    by (intros A' n' H1 H2; left; left; split; assumption).
  eapply (aheap_pres_rw_cells _ _ _ _ _ _ _ PRES5) in FRR; [| apply CRS; cbn [cells_size csize Nat.add]; lia].
  eapply (aheap_pres_rw_cells _ _ _ _ _ _ _ PRES5) in FRa; [| apply CRS; cbn [cells_size csize Nat.add]; lia].
  eapply (aheap_pres_rw_cells _ _ _ _ _ _ _ PRES5) in FRp0; [| apply CRS; cbn [cells_size csize Nat.add]; lia].
  eapply (aheap_pres_rw_cells _ _ _ _ _ _ _ PRES5) in SS; [| apply CRS; cbn [cells_size csize Nat.add]; lia].
  eapply (aheap_pres_rw_cells _ _ _ _ _ _ _ PRES5) in FRS; [| apply CRS; cbn [cells_size csize Nat.add]; lia].
  eapply (aheap_pres_u64arr _ _ _ _ _ _ _ PRES5) in TB; [| apply CRS; rewrite ?LTB; lia].
  xport FRR MU6 WM6 ltac:(lia). xport FRa MU6 WM6 ltac:(lia). xport FRp0 MU6 WM6 ltac:(lia). xport SS MU6 WM6 ltac:(lia).
  xport FRS MU6 WM6 ltac:(lia). xport TB MU6 WM6 ltac:(rewrite LTB; lia). xport ST5 MU6 WM6 ltac:(lia).
  unfold aia_on in FL5. xport FL5 MU6 WM6 ltac:(unfold AIA_FLAG; lia).
  xport REST5 MU6 WM6 ltac:(lia).

  eapply implF_evtF with (P := fun ms' => ms' = _).
  { step. apply evtF_done. reflexivity. }
  cbv beta. intros ms6' ->.
  eapply implS_sbind.
  { eapply (AHI_dealloc L RNG1 _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ F fc m6 st1 (HB q UB n :: LB) p A nold lo
              (bv_unsigned sp + -2136) AREALLOC_PC tb trc).
    all: try lazymatch goal with
         | |- AHEAP_P _ _ _ _ _ _ => exact AH6
         | |- In (HB _ _ _) _ => exact HIN5
         | |- mem_inv _ _ => exact MI6
         | |- stk _ _ _ _ => rewrite USP; exact ST5
         | |- @eq word _ _ => first [reflexivity | exact TP | (f_equal; lia)]
         | |- rw_cells _ _ _ _ => first [exact SS | exact FL5]
         | |- u64arr _ _ _ _ => exact TB
         | |- In _ (al_U _) => exact TRU
         | |- map _ _ = _ => exact TRF
         | |- rng _ _ _ => rewrite ?USP; eapply rng_sub; [exact RSTK1| lia| lia]
         end.
    all: rewrite ?USP; rewrite ?unsigned_lit by lia; unfold AFREE_STACK in *; try lia; try assumption.
    all: match goal with |- ?G => idtac "REMD" G end. }

  intros st2 RNG2 ms7 (LE2 & t0f & t1f & t2f & a0f & a1f & a2f & a3f & a4f & a5f & a6f & a7f & t3f & t4f & t5f & t6f & m7 & -> & MI7 & ST7 & PRES7 & AH7).
  rewrite USP in ST7, PRES7.
  replace (ret_pc (Z_to_bv 64 251900)) with (Z_to_bv 64 251900) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  assert (QP : q <> p).
  { intros ->. pose proof (AHI_hb_ids L RNG1 st1 _ m5 AH5) as ND. cbn [hb_ids flat_map ab_kind app] in ND. inversion ND as [|x l NI _]; subst. apply NI.
    apply in_flat_map. exists (HB p A nold). split; [exact HIN| left; reflexivity]. }
  pose proof (AFreeRep.lb_remove_cons_other p q UB n LB QP) as ELB.
  rewrite ELB in PRES7, AH7.
  assert (SUBR : forall b, In b (lb_remove p LB) -> In b LB) by (intros b Hb; apply AFreeRep.In_lb_remove in Hb; tauto).

  assert (CRS7 : forall A' n', bv_unsigned sp + -2208 <= A' -> A' + n' <= 2^47 -> aclient_range aci_I (HB q UB n :: lb_remove p LB) (bv_unsigned sp + -2208) A' n')
    by (intros A' n' H1 H2; left; left; split; assumption).
  eapply (aheap_pres_rw_cells _ _ _ _ _ _ _ PRES7) in FRR; [| apply CRS7; cbn [cells_size csize Nat.add]; lia].
  eapply (aheap_pres_rw_cells _ _ _ _ _ _ _ PRES7) in FRa; [| apply CRS7; cbn [cells_size csize Nat.add]; lia].
  eapply (aheap_pres_rw_cells _ _ _ _ _ _ _ PRES7) in FRp0; [| apply CRS7; cbn [cells_size csize Nat.add]; lia].
  eapply (aheap_pres_rw_cells _ _ _ _ _ _ _ PRES7) in SS; [| apply CRS7; cbn [cells_size csize Nat.add]; lia].
  eapply (aheap_pres_rw_cells _ _ _ _ _ _ _ PRES7) in FRS; [| apply CRS7; cbn [cells_size csize Nat.add]; lia].
  eapply (aheap_pres_u64arr _ _ _ _ _ _ _ PRES7) in TB; [| apply CRS7; rewrite ?LTB; lia].
  pose proof (F_afree_icpt.rw_cells_of_u64arr m7 _ tb TB) as TBC. rewrite LTB in TBC.
  replace (bv_unsigned sp + -2136 + 16) with (bv_unsigned sp + -2120) in TBC by lia.

  assert (NEW6 : rw_cells asegs m6 UB [CB (Z.to_nat (Z.min n nold)) src; CB (Z.to_nat (n - Z.min n nold)) (skipn k junk)]).
  { change [CB (Z.to_nat (Z.min n nold)) src; CB (Z.to_nat (n - Z.min n nold)) (skipn k junk)]
      with ([CB (Z.to_nat (Z.min n nold)) src] ++ [CB (Z.to_nat (n - Z.min n nold)) (skipn k junk)]).
    apply rw_cells_app. split; [exact DST6|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r.
    replace (Z.to_nat (n - Z.min n nold)) with (Z.to_nat n - k)%nat by (subst k; lia). exact REST5. }
  assert (NEW7 : rw_cells asegs m7 UB [CB (Z.to_nat (Z.min n nold)) src; CB (Z.to_nat (n - Z.min n nold)) (skipn k junk)]).
  { eapply aheap_pres_rw_cells; [exact PRES7| exact NEW6|]. right. left. exists (HB q UB n). split; [left; reflexivity|].
    cbn [ab_addr ab_size cells_size csize Nat.add]. lia. }
  pose proof AH7 as (_ & ARNG7 & _). destruct ARNG7 as (RIMG7 & _).

  apply implS_ret.
  eapply evtF_mono.
  { eapply (ricptE_spec RNG2 _ sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ ra s0 s1 s2 s3 s4 s5 s6 sp _ _ _ _ _ F fc m7 lo UB junk2 junkR).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact ST7
         | |- mem_inv _ _ => exact MI7
         | |- rw_cells _ _ _ _ => first [exact FRR | exact FRa | exact FRS]
         | |- exists _, rw_cells _ _ _ _ /\ _ => first [eexists; split; [exact FRp0| reflexivity] | eexists; split; [exact SS| reflexivity] | eexists; split; [exact TBC| reflexivity]]
         | |- rng_aimg _ => exact RIMG7
         | |- rng _ _ _ => eapply rng_fp_le; [exact LE2| exact RSTK1]
         end.
    all: try lia.
    all: match goal with |- ?G => idtac "REME" G end. }
  cbv beta. intros ms8 (a0g & a1g & a2g & a3g & a4g & a5g & a6g & a7g & t0g & t1g & t2g & t3g & t4g & t5g & t6g & -> & _ & ST8).

  unfold arealloc_post_h, arealloc_post. cbn [snd fst]. split; [exact (fp_le_trans _ _ _ LE1 LE2)|].
  exists t0g, t1g, t2g, (Z_to_bv 64 UB), a1g, a2g, a3g, a4g, a5g, a6g, a7g, t3g, t4g, t5g, t6g, m7.
  split; [reflexivity|]. split; [exact MI7|]. split; [exact ST8|]. split.
  {
    eapply aheap_pres_trans; [eapply aheap_pres_weaken; [exact PRES3| lia| exact SUBR]|].
    eapply aheap_pres_trans; [eapply aheap_pres_weaken; [exact PRES5| lia| exact SUBR]|].
    eapply aheap_pres_trans; [eapply (pres_head_write L RNG1 st1 LB m5 m6 q UB n (Z.min n nold) (lb_remove p LB) (bv_unsigned sp)); [exact AH5| exact MU6| exact WM6| lia| exact BRn| exact SUBR| lia]|].
    eapply aheap_pres_weaken; [exact PRES7| lia| intros b Hb; right; exact Hb]. }
  cbn [snd fst].
  exists UB, src, (skipn k junk).
  split; [reflexivity|]. split; [exact BRn|]. split; [exact AH7|]. split; [exact BSRC0|]. split; [exact LSRC|]. split; [exact NEW7|].
  split; [eapply rng_fp_le; [exact LE2| exact RNGn]| eapply rng_fp_le; [exact LE2| exact RNGsn]].
Qed.
End CANSEC2.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.Shadow.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import RtCells.TwinB AProto.TwinB ABase.TwinB ABytes.TwinB AQConst.TwinB AKitQ.TwinB AMalloc_iface.TwinB ADepot_iface.TwinB APoisonR_iface.TwinB ARep.TwinB ARepQ.TwinB ARepQP.TwinB ALayout.TwinB AHeapP.TwinB AKit.TwinB AKit2.TwinB ASec.TwinB F_amalloc_arep.TwinB F_afree_arep.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc1.TwinB.F_aalloc1. Import F_adepot.TwinB AFake_iface.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFake_arep.TwinB.AFake_arep. Import F_apoison_remap.TwinB AInstance.TwinB AInstanceM.TwinB AInstanceF.TwinB AFreeAll.TwinB.
Import ADeallocate.TwinB AEmbedBind.TwinB F_arealloc_iseg.TwinB F_arealloc_pre.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeNull.TwinB.AReallocFront. Import AReallocRead.TwinB.
Import AFrameD.TwinB AHolesD.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ASF_kit.TwinB.ASF_kit. Import AEmbRep.TwinB AExh.TwinB ARefill_iface_x.TwinB ARefillP_x.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AMallocPG_x.TwinB.AMallocPG_x. Import AMalloc_x.TwinB AInstanceD.TwinB AInstanceX.TwinB F_arealloc_null.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC2. Context {rc : runConstT} {ov : annOV} {gb : GcBit}.

Definition aia_on (m : amem) : Prop :=
  rw_cells bsegs m AIA_FLAG [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Definition AQF (L : alayout) (st : astate) (X : aconc) (m : amem) : Prop := AQUAR L st X m /\ aia_on m.
Definition AHF : aholes := F_amalloc_arep.TwinB.AH adepot_iface AQF ASEC_of AFAKE.

Lemma AHF_laws : ahole_laws AHF.
Proof.
  pose proof AH_laws as HL. constructor.
  - intros L st st' X X' m m' W [HQ FLG] MU WM UT QS. split.
    + exact (hq_frame _ HL L st st' X X' m m' W HQ MU WM UT QS).
    + unfold aia_on in *. eapply rw_cells_transport; [exact FLG| exact MU| exact WM|].
      apply ARepQP.TwinB.disjoint_from_Forall. eapply Forall_impl; [| exact UT]. intros iv (_ & _ & _ & A & _).
      unfold AIA_FLAG. cbn [cells_size csize Nat.add]. cbn in A |- *. lia.
  - exact (hs_frame _ HL).
  - exact (hd_frame _ HL).
  - exact (hf_frame _ HL).
  - exact (hf_blocks _ HL).
Qed.

Lemma AHF_lawsD : ahole_lawsD AHF.
Proof.
  pose proof AH_lawsD as HLD. constructor.
  - intros L st st' X X' m m' W [HQ FLG] MU UT QS. split.
    + exact (hqD _ HLD L st st' X X' m m' W HQ MU UT QS).
    + unfold aia_on in *. eapply rw_cells_transportD; [exact FLG| exact MU|].
      apply ARepQP.TwinB.disjoint_from_Forall. eapply Forall_impl; [| exact UT]. intros iv (_ & _ & _ & A & _).
      unfold AIA_FLAG. cbn [cells_size csize Nat.add]. cbn in A |- *. lia.
  - exact (hx_get _ HLD).
  - exact (hsD _ HLD).
  - exact (hdD _ HLD).
  - exact (hfD _ HLD).
Qed.

Lemma AHF_of_AHI : forall L RNG st LB m, AHEAP_P AHI L RNG st LB m -> aia_on m -> AHEAP_P AHF L RNG st LB m.
Proof.
  intros L RNG st LB m (ALO & ARNG & [X [AR BL]] & HFK) FLG.
  destruct AR as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  split; [exact ALO|]. split; [exact ARNG|]. split; [| exact HFK].
  exists X. split; [| exact BL].
  split; [exact WF|]. split; [exact RT|]. split; [exact INST|]. split; [exact THR|]. split; [exact CLS|].
  split; [exact (conj HQ FLG)|]. split; [exact HS|]. split; [exact HD|]. split; [exact HRO|]. split; [exact RT2|]. split; [exact AVL| exact RT3].
Qed.

Lemma AHI_of_AHF : forall L RNG st LB m, AHEAP_P AHF L RNG st LB m -> AHEAP_P AHI L RNG st LB m /\ aia_on m.
Proof.
  intros L RNG st LB m (ALO & ARNG & [X [AR BL]] & HFK).
  destruct AR as (WF & RT & INST & THR & CLS & [HQ FLG] & HS & HD & HRO & RT2 & AVL & RT3).
  split; [| exact FLG].
  split; [exact ALO|]. split; [exact ARNG|]. split; [| exact HFK].
  exists X. split; [| exact BL].
  split; [exact WF|]. split; [exact RT|]. split; [exact INST|]. split; [exact THR|]. split; [exact CLS|].
  split; [exact HQ|]. split; [exact HS|]. split; [exact HD|]. split; [exact HRO|]. split; [exact RT2|]. split; [exact AVL| exact RT3].
Qed.

Hypothesis EXHW : exh_first_stmt.
Theorem AHF_allocate_h : aallocate_stmt_h aci_I (AHEAP_P AHF).
Proof. exact (aallocate_all_h adepot_iface AQF AFAKE AHF_laws AHF_lawsD EXHW poison_remap_proof aci_I aci_ok aci_ok2 aci_ok3). Qed.

Definition AREALLOC_STACK : Z := 8192.

Definition arealloc (RESV : list (Z * Z)) (st : astate) (p : aptr) (n : Z) : AM (astate * option aptr) :=
  sbind (amalloc ATOP RESV st n) (fun r =>
    match snd r with
    | Some q => sbind (afree (fst r) (Some p)) (fun st2 => aret (st2, Some q))
    | None => aret r
    end).

Section Stmt.
Variable CI : list (Z * Z).
Variable AHEAP : alayout -> footprint -> astate -> list ablock -> amem -> Prop.

Definition arealloc_post (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (p : aptr) (A nold n lo : Z) (m : amem)
    (r : astate * option aptr) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI (lb_remove p LB) (bv_unsigned sp) m m'
    /\ match snd r with
       | None => False
       | Some q => exists UB (src junk : list byte),
           a0 = Z_to_bv 64 UB /\ ablock_range UB n
           /\ AHEAP L RNG' (fst r) (HB q UB n :: lb_remove p LB) m'

           /\ bytes_at bsegs m A src /\ length src = Z.to_nat (Z.min n nold)
           /\ rw_cells bsegs m' UB [CB (Z.to_nat (Z.min n nold)) src; CB (Z.to_nat (n - Z.min n nold)) junk]
           /\ rng RNG' UB n /\ rng RNG' (shad UB) (shlen (n + 7))
       end.

Definition arealloc_post_h (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (p : aptr) (A nold n lo : Z) (m : amem)
    (r : astate * option aptr) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' =>
    match snd r with
    | Some _ => arealloc_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p A nold n lo m r RNG' ms'
    | None => fp_le RNG RNG' /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None m' (seg_rom bsegs)
        /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
        /\ aheap_pres_e CI LB (bv_unsigned sp) m m'
        /\ AHEAP L RNG' (fst r) LB m'
        /\ rw_cells bsegs m' AERRNO [C4 (Z_to_bv 64 12)]
    end.
Definition arealloc_stmt_h : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (st : astate) (LB : list ablock) (p : aptr) (A nold n lo : Z) (tr : list Z) (RESV : list (Z * Z)),
  ann_ov (a_next st) = None ->
  AHEAP L RNG st LB m -> In (HB p A nold) LB ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AREALLOC_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> 1 <= n <= AREQMAX ->
  aunw m L RNG lo AREALLOC_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AREALLOC_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  aresv_ok L RESV ->

  bv_unsigned fc < 32 -> c6m RESV RNG st -> (let '(_, cap0, _) := a_emb st in cap0 <= 2 ^ 23) ->
  (exists e0 : word, rw_cells bsegs m AERRNO [C4 e0]) ->
  implS bsegs RNG (aembed ATOP (arealloc RESV st p n))
        (epostF (arealloc_post_h L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p A nold n lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AREALLOC_SYM) fc None m (seg_rom bsegs)).
End Stmt.

Lemma aheap_pres_u64arr : forall CI LB SP m m' A ws,
  aheap_pres CI LB SP m m' -> u64arr bsegs m A ws -> aclient_range CI LB SP A (8 * Z.of_nat (length ws)) -> u64arr bsegs m' A ws.
Proof.
  intros CI LB SP m m' A ws HP [BA WR] CR. split.
  - eapply aheap_pres_bytes_at; [exact HP| exact BA|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact CR.
  - eapply aheap_pres_wr_at; [exact HP| exact WR| exact CR].
Qed.

Lemma cb_split2 : forall m A (n k : nat) bs, length bs = n -> (k <= n)%nat ->
  rw_cells bsegs m A [CB n bs] ->
  rw_cells bsegs m A [CB k (firstn k bs)] /\ rw_cells bsegs m (A + Z.of_nat k) [CB (n - k) (skipn k bs)].
Proof.
  intros m A n k bs LN K H.
  pose proof (rw_cells_split_CB bsegs m A [] _ _ [] [k; (n - k)%nat] H ltac:(cbn; lia)) as SP. cbn [app mk_CB_cells] in SP.
  rewrite (firstn_all2 (n := (n - k)%nat) (skipn k bs)) in SP by (rewrite length_skipn; lia).
  change [CB k (firstn k bs); CB (n - k) (skipn k bs)] with ([CB k (firstn k bs)] ++ [CB (n - k) (skipn k bs)]) in SP.
  apply rw_cells_app in SP. destruct SP as [H1 H2]. cbn [cells_size csize] in H2. rewrite Nat.add_0_r in H2. split; assumption.
Qed.

Lemma pres_head_write : forall L RNG st LB m m' (q : aptr) UB n k LBk SP,
  AHEAP_I L RNG st (HB q UB n :: LB) m -> munch [(UB, UB + k)]%Z m m' -> wmono bsegs m m' -> 0 <= k <= n -> ablock_range UB n ->
  (forall b, In b LBk -> In b LB) -> ATOP <= SP ->
  aheap_pres aci_I LBk SP m m'.
Proof.
  intros L RNG st LB m m' q UB n k LBk SP AH MU WM K BR SUB HSP a Ha CLA.
  split; [| intros Hw; apply WM; exact Hw].
  apply MU. rewrite wa_unsigned by exact Ha. cbn [outside]. split; [| exact I].
  pose proof BR as (BK & _ & HI & _). pose proof atop_range as ATR.
  assert (NI : ~ In (HB q UB n) LB) by (pose proof (AHI_blocks_nodup L RNG st _ m AH) as ND; inversion ND; assumption).
  assert (BB : forall b, In b LB -> AIMG_HI <= ab_addr b /\ ab_addr b + ab_size b <= ATOP /\ (UB + n <= ab_addr b \/ ab_addr b + ab_size b <= UB)).
  { intros b Hb. pose proof (AHI_block_bounds L RNG st _ m b AH ltac:(right; exact Hb)) as (B1 & B2 & B3).
    assert (NE : HB q UB n <> b) by (intros E; apply NI; rewrite E; exact Hb).
    pose proof (AHI_blocks_disjoint L RNG st _ m (HB q UB n) b AH ltac:(left; reflexivity) ltac:(right; exact Hb) NE) as D. cbn [ab_addr ab_size] in D. lia. }
  destruct CLA as [SK | [CIa | [BLK | SH]]].
  - pose proof (ablk_lin _ _ BK) as (_ & _ & G3 & _). lia.
  - destruct CIa as (iv & Hiv & R). pose proof (aci_ok1 iv Hiv) as (Q1 & Q2). pose proof (ablk_lin _ _ BK) as (G1 & _). lia.
  - destruct BLK as (b & Hb & R). destruct (BB b (SUB b Hb)) as (_ & _ & D). lia.
  - destruct SH as (a' & Ha' & ->). rewrite shad_div in Ha |- *. unfold ASHOFF in *.
    assert (A47 : 0 <= a' < 2^47).
    { destruct Ha' as [SK | [CIa | FK]].
      - lia.
      - destruct CIa as (iv & Hiv & R). pose proof (aci_ok1 iv Hiv) as (Q1 & Q2). unfold AIMG_HI in *. lia.
      - destruct FK as (cls & FA & sz & Hin & R). destruct (BB _ (SUB _ Hin)) as (B1 & B2 & _). cbn [ab_addr ab_size] in B1, B2. unfold AIMG_HI in *. lia. }
    unfold ablk, AIMG_HI, KLS in BK. Z.div_mod_to_equations. lia.
Qed.

Lemma errno_client : forall LB SP, aclient_range aci_I LB SP AERRNO 4.
Proof.
  intros LB SP. left. right. left. exists (0x5fe2d0, 0x60ede8). split; [unfold aci_I, msg_img_ranges; cbn [In]; tauto|].
  unfold AERRNO, ATP. cbn [fst snd]. lia.
Qed.

Theorem AHI_realloc_h : arealloc_stmt_h aci_I AHEAP_I.
Proof.
  unfold arealloc_stmt_h. intros until RESV. intros OVF AH HIN MI ST BOT LO TP Ha0 Ha1 NR AUNW S0NE RA4 RANE SP16 RSTK RESVOK FCB C6M CAPB [e0 ERR0].
  pose proof (AHI_block L RNG st LB m p A nold AH HIN) as (NOLD & BRo & RNGo & RNGso & SHo & WRo & CHo & ARENAo).
  pose proof BRo as (BKo & _ & HIo & ALo). pose proof (ablk_lin _ _ BKo) as (GL1 & GL2 & GL3 & GL4).
  pose proof atop_range as ATR. unfold AIMG_HI in GL1.
  assert (SP47 : bv_unsigned sp < 2^47).
  { destruct AUNW as [(X1 & _)|(_ & X2 & _)]; [| exact X2]. pose proof (AHI_layout L RNG st LB m AH) as (_ & _ & TOP47 & _). lia. }
  word_range sp SPR. unfold AREALLOC_STACK in LO.
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -2208)) = bv_unsigned sp + -2208) by (apply unsigned_lit; lia).

  eapply implF_evtF.
  { eapply (arealloc_frontP adepot_iface ASEC_of AFAKE AH_laws aci_I aci_okQ L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB A n lo tr);
      try eassumption; unfold AFREE_STACK, AREALLOC_STACK, AREQMAX in *; lia. }
  cbv beta. intros ms3 (trc & sj & PRE & TRU & LTRC & PRES3 & AH3).
  unfold realloc_pre_post in PRE.
  destruct PRE as (t0c & t1c & t2c & a7c & t3c & t4c & t5c & t6c & m3 & sj' & tb & junk0 & junk2 & junkR & -> & MU3 & WM3 & MI3 & ST3 & FRR & FRa & FRp0 & SS & TB & LTB & TRF & FRS
                   & UNW3 & STATS3 & LSJ3 & FL3 & IAS3 & IAM3).
  cbn [ms_mem] in PRES3, AH3.

  eapply implF_evtF with (P := fun ms' => ms' = _).
  { step. apply evtF_done. reflexivity. }
  cbv beta. intros ms4 ->.

  pose proof SS as SS0. rw_split SS0 1%nat FRp SZT. apply rw_cells_C4C4_to_C8 in SZT. 2: { clear -LTRC; lia. }
  rw_join FRp SZT SSA.
  unfold arealloc. eapply implS_sbind.
  { eapply (AHF_allocate_h L RNG _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ F fc m3 st LB n lo (bv_unsigned sp + -2136) AREALLOC_PC trc tb RESV).
    all: try lazymatch goal with
         | |- AHEAP_P AHF _ _ _ _ _ => apply AHF_of_AHI; [exact AH3| exact FL3]
         | |- mem_inv _ _ => exact MI3
         | |- stk _ _ _ _ => rewrite USP; exact ST3
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- rw_cells _ _ _ _ => exact SSA
         | |- u64arr _ _ _ _ => exact TB
         | |- In _ _ => exact TRU
         | |- aresv_ok _ _ => exact RESVOK
         | |- map _ _ = _ => exact TRF
         | |- rng _ _ _ => rewrite ?USP; eapply rng_sub; [exact RSTK| lia| lia]
         end.
    all: rewrite ?USP; unfold AMALLOC_STACK, AREQMAX in *; try lia; try assumption.
    all: match goal with |- ?G => idtac "REMAL" G end. }

  intros [st1 oq] RNG1 ms5 POST5. unfold aallocate_post_h in POST5. cbn [snd fst] in POST5 |- *. destruct oq as [q|].
  2: {
       destruct POST5 as (LE1 & t0d & t1d & t2d & a1d & a2d & a3d & a4d & a5d & a6d & a7d & t3d & t4d & t5d & t6d & m5 & -> & MI5 & ST5 & PRES5 & AHF5).
       destruct (AHI_of_AHF _ _ _ _ _ AHF5) as [AH5 FL5].
       rewrite USP in ST5, PRES5.
       replace (ret_pc (Z_to_bv 64 254200)) with (Z_to_bv 64 254200) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
       assert (CRS : forall A' n', bv_unsigned sp + -2208 <= A' -> A' + n' <= 2^47 -> aclient_range aci_I LB (bv_unsigned sp + -2208) A' n')
         by (intros A' n' H1 H2; left; left; split; assumption).
       eapply (aheap_pres_rw_cells _ _ _ _ _ _ _ PRES5) in FRR; [| apply CRS; cbn [cells_size csize Nat.add]; lia].
       eapply (aheap_pres_rw_cells _ _ _ _ _ _ _ PRES5) in FRa; [| apply CRS; cbn [cells_size csize Nat.add]; lia].
       eapply (aheap_pres_rw_cells _ _ _ _ _ _ _ PRES5) in FRp0; [| apply CRS; cbn [cells_size csize Nat.add]; lia].
       eapply (aheap_pres_rw_cells _ _ _ _ _ _ _ PRES5) in SS; [| apply CRS; cbn [cells_size csize Nat.add]; lia].
       eapply (aheap_pres_rw_cells _ _ _ _ _ _ _ PRES5) in FRS; [| apply CRS; cbn [cells_size csize Nat.add]; lia].
       eapply (aheap_pres_u64arr _ _ _ _ _ _ _ PRES5) in TB; [| apply CRS; rewrite ?LTB; lia].
       pose proof (F_afree_icpt.TwinB.rw_cells_of_u64arr m5 _ tb TB) as TBC. rewrite LTB in TBC.
       replace (bv_unsigned sp + -2136 + 16) with (bv_unsigned sp + -2120) in TBC by lia.

       assert (ERR5 : rw_cells bsegs m5 AERRNO [C4 e0]).
       { eapply aheap_pres_rw_cells; [exact PRES5| | cbn [cells_size csize Nat.add]; apply errno_client].
         eapply aheap_pres_rw_cells; [exact PRES3| exact ERR0| cbn [cells_size csize Nat.add]; apply errno_client]. }
       pose proof AH5 as (_ & ARNG5 & _). destruct ARNG5 as (RIMG5 & _).
       assert (RSTK1 : rng RNG1 lo (bv_unsigned sp - lo)) by (eapply rng_fp_le; [exact LE1| exact RSTK]).
       apply implS_ret.
       eapply evtF_mono.
       { eapply (ricptN_spec RNG1 _ sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ ra s0 s1 s2 s3 s4 s5 s6 sp _ _ _ _ _ F fc m5 lo junk2 junkR e0).
         all: try lazymatch goal with
              | |- stk _ _ _ _ => exact ST5
              | |- mem_inv _ _ => exact MI5
              | |- @eq word _ _ => exact TP
              | |- rw_cells _ _ AERRNO _ => exact ERR5
              | |- rw_cells _ _ _ _ => first [exact FRR | exact FRa | exact FRS]
              | |- exists _, rw_cells _ _ _ _ /\ _ => first [eexists; split; [exact FRp0| reflexivity] | eexists; split; [exact SS| reflexivity] | eexists; split; [exact TBC| reflexivity]]
              | |- rng_aimg _ => exact RIMG5
              | |- rng _ _ _ => exact RSTK1
              end.
         all: try lia.
         all: match goal with |- ?G => idtac "REMN" G end. }
       cbv beta. intros ms8 (t0g & t1g & t2g & a1g & a2g & a3g & a4g & a5g & a6g & a7g & t3g & t4g & t5g & t6g & m8 & -> & MU8 & WM8 & MI8 & ST8 & ERR8).
       unfold arealloc_post_h. cbn [snd fst]. split; [exact LE1|].
       exists t0g, t1g, t2g, a1g, a2g, a3g, a4g, a5g, a6g, a7g, t3g, t4g, t5g, t6g, m8.
       split; [reflexivity|]. split; [exact MI8|]. split; [exact ST8|].

       assert (CW8 : Forall (fun iv => aclient_range aci_I LB (ATOP + 4096) (fst iv) (snd iv - fst iv))
                            [(bv_unsigned sp - 2176, bv_unsigned sp - 2160); (AERRNO, AERRNO + 4)]%Z).
       { constructor; [| constructor; [| constructor]]; cbn [fst snd].
         - left. left. split; lia.
         - replace (AERRNO + 4 - AERRNO) with 4 by lia. apply errno_client. }
       split; [| split; [exact (AHI_frame L RNG1 st1 LB m5 m8 _ AH5 MU8 WM8 CW8)| exact ERR8]].
       intros a Ha CLA NERR.
       assert (E8 : m8 (wa a) = m5 (wa a) /\ (wview bsegs m5 (wa a) <> None -> wview bsegs m8 (wa a) <> None)).
       { split; [| intros Hw; apply WM8; exact Hw]. apply MU8. rewrite wa_unsigned by exact Ha. cbn [outside]. split; [| split; [exact NERR| exact I]].

         assert (BB : forall b, In b LB -> AIMG_HI <= ab_addr b /\ ab_addr b + ab_size b <= ATOP).
         { intros b Hb. pose proof (AHI_block_bounds L RNG1 st1 _ m5 b AH5 Hb) as (B1 & B2 & B3). lia. }
         destruct CLA as [SK | [CIa | [BLK | SH]]].
         - lia.
         - destruct CIa as (iv & Hiv & R). pose proof (aci_ok1 iv Hiv) as (Q1 & Q2). unfold AIMG_HI in *. lia.
         - destruct BLK as (b & Hb & R). destruct (BB b Hb) as (B1 & B2). lia.
         - destruct SH as (a' & Ha' & ->). rewrite shad_div in Ha |- *. unfold ASHOFF in *.
           assert (A47 : 0 <= a' < 2^47).
           { destruct Ha' as [SK | [CIa | FK]].
             - lia.
             - destruct CIa as (iv & Hiv & R). pose proof (aci_ok1 iv Hiv) as (Q1 & Q2). unfold AIMG_HI in *. lia.
             - destruct FK as (cls & FA & sz & Hin & R). destruct (BB _ Hin) as (B1 & B2). cbn [ab_addr ab_size] in B1, B2. unfold AIMG_HI in *. lia. }
           Z.div_mod_to_equations. lia. }
       destruct E8 as [E8 W8].
       destruct (PRES3 a Ha CLA) as [E3 W3]. cbn [ms_mem MS] in E3, W3.
       assert (CLA5 : aclient_addr aci_I LB (bv_unsigned sp + -2208) a).
       { destruct CLA as [SK | [CIa | [BLK | SH]]]; [left; lia| right; left; exact CIa| right; right; left; exact BLK| right; right; right; exact SH]. }
       destruct (PRES5 a Ha CLA5) as [E5 W5].
       split; [congruence| intros Hw; apply W8, W5, W3; exact Hw]. }
  destruct POST5 as (LE1 & t0d & t1d & t2d & a0d & a1d & a2d & a3d & a4d & a5d & a6d & a7d & t3d & t4d & t5d & t6d & m5 & -> & MI5 & ST5 & PRES5 & MATCH).
  cbn [snd fst] in MATCH.
  destruct MATCH as (UB & junk & -> & BRn & AHF5 & NEWC & RNGn & RNGsn & SECn).
  destruct (AHI_of_AHF _ _ _ _ _ AHF5) as [AH5 FL5].
  rewrite USP in ST5, PRES5.
  replace (ret_pc (Z_to_bv 64 254200)) with (Z_to_bv 64 254200) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  pose proof BRn as (BKn & _ & HIn & ALn). pose proof (ablk_lin _ _ BKn) as (GN1 & GN2 & GN3 & GN4). unfold AIMG_HI in GN1.
  assert (HIN5 : In (HB p A nold) (HB q UB n :: LB)) by (right; exact HIN).
  assert (QNE : HB q UB n <> HB p A nold).
  { intros E. pose proof (AHI_blocks_nodup L RNG1 st1 _ m5 AH5) as ND. inversion ND as [|x l NI _]; subst. apply NI. rewrite E. exact HIN. }
  pose proof (AHI_blocks_disjoint L RNG1 st1 _ m5 (HB q UB n) (HB p A nold) AH5 ltac:(left; reflexivity) HIN5 QNE) as DISJ. cbn [ab_addr ab_size] in DISJ.

  destruct (rw_cells_of_wr_at bsegs m A nold WRo (no_image_asan A (A + nold) ltac:(lia)) ltac:(lia)) as (bs & LBS & CBo).
  set (k := Z.to_nat (Z.min n nold)).
  assert (KN : (k <= Z.to_nat nold)%nat) by (subst k; lia).
  destruct (cb_split2 m A (Z.to_nat nold) k bs LBS KN CBo) as [SRC0 _].
  set (src := firstn k bs) in *.
  assert (LSRC : length src = k) by (subst src; rewrite length_firstn; lia).
  assert (CRo : forall SPx, aclient_range aci_I LB SPx A (Z.of_nat k)).
  { intros SPx. right. left. exists (HB p A nold). split; [exact HIN|]. cbn [ab_addr ab_size]. subst k. lia. }
  assert (SRC5 : rw_cells bsegs m5 A [CB k src]).
  { eapply aheap_pres_rw_cells; [exact PRES5| | cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r; apply CRo].
    eapply aheap_pres_rw_cells; [exact PRES3| exact SRC0| cbn [cells_size csize Nat.add]; rewrite Nat.add_0_r; apply CRo]. }
  assert (BSRC0 : bytes_at bsegs m A src) by (destruct SRC0 as [[_ BA] _]; cbn [cells_bytes cbytes app] in BA; rewrite app_nil_r in BA; exact BA).
  assert (BSRC5 : bytes_at bsegs m5 A src) by (destruct SRC5 as [[_ BA] _]; cbn [cells_bytes cbytes app] in BA; rewrite app_nil_r in BA; exact BA).

  assert (KN2 : (k <= Z.to_nat n)%nat) by (subst k; lia).
  assert (LJ : length junk = Z.to_nat n) by (destruct NEWC as [[WFc _] _]; cbn in WFc; tauto).
  destruct (cb_split2 m5 UB (Z.to_nat n) k junk LJ KN2 NEWC) as [DST5 REST5].

  destruct (live_header adepot_iface AFAKE L RNG1 st1 _ m5 p A nold AH5 HIN5) as (b1 & actx & HD5 & B1 & NO & A16 & RH5).
  pose proof (AFake_arep.TwinB.AFake_arep.relro_word m5 0xd3658 0xd5538 (AHI_relro L RNG1 st1 _ m5 AH5) ltac:(unfold ARELRO_LO; lia) ltac:(unfold ARELRO_HI; lia) ltac:(vm_compute; reflexivity)) as GOT5.
  pose proof (AHI_rtcells L RNG1 st1 _ m5 AH5) as (_ & _ & _ & REAL5 & _).
  pose proof AH5 as (_ & ARNG5 & _). destruct ARNG5 as (RIMG5 & _).
  assert (RSTK1 : rng RNG1 lo (bv_unsigned sp - lo)) by (eapply rng_fp_le; [exact LE1| exact RSTK]).
  assert (MINK : Z.of_nat k = Z.min n nold) by (subst k; lia).

  replace (Z_to_bv 64 A) with (Z_to_bv 64 (A - 16 + 16)) by (f_equal; lia).
  eapply implF_evtF.
  { eapply (ricptC_spec RNG1 _ sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ F fc m5 (A - 16) n nold UB b1 actx src (firstn k junk)).
    all: try lazymatch goal with
         | |- mem_inv _ _ => exact MI5
         | |- rw_cells _ _ _ _ => first [exact HD5 | exact GOT5 | exact REAL5 | (fold k; exact DST5)]
         | |- bytes_at _ _ _ _ => replace (A - 16 + 16) with A by lia; exact BSRC5
         | |- length _ = _ => exact LSRC
         | |- rng_aimg _ => exact RIMG5
         | |- rng _ _ _ => first [exact RH5
                                 | (replace (A - 16 + 16) with A by lia; eapply rng_sub; [eapply rng_fp_le; [exact LE1| exact RNGo]| lia| lia])
                                 | (eapply rng_sub; [exact RNGn| lia| lia])]
         end.
    all: unfold AREQMAX in *; try lia.
    all: match goal with |- ?G => idtac "REMC" G end. }
  cbv beta. intros ms6 (t0e & t1e & t2e & a6e & a7e & t3e & t4e & t5e & t6e & m6 & -> & MU6 & WM6 & MI6 & DST6 & BSRC6).

  assert (AH6 : AHEAP_I L RNG1 st1 (HB q UB n :: LB) m6).
  { eapply AHI_frame; [exact AH5| exact MU6| exact WM6|].
    constructor; [| constructor]. cbn [fst snd]. right. left. exists (HB q UB n). split; [left; reflexivity|]. cbn [ab_addr ab_size]. lia. }

  assert (CRS : forall A' n', bv_unsigned sp + -2208 <= A' -> A' + n' <= 2^47 -> aclient_range aci_I LB (bv_unsigned sp + -2208) A' n')
    by (intros A' n' H1 H2; left; left; split; assumption).
  eapply (aheap_pres_rw_cells _ _ _ _ _ _ _ PRES5) in FRR; [| apply CRS; cbn [cells_size csize Nat.add]; lia].
  eapply (aheap_pres_rw_cells _ _ _ _ _ _ _ PRES5) in FRa; [| apply CRS; cbn [cells_size csize Nat.add]; lia].
  eapply (aheap_pres_rw_cells _ _ _ _ _ _ _ PRES5) in FRp0; [| apply CRS; cbn [cells_size csize Nat.add]; lia].
  eapply (aheap_pres_rw_cells _ _ _ _ _ _ _ PRES5) in SS; [| apply CRS; cbn [cells_size csize Nat.add]; lia].
  eapply (aheap_pres_rw_cells _ _ _ _ _ _ _ PRES5) in FRS; [| apply CRS; cbn [cells_size csize Nat.add]; lia].
  eapply (aheap_pres_u64arr _ _ _ _ _ _ _ PRES5) in TB; [| apply CRS; rewrite ?LTB; lia].
  xport FRR MU6 WM6 ltac:(lia). xport FRa MU6 WM6 ltac:(lia). xport FRp0 MU6 WM6 ltac:(lia). xport SS MU6 WM6 ltac:(lia).
  xport FRS MU6 WM6 ltac:(lia). xport TB MU6 WM6 ltac:(rewrite LTB; lia). xport ST5 MU6 WM6 ltac:(lia).
  unfold aia_on in FL5. xport FL5 MU6 WM6 ltac:(unfold AIA_FLAG; lia).
  xport REST5 MU6 WM6 ltac:(lia).

  eapply implF_evtF with (P := fun ms' => ms' = _).
  { step. apply evtF_done. reflexivity. }
  cbv beta. intros ms6' ->.
  eapply implS_sbind.
  { eapply (AHI_dealloc L RNG1 _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ F fc m6 st1 (HB q UB n :: LB) p A nold lo
              (bv_unsigned sp + -2136) AREALLOC_PC tb trc).
    all: try lazymatch goal with
         | |- AHEAP_P _ _ _ _ _ _ => exact AH6
         | |- In (HB _ _ _) _ => exact HIN5
         | |- mem_inv _ _ => exact MI6
         | |- stk _ _ _ _ => rewrite USP; exact ST5
         | |- @eq word _ _ => first [reflexivity | exact TP | (f_equal; lia)]
         | |- rw_cells _ _ _ _ => first [exact SS | exact FL5]
         | |- u64arr _ _ _ _ => exact TB
         | |- In _ (al_U _) => exact TRU
         | |- map _ _ = _ => exact TRF
         | |- rng _ _ _ => rewrite ?USP; eapply rng_sub; [exact RSTK1| lia| lia]
         end.
    all: rewrite ?USP; rewrite ?unsigned_lit by lia; unfold AFREE_STACK in *; try lia; try assumption.
    all: match goal with |- ?G => idtac "REMD" G end. }

  intros st2 RNG2 ms7 (LE2 & t0f & t1f & t2f & a0f & a1f & a2f & a3f & a4f & a5f & a6f & a7f & t3f & t4f & t5f & t6f & m7 & -> & MI7 & ST7 & PRES7 & AH7).
  rewrite USP in ST7, PRES7.
  replace (ret_pc (Z_to_bv 64 254348)) with (Z_to_bv 64 254348) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  assert (QP : q <> p).
  { intros ->. pose proof (AHI_hb_ids L RNG1 st1 _ m5 AH5) as ND. cbn [hb_ids flat_map ab_kind app] in ND. inversion ND as [|x l NI _]; subst. apply NI.
    apply in_flat_map. exists (HB p A nold). split; [exact HIN| left; reflexivity]. }
  pose proof (AFreeRep.TwinB.lb_remove_cons_other p q UB n LB QP) as ELB.
  rewrite ELB in PRES7, AH7.
  assert (SUBR : forall b, In b (lb_remove p LB) -> In b LB) by (intros b Hb; apply AFreeRep.TwinB.In_lb_remove in Hb; tauto).

  assert (CRS7 : forall A' n', bv_unsigned sp + -2208 <= A' -> A' + n' <= 2^47 -> aclient_range aci_I (HB q UB n :: lb_remove p LB) (bv_unsigned sp + -2208) A' n')
    by (intros A' n' H1 H2; left; left; split; assumption).
  eapply (aheap_pres_rw_cells _ _ _ _ _ _ _ PRES7) in FRR; [| apply CRS7; cbn [cells_size csize Nat.add]; lia].
  eapply (aheap_pres_rw_cells _ _ _ _ _ _ _ PRES7) in FRa; [| apply CRS7; cbn [cells_size csize Nat.add]; lia].
  eapply (aheap_pres_rw_cells _ _ _ _ _ _ _ PRES7) in FRp0; [| apply CRS7; cbn [cells_size csize Nat.add]; lia].
  eapply (aheap_pres_rw_cells _ _ _ _ _ _ _ PRES7) in SS; [| apply CRS7; cbn [cells_size csize Nat.add]; lia].
  eapply (aheap_pres_rw_cells _ _ _ _ _ _ _ PRES7) in FRS; [| apply CRS7; cbn [cells_size csize Nat.add]; lia].
  eapply (aheap_pres_u64arr _ _ _ _ _ _ _ PRES7) in TB; [| apply CRS7; rewrite ?LTB; lia].
  pose proof (F_afree_icpt.TwinB.rw_cells_of_u64arr m7 _ tb TB) as TBC. rewrite LTB in TBC.
  replace (bv_unsigned sp + -2136 + 16) with (bv_unsigned sp + -2120) in TBC by lia.

  assert (NEW6 : rw_cells bsegs m6 UB [CB (Z.to_nat (Z.min n nold)) src; CB (Z.to_nat (n - Z.min n nold)) (skipn k junk)]).
  { change [CB (Z.to_nat (Z.min n nold)) src; CB (Z.to_nat (n - Z.min n nold)) (skipn k junk)]
      with ([CB (Z.to_nat (Z.min n nold)) src] ++ [CB (Z.to_nat (n - Z.min n nold)) (skipn k junk)]).
    apply rw_cells_app. split; [exact DST6|]. cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r.
    replace (Z.to_nat (n - Z.min n nold)) with (Z.to_nat n - k)%nat by (subst k; lia). exact REST5. }
  assert (NEW7 : rw_cells bsegs m7 UB [CB (Z.to_nat (Z.min n nold)) src; CB (Z.to_nat (n - Z.min n nold)) (skipn k junk)]).
  { eapply aheap_pres_rw_cells; [exact PRES7| exact NEW6|]. right. left. exists (HB q UB n). split; [left; reflexivity|].
    cbn [ab_addr ab_size cells_size csize Nat.add]. lia. }
  pose proof AH7 as (_ & ARNG7 & _). destruct ARNG7 as (RIMG7 & _).

  apply implS_ret.
  eapply evtF_mono.
  { eapply (ricptE_spec RNG2 _ sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ ra s0 s1 s2 s3 s4 s5 s6 sp _ _ _ _ _ F fc m7 lo UB junk2 junkR).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact ST7
         | |- mem_inv _ _ => exact MI7
         | |- rw_cells _ _ _ _ => first [exact FRR | exact FRa | exact FRS]
         | |- exists _, rw_cells _ _ _ _ /\ _ => first [eexists; split; [exact FRp0| reflexivity] | eexists; split; [exact SS| reflexivity] | eexists; split; [exact TBC| reflexivity]]
         | |- rng_aimg _ => exact RIMG7
         | |- rng _ _ _ => eapply rng_fp_le; [exact LE2| exact RSTK1]
         end.
    all: try lia.
    all: match goal with |- ?G => idtac "REME" G end. }
  cbv beta. intros ms8 (a0g & a1g & a2g & a3g & a4g & a5g & a6g & a7g & t0g & t1g & t2g & t3g & t4g & t5g & t6g & -> & _ & ST8).

  unfold arealloc_post_h, arealloc_post. cbn [snd fst]. split; [exact (fp_le_trans _ _ _ LE1 LE2)|].
  exists t0g, t1g, t2g, (Z_to_bv 64 UB), a1g, a2g, a3g, a4g, a5g, a6g, a7g, t3g, t4g, t5g, t6g, m7.
  split; [reflexivity|]. split; [exact MI7|]. split; [exact ST8|]. split.
  {
    eapply aheap_pres_trans; [eapply aheap_pres_weaken; [exact PRES3| lia| exact SUBR]|].
    eapply aheap_pres_trans; [eapply aheap_pres_weaken; [exact PRES5| lia| exact SUBR]|].
    eapply aheap_pres_trans; [eapply (pres_head_write L RNG1 st1 LB m5 m6 q UB n (Z.min n nold) (lb_remove p LB) (bv_unsigned sp)); [exact AH5| exact MU6| exact WM6| lia| exact BRn| exact SUBR| lia]|].
    eapply aheap_pres_weaken; [exact PRES7| lia| intros b Hb; right; exact Hb]. }
  cbn [snd fst].
  exists UB, src, (skipn k junk).
  split; [reflexivity|]. split; [exact BRn|]. split; [exact AH7|]. split; [exact BSRC0|]. split; [exact LSRC|]. split; [exact NEW7|].
  split; [eapply rng_fp_le; [exact LE2| exact RNGn]| eapply rng_fp_le; [exact LE2| exact RNGsn]].
Qed.
End CANSEC2.
End TwinB.
