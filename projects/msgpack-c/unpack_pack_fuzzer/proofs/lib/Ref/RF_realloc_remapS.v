(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SysCopy SFModel Arr ITree Nodes Decode.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import A_F_malloc_free A_F_malloc_fast A_F_malloc_enframe A_F_free A_F_free_spec A_MallocKit_AB A_MallocKit_A A_MallocBlocks A_MallocHINV A_MallocFacts_B A_Malloc_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import STree Malloc MallocCtrl MallocInv MI_Arith MI_Inv MI_Kit MI_Read MI_Geom MI_Pres2 MI_Cnt MI_WFree MI_WGroup MI_Realloc2 Realloc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import Monad Prog ProgR A_Realloc A_Realloc2 A_MallocFacts_Bpres A_MallocKit_A2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref Require Import RMallocRep RMallocTree RMallocKit_A RMallocKit_B RMallocKit_A2 RMalloc_iface RMalloc_ifaceP RF_free RF_free_spec RRealloc_iface RF_realloc_inpl RF_realloc_dec RF_mremap RF_realloc_rrep RF_realloc_inplS RF_realloc_moveS RMemEq RF_enframe.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require MI_WAMeta.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require A_MallocFacts_inv3 StrFun A_ASlot_M0.

Set Keyed Unification.
Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Definition remap_arm_stmt : Prop :=
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m1 : mem)
    (s : PState) (LB LB0 : list block) (p : bptr) (A old n lo B : Z) (errv : word) (oldbs : list byte)
    (st : mstate) (g bg : aptr) (idx : Z) (r : region) (off : Z),
  let c : cptr := fst p in
  let mr := get_meta_rec st g in
  let stride := get_stride mr in
  let Bg := conc st bg in
  let E := Bg + 16 + stride * (idx + 1) - 4 in
  let sp1 := bv_unsigned sp - 64 in
  let POST := rrealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p A old n lo B oldbs m in
  rmalloc_impl_stmt -> rfree_impl_stmt ->
  Permutation LB0 LB -> strip st = ps_m s -> rmrep st m1 -> brk_link st (ps_brk s) ->
  AREACH_from ref_reserved st LB0 -> In (p, A, old) LB0 ->
  s_slots st !! c = Some (g, idx) -> m_mem mr = Some bg -> s_regions st !! (fst bg) = Some r -> r_kind r = RKGroup ->
  fst c = fst bg -> c = (fst bg, snd bg + UNIT + stride * idx) -> Bg = r_base r + snd bg ->
  A = conc st c + UNIT * off -> 0 <= off <= 255 -> UNIT * off + old <= stride - IB -> 0 <= old ->
  UNIT <= stride -> stride mod UNIT = 0 -> 0 <= snd bg -> snd bg mod UNIT = 0 -> 0 <= idx <= m_last_idx mr -> m_last_idx mr <= 31 ->
  snd bg + UNIT + stride * (idx + 1) <= round_up_pg (r_len r) -> r_base r + round_up_pg (r_len r) <= alloc_ceiling -> 0 <= r_base r ->
  (m_sizeclass mr < 48 -> stride < 2 ^ 20) -> (48 <= m_sizeclass mr -> m_sizeclass mr = 63) ->
  known st (fst c, snd c + UNIT * off - 3) (idx + 32 * Z.min (snd c + stride - IB - (snd c + UNIT * off) - old) 5) ->
  rw_cells rsegs m1 sp1 [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m1 lo sp1 -> mem_inv rsegs m1 -> rw_cells rsegs m1 (errno_addr tp) [C4 errv] ->
  rauxv_ok m1 B -> rpres_except (fun a => (lo <= a < bv_unsigned sp) \/ (RERRNO <= a < RERRNO + 4)) m m1 ->
  bytes_at rsegs m A oldbs -> Z.of_nat (length oldbs) = old ->
  bv_unsigned sp <= B -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RREALLOC_STACK ->
  tp = Z_to_bv 64 RATP -> 0 <= n < 2^48 -> True ->
  forall (y7 a5v y28 : word),
  MMAP_THRESHOLD <= n -> m_sizeclass mr = 63 ->
  implM rsegs (realloc_body p A n (ps_m s)) s POST
      (MS (mkR ra (Z_to_bv 64 sp1) gp tp (Z_to_bv 64 E) (Z_to_bv 64 (Bg + stride * idx + 16)) y7 s0 (wz (conc st g)) (Z_to_bv 64 A) (Z_to_bv 64 n)
               (wz Bg) (Z_to_bv 64 (m_sizeclass mr)) (wz (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)) a5v
               (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - A)) (Z_to_bv 64 (A + old)) s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 t4 t5 t6)
          F (Z_to_bv 64 0x49cb0) fc None m1 (seg_rom rsegs)).

Lemma implM_of_enode {A} (n0 : node) (dec : resp -> option A) (s : PState) (Q : A -> PState -> machine_state -> Prop) ms :
  impl rsegs (at_node rsegs) (enode n0 dec) (epost (fun a ms' => Q a s ms')) ms -> implM rsegs (msys n0 dec) s Q ms.
Proof.
  intros H. unfold implM, msys, enode in *. cbn [impl] in *. eapply evt_mono; [exact H|].
  intros ms1 [AT K]. split; [exact AT|]. intros rsp. specialize (K rsp). destruct (dec rsp) as [a|]; cbn in *; exact K.
Qed.

Lemma rptrs_remap st LB (m : mem) rid r (g bg : aptr) ai :
  CINV st LB -> rmrep st m ->
  (s_regions st) !! rid = Some r -> r_kind r = RKGroup ->
  (s_groups st) !! bg = Some (mkGhdr (Some g) ai) ->
  (forall b gh, (s_groups st) !! b = Some gh -> fst b = rid -> b = bg) ->
  let P := fun q : N => q <> rid in
  optr_in P (c_free_meta_head (ctx st)) /\ optr_in P (c_avail_meta (ctx st)) /\ optr_in P (c_meta_area_head (ctx st))
  /\ optr_in P (c_meta_area_tail (ctx st)) /\ optr_in P (c_avail_meta_areas (ctx st))
  /\ (forall sc, optr_in P (active st sc))
  /\ match c_brk (ctx st) with BrkLive q _ => P q | _ => True end
  /\ (forall g', optr_in P (m_prev (get_meta_rec st g')) /\ optr_in P (m_next (get_meta_rec st g')) /\ (g' <> g -> optr_in P (m_mem (get_meta_rec st g'))))
  /\ (forall a ar, (s_areas st) !! a = Some ar -> P (fst a) /\ optr_in P (a_next ar))
  /\ (forall b gh, (s_groups st) !! b = Some gh -> optr_in P (g_meta gh)).
Proof.
  intros C MR Hr Kr Hg ONLYG P. pose proof (KINV_of_CINV _ _ C) as K. destruct (ci_mp _ _ C) as (M1 & M2 & M3 & M4 & M5).
  pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
  assert (MSr : forall q, meta_slot st q -> fst q <> rid).
  { intros q (a & ar & k & Ha & Hk & ->) E. cbn in E. destruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _).
    rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr). }
  assert (NGr : forall p, ng_ptr st p -> optr_in P p).
  { intros [q|]; cbn; [| exact (fun _ => I)]. intros (r' & Hr' & NK) E. rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. exact (NK Kr). }
  assert (OM : forall p, (forall q, p = Some q -> meta_slot st q) -> optr_in P p).
  { intros [q|] H; cbn; [apply MSr; apply H; reflexivity| exact I]. }
  pose proof (ki_links _ _ _ K) as [LN LP LNN LS].
  split; [apply OM; intros h Hh; exact (proj1 (kinv_free_head st LB 0 h K Hh))|].
  split; [apply NGr; exact M1|]. split; [apply NGr; exact M2|]. split; [apply NGr; exact M3|]. split; [apply NGr; exact M4|].
  split; [intros sc; apply OM; intros a Ha; exact (proj1 (proj2 (kinv_active st LB 0 sc a K Ha)))|].
  split.
  { destruct (c_brk (ctx st)) as [| |brid boff] eqn:HB; try exact I.
    intros E. destruct (ki_bk _ _ _ K brid boff HB) as (r' & Hr' & K'). rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. rewrite Kr in K'. discriminate. }
  split.
  { intros g'. split; [apply OM; intros pv Hp; exact (proj2 (LP g' pv Hp))|]. split; [apply OM; intros nx Hn; exact (proj2 (LN g' nx Hn))|].
    intros NE. destruct (m_mem (get_meta_rec st g')) as [b|] eqn:MB; cbn; [| exact I]. intros E.
    pose proof (ci_memh _ _ C g' b MB) as [ai' Hb']. pose proof (ONLYG b _ Hb' E) as ->. rewrite Hg in Hb'. apply NE. congruence. }
  split.
  { intros a ar Ha. split; [| apply NGr; exact (M5 a ar Ha)].
    intros E. destruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _). rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr). }
  intros b gh Hb. destruct (ki_grps _ _ _ K b gh Hb) as (g' & Hg' & _). rewrite Hg'. cbn. apply MSr.
  assert (HB : A_MallocFacts_B.hosts st b g') by (exists (g_active_idx gh); rewrite Hb; destruct gh; cbn in Hg' |- *; subst; reflexivity).
  exact (go_slot _ _ _ (ki_gmetas _ _ _ K b g' HB)).
Qed.

Lemma ticks_ok_trim_shadow st rid k : ticks_ok st -> ticks_ok (trim_shadow rid k st).
Proof.
  intros [T1 T2]. unfold trim_shadow, upd_shadow. split; cbn [s_shadow s_tick set_shadow].
  - intros q sh u hl ch Hs Hu Hin. destruct (N.eq_dec q rid) as [->|NE].
    + rewrite lookup_insert_eq in Hs. injection Hs as <-. cbn in Hu.
      unfold get_shadow in Hu. destruct (s_shadow st !! rid) as [sh0|] eqn:E; cbn in Hu; [eapply T1; eauto| rewrite lookup_empty in Hu; discriminate].
    + rewrite lookup_insert_ne in Hs by congruence. eapply T1; eauto.
  - intros q sh pg t Hs Hp. destruct (N.eq_dec q rid) as [->|NE].
    + rewrite lookup_insert_eq in Hs. injection Hs as <-. cbn in Hp.
      unfold get_shadow in Hp. destruct (s_shadow st !! rid) as [sh0|] eqn:E; cbn in Hp; [eapply T2; eauto| rewrite lookup_empty in Hp; discriminate].
    + rewrite lookup_insert_ne in Hs by congruence. eapply T2; eauto.
Qed.

Lemma rinplace_pres (mx : mem) (P E n b3 lo hi : Z) :
  lo <= P - 3 -> P + n <= E -> E + 1 <= hi -> 0 <= lo -> hi <= 2^64 -> 0 <= n -> 3 <= P ->
  rpres_except (fun x => x = P - 3 \/ P + n <= x < hi) mx (rinplace_mem (write_to_mem mx (wa E) [b8 0]) P E n b3).
Proof.
  intros H1 H2 H3 H4 H5 H6 H7. unfold rinplace_mem. cbv zeta.
  assert (L4 : forall w, length (le4 w) = 4%nat) by (intros; reflexivity).
  set (rr := E - P - n) in *.
  assert (P30 : rpres_except (fun x => x = P - 3 \/ P + n <= x < hi) mx (write_to_mem mx (wa E) [b8 0])).
  { apply rpres_write; [apply rpres_except_refl| lia| cbn; lia| cbn; intros; right; lia]. }
  set (mw := write_to_mem mx (wa E) [b8 0]) in *. clearbody mw.
  set (m3' := if rr =? 0 then _ else _).
  assert (P3 : rpres_except (fun x => x = P - 3 \/ P + n <= x < hi) mx m3').
  { subst m3'. destruct (Z.eqb_spec rr 0); [exact P30|]. apply rpres_write; [exact P30| lia| cbn; lia| cbn; intros; right; lia]. }
  clearbody m3'.
  set (m4 := if 5 <=? rr then _ else _).
  assert (P4 : rpres_except (fun x => x = P - 3 \/ P + n <= x < hi) mx (fst m4) /\ 0 <= snd m4 <= 5).
  { subst m4. destruct (Z.leb_spec 5 rr); cbn [fst snd].
    - split; [| lia]. apply rpres_write; [| lia| rewrite L4; lia| rewrite L4; intros; right; lia].
      apply rpres_write; [exact P3| lia| cbn; lia| cbn; intros; right; lia].
    - split; [exact P3| lia]. }
  clearbody m4. destruct m4 as [m4 r5]. cbn [fst snd] in P4 |- *. destruct P4 as [P4 _].
  apply rpres_write; [exact P4| lia| cbn; lia| cbn; intros; left; lia].
Qed.

Lemma rreserved_free_intro b n : 0 <= b -> (b + n <= 0x10000 \/ 0x88000 <= b) -> ranges_free ref_reserved b n = true.
Proof.
  intros Hb H. unfold ref_reserved. apply ranges_free_intro. intros b' k Hin.
  cbn in Hin. destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-; lia.
Qed.

Lemma ranges_free_app_l l1 l2 a n : ranges_free (l1 ++ l2) a n = true -> ranges_free l1 a n = true.
Proof. intros H. apply ranges_free_intro. intros b k Hin. eapply ranges_free_In; [exact H|]. apply in_or_app. left. exact Hin. Qed.

Lemma In_live_ranges_except cs rid q rq : (s_regions cs) !! q = Some rq -> q <> rid -> In (region_live_range rq) (live_ranges_except cs rid).
Proof.
  intros Hq NE. unfold live_ranges_except. apply in_or_app. right. apply in_map_iff. exists (q, rq). split; [reflexivity|].
  apply (proj1 (list_elem_of_In _ _)). apply (proj2 (list_elem_of_filter _ _ _)).
  split; [cbn; destruct (N.eqb_spec q rid); [congruence| exact I]| apply elem_of_map_to_list; exact Hq].
Qed.

Lemma wr_at_app m a n1 n2 : wr_at rsegs m a n1 -> wr_at rsegs m (a + n1) n2 -> 0 <= n1 -> 0 <= n2 -> wr_at rsegs m a (n1 + n2).
Proof.
  intros (A0 & A1 & W1) (B0 & B1 & W2) H1 H2. split; [exact A0|]. split; [lia|]. intros i Hi.
  destruct (Z.lt_ge_cases i n1) as [LT|GE]; [apply W1; lia|]. replace (a + i) with (a + n1 + (i - n1)) by lia. apply W2. lia.
Qed.

Definition rtail_post (sp gp tp s7 s8 s9 s10 s11 t4 t5 t6 rav s0v s1v s2v s3v s4v s5v s6v gw w0 w1 w2 : word) (w3 w4 : word)
   (F : bvmap 5 word) (fc : bv 32) (m : mem) (G NB needed n off b3 : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 m2 m',
    ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + 64)) gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 (NB + 16 + 16 * off)) a1 a2 a3 a4 a5 a6 a7
                  s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc rav) fc None m' (seg_rom rsegs)
    /\ m' = rinplace_mem (write_to_mem m2 (wa (NB + needed - 4)) [b8 0]) (NB + 16 + 16 * off) (NB + needed - 4) n b3
    /\ munch [(G + 16, G + 24); (G + 32, G + 40)] m m2 /\ wmono rsegs m m2
    /\ mem_inv rsegs m'
    /\ rw_cells rsegs m2 (bv_unsigned gw) [C8 w0; C8 w1; C8 (wz NB); C4 w3; C4 w4; C8 (wz (4064 + needed))]
    /\ rw_cells rsegs m' (bv_unsigned sp) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].

Section TAIL_W.
Variables (ra1 sp gp tp s7 s8 s9 s10 s11 t4 t5 t6 rav s0v s1v s2v s3v s4v s5v s6v gw w0 w1 w2 : word) (w3 w4 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (G NB needed n off mword b3 : Z).
Hypotheses (HGW : bv_unsigned gw = G) (G0 : 0 <= G) (NB0 : 0 < NB) (HN : 0 <= n) (Hoff : 0 <= off) (B3R : 0 <= b3 < 256)
    (NDR : n + 16 * off + 20 <= needed < n + 16 * off + 20 + 4096) (NDA : needed mod 4096 = 0) (ND62 : needed < 2^62)
    (MWM : mword mod 4096 = 4064) (MW64 : 0 <= mword < 2^64)
    (GFR : G + 40 <= NB \/ NB + needed <= G) (GSP : G + 40 <= bv_unsigned sp) (NSP : NB + needed <= bv_unsigned sp) (SPH : bv_unsigned sp + 64 <= 2^64)
    (MM : rw_cells rsegs m (bv_unsigned gw) [C8 w0; C8 w1; C8 w2; C4 w3; C4 w4; C8 (wz mword)])
    (WRN : wr_at rsegs m NB needed) (BK : bytes_at rsegs m (NB + 13 + 16 * off) [b8 b3])
    (FR : rw_cells rsegs m (bv_unsigned sp) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav])
    (MI : mem_inv rsegs m).
Let POST := rtail_post sp gp tp s7 s8 s9 s10 s11 t4 t5 t6 rav s0v s1v s2v s3v s4v s5v s6v gw w0 w1 w2 w3 w4 F fc m G NB needed n off b3.

Lemma tail_6c0 : forall (t0v t1v t2v a0v a3v a4v a5v a6v a7v s2 s5 s6 t3v : word),
  evt rsegs POST
      (MS (mkR ra1 sp gp tp t0v t1v t2v (Z_to_bv 64 needed) gw a0v (Z_to_bv 64 n) (Z_to_bv 64 NB)
               a3v a4v a5v a6v a7v s2 (Z_to_bv 64 (16 * off)) (Z_to_bv 64 4095) s5 s6 s7 s8 s9 s10 s11 t3v t4 t5 t6)
          F (Z_to_bv 64 0x49d00) fc None m (seg_rom rsegs)).
Proof.
  intros.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  set (P' := NB + 16 + 16 * off). set (E' := NB + needed - 4).
  assert (EP' : P' = NB + 16 + 16 * off) by reflexivity. assert (EE' : E' = NB + needed - 4) by reflexivity. clearbody P' E'.
  replace (NB + 13 + 16 * off) with (P' - 3) in BK by lia.
  pose proof (munch_refl [(G + 16, G + 24); (G + 32, G + 40)] m) as MU. pose proof (wmono_refl rsegs m) as WM.

  step. step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. cbn in K0. lia. } clear K0.

  step. step. rewrite ?(unsigned_lit NB), ?(unsigned_lit (16 * off)) by lia.
  step. rewrite ?(unsigned_lit needed) by lia.
  step. step. step. step. rewrite ?(unsigned_lit n), ?(unsigned_lit (NB + 16 * off + 16)) by lia.
  step. step.

  rewrite (wz_unsigned mword) by exact MW64.
  replace (Z.land mword 4095) with 4064 by (change 4095 with (Z.ones 12); rewrite Z.land_ones by lia; change (2 ^ 12) with 4096; symmetry; exact MWM).
  rewrite (unsigned_lit 4064) by lia. rewrite (unsigned_lit needed) by lia.
  rewrite (StrFun.lor_add' 4064 needed 12) by (change (2^12) with 4096; first [exact NDA| lia]).
  replace (NB + 16 * off + 16) with P' by lia. replace (n + P') with (P' + n) by lia.
  rewrite (unsigned_lit (NB + needed + -4)), (unsigned_lit (P' + n)) by lia.
  rewrite (swrap32_small (NB + needed + -4 - (P' + n))) by lia.
  replace (NB + needed + -4 - (P' + n)) with (E' - P' - n) by lia.
  replace (NB + needed + -4) with E' by lia. replace (NB + needed) with (E' + 4) by lia.

  step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    rename MU into MU2; unfold munch in MU2; assert (WM2 : id (wmono rsegs m mx)) by exact WM;
    lazymatch goal with H : rw_cells rsegs mx (bv_unsigned gw) ?cs |- _ => assert (MM2 : id (rw_cells rsegs mx (bv_unsigned gw) cs)) by exact H end;
    pose proof (wr_at_store_ok rsegs mx NB needed (needed - 4) 1%nat WRN ltac:(lia) ltac:(lia)) as SO;
    replace (NB + (needed - 4)) with (E' + 4 + -4) in SO by lia; change (wa (E' + 4 + -4)) with (Z_to_bv 64 (E' + 4 + -4)) in SO end.

  step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
  replace (E' + 4 + -4) with E' in * by lia.
  eapply evt_mono.
  { lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      apply (inpl_6f8 ra1 sp gp tp s7 s8 s9 s10 s11 t4 t5 t6 rav s0v s1v s2v s3v s4v s5v s6v F fc mx P' n E' b3) end;
      try eassumption; try lia.
    lazymatch goal with W : wr_at rsegs ?mx NB needed |- wr_at rsegs ?mx _ _ => eapply wr_at_sub; [exact W| lia| lia] end. }
  intros ms' (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & m' & -> & EM & MI' & FR').
  unfold POST, rtail_post. do 11 eexists.
  lazymatch goal with E3 : ?m3 = write_to_mem ?m2 _ _ |- _ => exists m2, m'; rewrite E3 in EM end.
  split; [rewrite EP'; reflexivity|]. split; [rewrite <- EE', <- EP'; exact EM|].
  split; [exact MU2|]. split; [exact WM2|]. split; [exact MI'|]. split; [| exact FR'].
  exact MM2.
Qed.
End TAIL_W.

Section TAIL.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m1 mm : mem)
    (s : PState) (LB LB0 : list block) (p : bptr) (A old n lo B : Z) (errv errv2 : word) (oldbs : list byte)
    (st : mstate) (g bg : aptr) (idx : Z) (r : region) (off : Z) (NB : Z).
Let c : cptr := fst p.
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let Bg := conc st bg.
Let E := Bg + 16 + stride * (idx + 1) - 4.
Let sp1 := bv_unsigned sp - 64.
Let OL := m_maplen mr * 4096.
Let needed := remap_needed (UNIT * off) n.
Let kt := Z.min OL needed.
Let mword := m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr.
Let POST := rrealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p A old n lo B oldbs m.
Hypotheses (PERM : Permutation LB0 LB) (Hst : strip st = ps_m s) (RMR : rmrep st m1) (HBL : brk_link st (ps_brk s))
    (AR : AREACH_from ref_reserved st LB0) (Hin0 : In (p, A, old) LB0)
    (SL : s_slots st !! c = Some (g, idx)) (HM : m_mem mr = Some bg) (Hr : s_regions st !! (fst bg) = Some r) (Kr : r_kind r = RKGroup)
    (FC : fst c = fst bg) (Ec : c = (fst bg, snd bg + UNIT + stride * idx)) (CB : Bg = r_base r + snd bg)
    (HA : A = conc st c + UNIT * off) (Hoff : 0 <= off <= 255) (FIT : UNIT * off + old <= stride - IB) (HO : 0 <= old)
    (S16 : UNIT <= stride) (SMOD : stride mod UNIT = 0) (B0 : 0 <= snd bg) (BG16 : snd bg mod UNIT = 0) (Hidx : 0 <= idx <= m_last_idx mr) (LI : m_last_idx mr <= 31)
    (SPAN : snd bg + UNIT + stride * (idx + 1) <= round_up_pg (r_len r)) (RCEIL : r_base r + round_up_pg (r_len r) <= alloc_ceiling) (RB0 : 0 <= r_base r)
    (SC63 : 48 <= m_sizeclass mr -> m_sizeclass mr = 63)
    (K3 : known st (fst c, snd c + UNIT * off - 3) (idx + 32 * Z.min (snd c + stride - IB - (snd c + UNIT * off) - old) 5)).
Hypotheses (FR : rw_cells rsegs mm sp1 [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    (ST1 : stk rsegs mm lo sp1) (MI1 : mem_inv rsegs mm) (ERR1 : rw_cells rsegs mm (errno_addr tp) [C4 errv2])
    (AUX1 : rauxv_ok mm B)
    (PRES1 : rpres_except (fun a => (lo <= a < bv_unsigned sp) \/ (RERRNO <= a < RERRNO + 4)) m m1)
    (OLDB : bytes_at rsegs m A oldbs) (OLEN : Z.of_nat (length oldbs) = old)
    (SB : bv_unsigned sp <= B) (CLO : alloc_ceiling <= lo) (LO : lo <= bv_unsigned sp - RREALLOC_STACK)
    (TP : tp = Z_to_bv 64 RATP) (HN : 0 <= n < 2^48) (THR : MMAP_THRESHOLD <= n) (SC : m_sizeclass mr = 63)
    (RC : realloc_case (strip st) c A n = RcRemap (fst c) g Bg OL needed).

Hypotheses (NB0 : 0 < NB) (NBA : NB mod 4096 = 0) (NCEIL : NB + needed <= alloc_ceiling) (RFR : ranges_free ref_reserved NB needed = true)
    (DISJ : forall rid2 r2, s_regions st !! rid2 = Some r2 -> rid2 <> fst bg -> let '(b2, l2) := region_live_range r2 in NB + needed <= b2 \/ b2 + l2 <= NB)
    (COPY : forall i, 0 <= i < kt -> mm (wa (NB + i)) = m1 (wa (Bg + i)))
    (ZERO : forall i, kt <= i < needed -> mm (wa (NB + i)) = Some (b8 0))
    (WRN : wr_at rsegs mm NB needed)
    (AGM : forall x, 0 <= x < 2^64 -> ~ (Bg <= x < Bg + OL) -> ~ (NB <= x < NB + needed) -> ~ (lo <= x < sp1) -> mm (wa x) = m1 (wa x))
    (WMM : forall x, 0 <= x < 2^64 -> ~ (Bg <= x < Bg + OL) -> ~ (NB <= x < NB + needed) -> wview rsegs m1 (wa x) <> None -> wview rsegs mm (wa x) <> None).

Lemma remap_tail : forall (rax t0v t1v t2v a3v a4v a5v a6v a7v s5v s6v t3v t4v t5v t6v : word),
  evt rsegs (POST (Some p) (set_m (remap_update (ps_m s) (fst c) g NB needed) s))
      (MS (mkR rax (Z_to_bv 64 sp1) gp tp t0v t1v t2v (Z_to_bv 64 needed) (wz (conc st g)) (Z_to_bv 64 A) (Z_to_bv 64 n) (Z_to_bv 64 NB)
               a3v a4v a5v a6v a7v (Z_to_bv 64 (A + old)) (Z_to_bv 64 (16 * off)) (Z_to_bv 64 4095) s5v s6v s7 s8 s9 s10 s11 t3v t4v t5v t6v)
          F (Z_to_bv 64 0x49d00) fc None mm (seg_rom rsegs)).
Proof.
  intros.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold RREALLOC_STACK, RMALLOC_STACK in LO. pose proof CLO as CLOv. pose_ceil. pose proof NCEIL as NCEILv. pose_ceil.
  assert (ETP : bv_unsigned tp + -164 = 422892) by (rewrite TP; unfold RATP; rewrite unsigned_lit by lia; reflexivity).

  destruct (realloc_bf ref_reserved st LB0 p A old AR Hin0 g bg idx SL HM) as (L & LS & BL & off' & ai & a & ar & ka & INV & CR & Hk & HA' & BF).
  change (fst p) with c in HA'. assert (off' = off) as -> by (rewrite HA in HA'; unfold UNIT in HA'; clear - HA'; lia). clear HA'.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as HgB. fold c in HgB.
  pose proof (ig_ok _ _ _ IG _ _ _ HgB) as GO.
  destruct (realloc_region_private ref_reserved st LB0 p A old AR Hin0 g bg idx SL HM SC r Hr) as (RPRIV & ONLYG & SB0 & I0 & L0 & EOL & _).
  change (MR st g) with mr in L0, EOL. fold OL in EOL.
  assert (Ebg : bg = (fst bg, 0)) by (destruct bg; cbn in SB0 |- *; subst; reflexivity).
  assert (HgB0 : s_groups st !! (fst bg, 0) = Some (mkGhdr (Some g) ai)) by (rewrite <- Ebg; exact HgB).
  assert (ONLYG0 : forall b gh, s_groups st !! b = Some gh -> fst b = fst bg -> b = (fst bg, 0)) by (intros b gh Hb Hf; rewrite <- Ebg; exact (ONLYG b gh Hb Hf)).
  assert (HM0 : m_mem mr = Some (fst bg, 0)) by (rewrite HM, <- Ebg; reflexivity).
  pose proof (g_maplen _ _ _ _ _ _ GO) as ML0. change (MR st g) with mr in ML0.
  destruct (g_sc _ _ _ _ _ _ GO) as [[S48 _]|(_ & _ & ML & _)]; [exfalso; change (MR st g) with mr in S48; clear - S48 SC; lia|]. change (MR st g) with mr in ML.
  assert (STR : stride = OL - 16).
  { subst stride OL. unfold get_stride. rewrite L0. cbn [Z.eqb andb]. destruct (Z.eqb_spec (m_maplen mr) 0); [exfalso; exact (ML ltac:(eassumption))| reflexivity]. }
  assert (OL4096 : 4096 <= OL) by (subst OL; clear - ML ML0; lia).
  assert (EBg : Bg = r_base r) by (subst Bg; rewrite CB, SB0; clear; lia).
  assert (Sc16 : snd c = 16) by (rewrite Ec; cbn [snd]; rewrite SB0, I0; unfold UNIT; clear; lia).
  assert (Ec16 : c = (fst bg, 16)) by (rewrite Ec at 1; cbn; f_equal; rewrite SB0, I0; unfold UNIT; clear; lia).
  assert (CC : conc st c = Bg + 16).
  { rewrite (conc_region' st c r) by (rewrite FC; exact Hr). rewrite Sc16, EBg. reflexivity. }
  assert (HAE : A = Bg + 16 + 16 * off) by (rewrite HA, CC; unfold UNIT; clear; lia).
  assert (HE : E = Bg + OL - 4) by (subst E; rewrite I0, STR; clear; lia).
  pose proof (remap_needed_ge (UNIT * off) n ltac:(clear - HN; lia) ltac:(unfold UNIT; clear - Hoff; lia)) as NDR. fold needed in NDR. unfold UNIT, IB in NDR.
  pose proof (remap_needed_pg (UNIT * off) n) as NDA. fold needed in NDA.
  assert (ND62 : needed < 2 ^ 62) by (clear - NDR HN Hoff; lia).
  assert (ND4096 : 4096 <= needed) by (clear - NDR NDA HN Hoff; Z.div_mod_to_equations; lia).
  assert (NDround : round_up_pg needed = needed) by (apply MI_WAMeta.round_up_pg_id; exact NDA).
  assert (KT : 4096 <= kt <= needed /\ kt <= OL) by (subst kt; clear - ND4096 OL4096; lia).
  pose proof RMR as (WF & CX & GL & ARS & GR & SH). pose proof WF as (Hres & WR & DISJr & WA & WG).
  destruct (WR _ _ Hr) as (RrB0 & RBAL & RL0 & RBC & RF). pose_ceil.
  pose proof (round_up_pg_ge (r_len r)) as RUP. rewrite <- EOL in RUP, RBC, RF.
  pose proof (rreserved_disjoint1 _ _ RF ltac:(clear - OL4096; lia)) as DRr. rewrite <- EBg in DRr, RBC, RrB0.
  pose proof (rreserved_disjoint1 _ _ RFR ltac:(clear - ND4096; lia)) as DRn.
  pose proof (g_freeable _ _ _ _ _ _ GO) as FB1. change (MR st g) with mr in FB1.
  assert (EMW : mword = 4064 + OL) by (subst mword OL; rewrite L0, FB1, SC; clear; lia).
  assert (MW64 : 0 <= mword < 2^64) by (rewrite EMW; clear - OL4096 RBC RrB0; lia).
  assert (MWM : mword mod 4096 = 4064).
  { rewrite EMW. subst OL. clear. rewrite Z.mod_add by lia. reflexivity. }
  pose proof (A_MallocFacts_inv3.areach_cinv_proof _ _ AR) as CINV0.
  assert (MSL : meta_slot st g).
  { destruct (bf_area _ _ _ _ _ _ _ _ _ _ _ BF) as (Ha & _ & _ & Hka & Emm). exists a, ar, ka. split; [exact Ha|]. split; [exact Hka| exact Emm]. }
  destruct (rarea_conc st _ _ WF (proj1 (bf_area _ _ _ _ _ _ _ _ _ _ _ BF))) as (rga & Hrga & Cga & Sga0 & Sga1 & SgaL & NKg & RgB0 & RgAL & RgC). pose_ceil.
  assert (HG : conc st g = conc st a + (24 + 40 * ka)).
  { destruct (bf_area _ _ _ _ _ _ _ _ _ _ _ BF) as (Ha & _ & _ & Hka & Emm). rewrite Emm. unfold mslot, AREA_HDR, META_SIZE. apply conc_aadd. rewrite Hrga. eauto. }
  pose proof (proj1 (proj2 (proj2 (proj2 (bf_area _ _ _ _ _ _ _ _ _ _ _ BF))))) as Hka.
  set (G := conc st g) in *.

  assert (DJ' : forall q rq, (s_regions st) !! q = Some rq -> q <> fst bg -> NB + needed <= lr_lo rq \/ r_base rq + round_up_pg (r_len rq) <= NB).
  { intros q rq Hq NE. specialize (DISJ q rq Hq NE). unfold region_live_range in DISJ. unfold lr_lo. destruct (r_kind rq); unfold PGSZ in DISJ; clear - DISJ; lia. }

  assert (NEra : fst a <> fst bg) by (intros E0; rewrite E0, Hr in Hrga; assert (rga = r) by congruence; subst rga; exact (NKg Kr)).
  assert (GFAR : (G + 40 <= Bg \/ Bg + OL <= G) /\ (G + 40 <= NB \/ NB + needed <= G) /\ G + 40 <= alloc_ceiling /\ (0x88000 <= G \/ G + 40 <= 0x10000)).
  { pose proof (DISJr _ _ _ _ Hrga Hr NEra) as D1. pose proof (DJ' _ _ Hrga NEra) as D2.
    pose proof (rarea_lr_lo st _ _ rga WF (proj1 (bf_area _ _ _ _ _ _ _ _ _ _ _ BF)) Hrga) as LRa. pose proof (lr_lo_group r Kr) as LRr.
    destruct (WR _ _ Hrga) as (_ & _ & _ & _ & RFa). pose proof (rreserved_disjoint1 _ _ RFa ltac:(clear - Sga0 Sga1; lia)) as DRa.
    unfold NSLOTS in Hka. rewrite <- EOL, LRr, <- EBg in D1. pose_ceil. clear - D1 D2 LRa Cga Sga0 Sga1 HG Hka RgC DRa. lia. }
  destruct GFAR as (GF1 & GF2 & GF3 & GF4). pose_ceil.
  assert (GR64 : 0 <= G < 2^64) by (clear - GF3 Cga RgB0 HG Hka Sga0; unfold NSLOTS in Hka; lia).

  assert (PEM : rpres_except (fun x => (Bg <= x < Bg + OL) \/ (NB <= x < NB + needed) \/ (lo <= x < sp1)) m1 mm).
  { intros x Hx NC. split; [apply AGM; clear - Hx NC; try lia; tauto| apply WMM; clear - Hx NC; try lia; tauto]. }
  pose proof (rmrep_meta_chunk st m1 g RMR MSL) as MM0. change (get_meta_rec st g) with mr in MM0. fold G in MM0.
  assert (MM : rw_cells rsegs mm G (meta_cells st mr)).
  { eapply rpres_except_rw_cells; [exact PEM| exact MM0|]. unfold meta_cells. cbn [cells_size csize Nat.add Z.of_nat]. intros x Hx [X|[X|X]]; subst sp1; clear - Hx X GF1 GF2 GF3 CLOv LO SPR; lia. }
  unfold meta_cells in MM. rewrite HM in MM. change (pw st (Some bg)) with (wz (conc st bg)) in MM. fold Bg in MM.
  change (meta_word mr) with mword in MM.

  destruct (SH _ _ Hr Kr) as [WRr RDr].
  destruct (RDr (snd c + UNIT * off - 3) _ ltac:(rewrite Sc16, <- EOL; unfold UNIT; clear - Hoff OL4096 NDR KT; lia) ltac:(rewrite <- FC; exact K3)) as [BK0 B3R].
  set (b3 := idx + 32 * Z.min (snd c + stride - IB - (snd c + UNIT * off) - old) 5) in *.
  assert (B3K : Z.land b3 31 = 0).
  { subst b3. rewrite I0. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. change (2^5) with 32.
    lazymatch goal with |- context [Z.min ?u 5] => destruct (Z.min_spec u 5) as [[X1 X2]|[X1 X2]]; rewrite X2 end;
      clear - FIT Hoff HO X1; Z.div_mod_to_equations; lia. }
  set (P' := NB + 16 + 16 * off). set (E' := NB + needed - 4).
  assert (EP' : P' = NB + 16 + 16 * off) by reflexivity. assert (EE' : E' = NB + needed - 4) by reflexivity. clearbody P' E'.
  assert (BK : bytes_at rsegs mm (NB + 13 + 16 * off) [b8 b3]).
  { destruct BK0 as (_ & _ & HB). split; [clear - NB0 Hoff; lia|]. split; [cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - NCEILv Hoff NDR HN; lia|].
    intros i Hi. destruct i; [| cbn in Hi; lia]. specialize (HB 0%nat Hi). cbn [nth_error] in HB |- *. rewrite Z.add_0_r in HB |- *.
    rewrite ref_mrd_overlay in HB |- * by (rewrite wa_unsigned; rewrite ?Sc16; unfold UNIT; clear - NB0 NCEILv Hoff NDR DRn DRr RrB0 RBC EBg OL4096 KT HN FIT HO STR; lia).
    rewrite <- HB. replace (NB + 13 + 16 * off) with (NB + (13 + 16 * off)) by (clear; lia).
    rewrite Sc16, <- EBg. unfold UNIT. replace (Bg + (16 + 16 * off - 3)) with (Bg + (13 + 16 * off)) by (clear; lia).
    apply COPY. clear - Hoff NDR KT FIT HO STR; lia. }
  assert (FR' : rw_cells rsegs mm (bv_unsigned (Z_to_bv 64 sp1)) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (rewrite unsigned_lit by (subst sp1; lia); exact FR).
  set (gw := wz G) in *. assert (HGW : bv_unsigned gw = G) by (subst gw; apply wz_unsigned; exact GR64). rewrite <- HGW in MM.

  eapply evt_mono.
  { apply (tail_6c0 rax (Z_to_bv 64 sp1) gp tp s7 s8 s9 s10 s11 t4v t5v t6v ra s0 s1 s2 s3 s4 s5 s6 gw _ _ _ _ _ F fc mm G NB needed n off mword b3
             HGW ltac:(clear - GR64; lia) NB0 ltac:(clear - HN; lia) ltac:(clear - Hoff; lia) B3R ltac:(clear - NDR; lia) NDA ND62 MWM MW64 GF2
             ltac:(rewrite unsigned_lit by (subst sp1; clear - SPR LO CLOv; lia); subst sp1; clear - GF3 CLOv LO; lia)
             ltac:(rewrite unsigned_lit by (subst sp1; clear - SPR LO CLOv; lia); subst sp1; clear - NCEILv CLOv LO; lia)
             ltac:(rewrite unsigned_lit by (subst sp1; clear - SPR LO CLOv; lia); subst sp1; clear - SPR LO; lia)
             MM WRN BK FR' MI1). }
  intros ms' (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & m2 & m' & -> & EM & MU2 & WM2 & MI' & MM2 & FR2).
  rewrite unsigned_lit in FR2 |- * by (subst sp1; clear - SPR LO CLOv; lia).
  replace (Z_to_bv 64 (sp1 + 64)) with sp by (apply bv_eq; rewrite unsigned_lit by (subst sp1; clear - SPR LO CLOv; lia); subst sp1; clear; lia).
  rewrite HGW in MM2.
  set (m3 := write_to_mem m2 (wa (NB + needed - 4)) [b8 0]) in EM.

  assert (PE2 : rpres_except (fun x => (G + 16 <= x < G + 24) \/ (G + 32 <= x < G + 40)) mm m2).
  { eapply rpres_except_of_munch; [exact MU2| exact WM2|]. intros x Hx NC. cbn [outside]. clear - NC. repeat split; lia. }
  assert (AG2 : forall x, 0 <= x < 2^64 -> ~ (Bg <= x < Bg + OL) -> ~ (NB <= x < NB + needed) -> ~ (lo <= x < sp1) -> ~ (G + 16 <= x < G + 24) -> ~ (G + 32 <= x < G + 40) ->
                 m2 (wa x) = m1 (wa x)).
  { intros x Hx N1 N2 N3 N4 N5. rewrite <- (AGM x Hx N1 N2 N3). apply (proj1 (PE2 x Hx ltac:(clear - N4 N5; tauto))). }

  assert (EMW' : meta_word (m_set_maplen (needed / 4096) mr) = 4064 + needed).
  { unfold meta_word, m_set_maplen. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. change (2 ^ 52 - 1) with (Z.ones 52).
    rewrite Z.land_ones by (clear; lia). rewrite Z.mod_small by (clear - ND62 ND4096; Z.div_mod_to_equations; lia).
    rewrite L0, FB1, SC. clear - NDA. Z.div_mod_to_equations. lia. }
  lazymatch type of MM2 with rw_cells _ _ _ [C8 ?u0; C8 ?u1; _; C4 ?u3; C4 ?u4; _] =>
    pose proof (rw_cells_app_inv m2 G [C8 u0; C8 u1] _ MM2) as [_ MMb]; cbn [cells_size csize Nat.add Z.of_nat app] in MMb;
    pose proof (rw_cells_app_inv m2 (G + 16) [C8 (wz NB)] _ MMb) as [NEWM MMc]; cbn [cells_size csize Nat.add Z.of_nat app] in MMc;
    pose proof (rw_cells_app_inv m2 (G + 16 + 8) [C4 u3; C4 u4] _ MMc) as [_ NEWW]; cbn [cells_size csize Nat.add Z.of_nat Pos.to_nat app] in NEWW end.
  replace (G + 16 + 8 + 8) with (G + 32) in NEWW by (clear; lia). rewrite <- EMW' in NEWW.
  destruct (rptrs_remap st LB0 m1 (fst bg) r g (fst bg, 0) ai CINV0 RMR Hr Kr HgB0 ONLYG0) as (PC1 & PC2 & PC3 & PC4 & PC5 & PC6 & PC7 & PM & PA & PG).

  assert (AGst : forall x, 0x10000 <= x < 0x88000 -> m2 (wa x) = m1 (wa x)).
  { intros x Hx. apply AG2; clear - Hx DRr DRn CLOv GF4 OL4096 ND4096; lia. }
  assert (MR2 : rmrep (rstT st (fst bg) g NB needed) m2).
  { apply (rmrep_remap st m1 m2 (fst bg) r g ai NB needed RMR Hr Kr HgB0 HM0 MSL EOL); try assumption.
    - clear - ND4096; lia.
    - intros x Hx. apply AGst. unfold RMLOCK in Hx. clear - Hx; lia.
    - intros x Hx. apply AGst. unfold RLIBC in Hx. clear - Hx; lia.
    - intros x Hx. apply AGst. unfold RGOT_SSP in Hx. clear - Hx; lia.
    - intros x Hx. apply AGst. unfold RSSP_GUARD in Hx. clear - Hx; lia.
    -
      intros a' ar' Ha' x Hx N4 N5.
      destruct (rarea_conc st _ _ WF Ha') as (ra' & Hra' & Ca' & Sa0 & Sa1 & SaL & NKa & RaB0 & RaAL & RaC). pose_ceil.
      assert (NEa : fst a' <> fst bg) by (intros E0; rewrite E0, Hr in Hra'; assert (ra' = r) by congruence; subst ra'; exact (NKa Kr)).
      pose proof (DISJr _ _ _ _ Hra' Hr NEa) as D1. pose proof (DJ' _ _ Hra' NEa) as D2.
      pose proof (rarea_lr_lo st _ _ ra' WF Ha' Hra') as LRa. pose proof (lr_lo_group r Kr) as LRr. rewrite <- EOL, LRr, <- EBg in D1.
      apply AG2; [clear - Hx Ca' Sa0 Sa1 RaB0 RaC; lia| clear - Hx D1 LRa Ca' Sa1; lia| clear - Hx D2 LRa Ca' Sa1; lia| subst sp1; clear - Hx Ca' Sa1 RaC CLOv LO; lia| exact N4| exact N5].
    -
      intros b' gh' Hb' NEb x Hx. destruct (WG b' gh' Hb') as (rb & Hrb & Krb & Sb0 & Sb1 & _).
      rewrite (conc_region' st b' rb Hrb) in Hx.
      pose proof (DISJr _ _ _ _ Hrb Hr NEb) as D1. pose proof (DJ' _ _ Hrb NEb) as D2. rewrite (lr_lo_group rb Krb) in D1, D2. rewrite <- EOL, (lr_lo_group r Kr), <- EBg in D1.
      assert (NEg : fst b' <> fst a) by (intros E0; rewrite E0, Hrga in Hrb; assert (rb = rga) by congruence; subst rb; exact (NKg Krb)).
      pose proof (DISJr _ _ _ _ Hrb Hrga NEg) as D3. rewrite (lr_lo_group rb Krb) in D3.
      pose proof (rarea_lr_lo st _ _ rga WF (proj1 (bf_area _ _ _ _ _ _ _ _ _ _ _ BF)) Hrga) as LRa.
      destruct (WR _ _ Hrb) as (RbB0 & _ & _ & RbC & _). pose_ceil. unfold NSLOTS in Hka.
      apply AG2; [clear - Hx Sb0 Sb1 RbB0 RbC; lia| clear - Hx D1 Sb0 Sb1; lia| clear - Hx D2 Sb0 Sb1; lia| subst sp1; clear - Hx Sb0 Sb1 RbC CLOv LO; lia
                | clear - Hx D3 LRa Cga Sga1 HG Hka Sb0 Sb1; lia| clear - Hx D3 LRa Cga Sga1 HG Hka Sb0 Sb1; lia].
    -
      intros q rq Hq Kq NEq x Hx.
      pose proof (DISJr _ _ _ _ Hq Hr NEq) as D1. pose proof (DJ' _ _ Hq NEq) as D2. rewrite (lr_lo_group rq Kq) in D1, D2. rewrite <- EOL, (lr_lo_group r Kr), <- EBg in D1.
      assert (NEg : q <> fst a) by (intros E0; rewrite E0, Hrga in Hq; assert (rq = rga) by congruence; subst rq; exact (NKg Kq)).
      pose proof (DISJr _ _ _ _ Hq Hrga NEg) as D3. rewrite (lr_lo_group rq Kq) in D3.
      pose proof (rarea_lr_lo st _ _ rga WF (proj1 (bf_area _ _ _ _ _ _ _ _ _ _ _ BF)) Hrga) as LRa.
      destruct (WR _ _ Hq) as (RqB0 & _ & _ & RqC & _). pose_ceil. unfold NSLOTS in Hka.
      apply AG2; [clear - Hx RqB0 RqC; lia| clear - Hx D1; lia| clear - Hx D2; lia| subst sp1; clear - Hx RqC CLOv LO; lia
                | clear - Hx D3 LRa Cga Sga1 HG Hka; lia| clear - Hx D3 LRa Cga Sga1 HG Hka; lia].
    - intros i Hi. assert (Hi' : 0 <= i < needed) by (clear - Hi; lia).
      rewrite <- EBg, <- (COPY i Hi). apply (proj1 (PE2 (NB + i) ltac:(clear - Hi' NB0 NCEILv; lia) ltac:(cbv beta; clear - Hi' GF2; lia))).
    - intros i Hi. assert (Hi' : 0 <= i < needed) by (clear - Hi KT; subst kt OL mr; lia).
      rewrite <- (ZERO i Hi). apply (proj1 (PE2 (NB + i) ltac:(clear - Hi' NB0 NCEILv; lia) ltac:(cbv beta; clear - Hi' GF2; lia))).
    - eapply rpres_except_wr_at; [exact PE2| exact WRN| cbv beta; intros x Hx; clear - Hx GF2; lia]. }

  pose proof (realloc_ticks _ _ _ AR) as TK.
  set (stR := rstT st (fst bg) g NB needed) in MR2.
  assert (TKR : ticks_ok stR).
  { subst stR. unfold rstT. apply ticks_ok_trim_shadow. unfold rstR. apply ticks_ok_upd_meta. eapply A_ASlot_M0.ticks_ok_same; [| | exact TK]; reflexivity. }
  set (st0 := set_tick (N.succ (s_tick st)) stR).
  assert (MR0 : rmrep st0 m2) by (apply rmrep_set_tick; exact MR2).
  assert (TK0 : ticks_ok st0) by (apply ticks_ok_set_tick; [change (s_tick stR) with (s_tick st); clear; lia| exact TKR]).
  set (r' := mkRegion RKGroup NB needed).
  assert (Hr' : s_regions st0 !! (fst bg) = Some r') by (subst st0 stR; cbn [s_regions set_tick]; apply rr_lookup_new).
  assert (GR0 : s_groups st0 = s_groups st) by reflexivity.
  pose proof (rmrep_wr8 st0 m2 (fst bg, needed - 4) 0 r' MR0 TK0 Hr' eq_refl ltac:(cbn [snd r_len r']; rewrite NDround; clear - ND4096; lia)
                ltac:(cbn [fst snd]; intros b' gh' Hb' Hf'; rewrite GR0 in Hb'; pose proof (ONLYG0 _ _ Hb' Hf') as ->; cbn [snd]; clear - ND4096; lia)
                ltac:(clear; lia)) as MR3.
  cbn [fst snd r_base r'] in MR3. replace (NB + (needed - 4)) with (NB + needed - 4) in MR3 by (clear; lia). fold m3 in MR3.
  pose proof (ticks_ok_wr8 st0 (fst bg, needed - 4) 0 TK0) as TK3.
  destruct (rss_mrep (wr8 (fst bg, needed - 4) 0 st0) m3 (fst bg, 0) r' (needed - 16) 0 n off b3 MR3 TK3
              ltac:(cbn [fst]; change (s_regions (wr8 ?q ?v ?X)) with (s_regions X); exact Hr') eq_refl ltac:(cbn [snd]; clear; lia) ltac:(clear; lia)
              ltac:(cbn [snd r_len r']; rewrite NDround; clear - ND4096; lia) ltac:(clear - ND4096; lia)
              ltac:(cbn [fst snd]; intros b' gh' Hb' Hf'; change (s_groups (wr8 ?q ?v ?X)) with (s_groups X) in Hb'; rewrite GR0 in Hb';
                    pose proof (ONLYG0 _ _ Hb' Hf') as ->; cbn [snd]; clear - ND4096; lia)
              ltac:(clear - Hoff; lia) ltac:(clear - HN; lia) ltac:(clear - NDR; lia) ltac:(clear - NDR; lia)
              B3K) as [RSS TKS].
  cbn [fst snd r_base r'] in RSS, TKS.
  replace (NB + (0 + 16 + (needed - 16) * 0 + 16 * off)) with P' in RSS by (rewrite EP'; clear; lia).
  replace (NB + (0 + 16 + (needed - 16) * 0 + (needed - 16 - 4))) with E' in RSS by (rewrite EE'; clear; lia).
  rewrite <- EP', <- EE' in EM. rewrite <- EM in RSS.
  lazymatch type of RSS with rmrep ?stF _ => assert (EFULL : remap_full st c off n NB needed = stF) end.
  { unfold remap_full. rewrite SL. cbv zeta.
    lazymatch goal with |- context [get_stride (get_meta_rec ?sx g)] =>
      replace (get_stride (get_meta_rec sx g)) with (needed - 16) end.
    2:{ change (get_meta_rec (set_tick _ (trim_shadow _ _ ?X)) g) with (get_meta_rec X g). unfold remap_update. rewrite MI_Kit.get_meta_rec_upd_same.
        change (get_meta_rec (set_regions _ st) g) with mr. unfold get_stride, m_set_maplen. cbn [m_last_idx m_sizeclass m_maplen]. rewrite L0.
        change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by (clear; lia). rewrite Z.mod_small by (clear - ND62 ND4096; Z.div_mod_to_equations; lia).
        cbn [Z.eqb andb]. destruct (Z.eqb_spec (needed / 4096) 0) as [X|X]; [exfalso; clear - X ND4096; Z.div_mod_to_equations; lia|]. cbn.
        unfold UNIT. clear - NDA. Z.div_mod_to_equations. lia. }
    rewrite I0, Ec16. subst st0 stR. unfold rstT, rstR, remap_update, aadd, UNIT, IB. cbn [fst snd].
    replace (0 + 16 + (needed - 16) * 0 + 16 * off) with (16 + 16 * off) by (clear; lia).
    replace (0 + 16 + (needed - 16) * 0 + (needed - 16 - 4)) with (needed - 4) by (clear; lia).
    replace (16 + (needed - 16 - 4)) with (needed - 4) by (clear; lia). reflexivity. }
  rewrite <- EFULL in RSS, TKS.

  assert (DISJc : forall rid2 r2, s_regions st !! rid2 = Some r2 -> rid2 <> fst c -> let '(b2, l2) := region_live_range r2 in NB + needed <= b2 \/ b2 + l2 <= NB).
  { intros rid2 r2 H2 NE2. apply (DISJ rid2 r2 H2). rewrite <- FC. exact NE2. }
  destruct (areach_realloc_remap ref_reserved st LB0 p A old n off AR Hin0 HN HA (fst c) g Bg OL needed NB RC NB0 NBA NCEIL DISJc) as (ARR & _).
  fold c in ARR. replace (NB + UNIT + UNIT * off) with P' in ARR by (rewrite EP'; unfold UNIT; clear; lia).

  unfold UNIT, IB in FIT, S16.
  assert (PE3 : rpres_except (fun x => x = P' - 3 \/ P' + n <= x < NB + needed) m2 m').
  { rewrite EM. subst m3. rewrite <- EE'. apply (rinplace_pres m2 P' E' n b3 NB (NB + needed)); rewrite ?EE', ?EP'; clear - NB0 NCEILv NDR Hoff HN ND4096; lia. }
  assert (PE23 : rpres_except (fun x => (NB <= x < NB + needed) \/ (G + 16 <= x < G + 24) \/ (G + 32 <= x < G + 40)) mm m').
  { eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE2| cbv beta; intros x Hx; clear - Hx; tauto]|].
    eapply rpres_except_mono; [exact PE3| cbv beta; intros x Hx; left; rewrite EP' in Hx; clear - Hx Hoff HN NDR; lia]. }
  set (C := fun x : Z => ((lo <= x < bv_unsigned sp) \/ (RERRNO <= x < RERRNO + 4)) \/ (Bg <= x < Bg + OL) \/ (NB <= x < NB + needed) \/ (G + 16 <= x < G + 24) \/ (G + 32 <= x < G + 40)).
  assert (PE : rpres_except C m m').
  { eapply rpres_except_trans; [eapply rpres_except_mono; [exact PRES1| subst C; cbv beta; intros x Hx; clear - Hx; tauto]|].
    eapply rpres_except_trans; [eapply rpres_except_mono; [exact PEM|]|].
    { subst C; cbv beta. intros x [X|[X|X]]; [right; left; exact X| right; right; left; exact X| left; left; subst sp1; clear - X; lia]. }
    eapply rpres_except_mono; [exact PE23| subst C; cbv beta; intros x Hx; clear - Hx; tauto]. }

  assert (NCstk : forall x, bv_unsigned sp <= x -> ~ C x).
  { intros x Hx. subst C; cbv beta. subst sp1. unfold RERRNO. clear - Hx LO CLOv RBC NCEILv GF3 SPR. lia. }
  assert (NCimg : forall x, x < 0x88000 -> 0x10000 <= x -> ~ (RERRNO <= x < RERRNO + 4) -> ~ C x).
  { intros x H1 H2 H3. subst C; cbv beta. clear - H1 H2 H3 CLOv DRr DRn GF4 OL4096 ND4096. lia. }
  pose proof (rarea_lr_lo st _ _ rga WF (proj1 (bf_area _ _ _ _ _ _ _ _ _ _ _ BF)) Hrga) as LRa. unfold NSLOTS in Hka.
  assert (NCblk : forall b' x, In b' (lb_remove p LB) -> blk_addr b' <= x < blk_addr b' + blk_size b' -> ~ C x).
  { intros b' x Hb' Hab. unfold lb_remove in Hb'. apply In_filter_b in Hb' as [Hb' NEQ].
    assert (Hb0 : In b' LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hb']).
    assert (NE : blk_slot b' <> c).
    { intros EQ. pose proof (nodup_slot_unique LB0 (p, A, old) b' (realloc_nodup _ _ _ AR) Hin0 Hb0 EQ) as ->.
      unfold bptr_eqb, blk_id in NEQ. cbn [fst snd] in NEQ. rewrite aptr_eqb_refl, Z.eqb_refl in NEQ. discriminate. }
    destruct (RHEAP_block_range_proof s LB0 m1 b' ltac:(exists st, LB0; split; [apply Permutation_refl|]; split; [exact Hst|]; split; [exact RMR|]; split; [exact HBL| exact AR]) Hb0) as (_ & _ & _ & BC' & BI').
    pose_ceil.
    destruct (realloc_blk_in_region ref_reserved st LB0 p A old AR Hin0 g bg idx SL HM b' Hb0 x Hab) as (rq & Hrq & Krq & Haq).
    pose proof (RPRIV b' Hb0 NE x) as PRV. rewrite <- EOL, <- EBg in PRV.
    assert (NQB : ~ (NB <= x < NB + needed)).
    { intros X. destruct (N.eq_dec (fst (blk_slot b')) (fst bg)) as [EQ|NEq].
      - rewrite EQ, Hr in Hrq. assert (rq = r) as -> by congruence. rewrite <- EOL, <- EBg in Haq. exact (PRV Haq Hab).
      - pose proof (DISJ _ _ Hrq NEq) as D. unfold region_live_range in D. rewrite Krq in D. clear - D X Haq. lia. }
    assert (NEg : fst (blk_slot b') <> fst a) by (intros E0; rewrite E0, Hrga in Hrq; assert (rq = rga) by congruence; subst rq; exact (NKg Krq)).
    pose proof (DISJr _ _ _ _ Hrq Hrga NEg) as D3. rewrite (lr_lo_group rq Krq) in D3.
    subst C; cbv beta. intros [[X|X]|[X|[X|[X|X]]]].
    - clear - X Hab BC' CLOv. lia.
    - unfold RERRNO in X. clear - X Hab BI'. lia.
    - exact (PRV X Hab).
    - exact (NQB X).
    - clear - X Haq D3 LRa Cga Sga1 HG Hka. lia.
    - clear - X Haq D3 LRa Cga Sga1 HG Hka. lia. }

  assert (ST' : stk rsegs m' lo sp1) by (eapply rpres_except_stk; [exact PE23| exact ST1| cbv beta; intros x Hx; subst sp1; clear - Hx NCEILv CLOv GF3 LO; lia]).
  eapply stk_release in FR2; [| exact ST'| subst sp1; clear - LO CLOv; lia]. clear ST'. rename FR2 into ST'. cbn [cells_size csize Nat.add] in ST'.
  lazymatch type of ST' with stk _ _ _ ?h => replace h with (bv_unsigned sp) in ST' by (subst sp1; clear; lia) end.
  rewrite ETP in ERR1.
  assert (ERR' : rw_cells rsegs m' (errno_addr tp) [C4 errv2]).
  { rewrite ETP. eapply rpres_except_rw_cells; [exact PE23| exact ERR1|]. cbn [cells_size csize Nat.add Z.of_nat]. cbv beta. intros x Hx. clear - Hx DRn GF4 ND4096; lia. }
  assert (AUX' : rauxv_ok m' B).
  { eapply rauxv_ok_pres_B; [exact AUX1| exact PE23| cbv beta; intros x Hx; clear - Hx SB LO CLOv NCEILv GF3; lia| cbv beta; unfold RAUXV_CELL, RLIBC; intros x Hx; clear - Hx DRn GF4 ND4096; lia]. }

  pose proof (realloc_nodup _ _ _ AR) as ND0.
  assert (PERM' : Permutation (rLB' LB0 p n P') ((p, P', n) :: lb_remove p LB)).
  { unfold rLB'. apply perm_skip. rewrite (lb_remove_lbrm LB p A old (NoDup_map_perm blk_slot LB0 LB PERM ND0) ltac:(eapply Permutation_in; [exact PERM| exact Hin0])).
    unfold lbrm. cbn [blk_slot fst]. fold c. apply filter_Permutation. exact PERM. }

  assert (AIMG0 : A + old <= 0x10000 \/ 0x88000 <= A) by (clear - DRr HAE FIT Hoff HO STR OL4096; lia).
  assert (HK0 : 0 <= Z.min old n <= old /\ Z.min old n <= n) by (clear - HO HN; lia).
  set (k := Z.to_nat (Z.min old n)).
  assert (OLDk : bytes_at rsegs m A (firstn k oldbs)).
  { rewrite <- (firstn_skipn k oldbs) in OLDB. apply bytes_at_app in OLDB as [X _]. exact X. }
  assert (LK : length (firstn k oldbs) = k) by (rewrite length_firstn; subst k; clear - HK0 OLEN; lia).
  assert (OLD1 : bytes_at rsegs m1 A (firstn k oldbs)).
  { eapply rpres_except_bytes_at; [exact PRES1| exact OLDk|]. rewrite LK. cbv beta. intros x Hx. subst k. unfold RERRNO. clear - Hx HK0 AIMG0 HAE FIT HO STR RBC CLOv LO Hoff; lia. }
  assert (OLDmm : bytes_at rsegs mm P' (firstn k oldbs)).
  { apply (rbytes_at_moved m1 mm A P' (firstn k oldbs) OLD1); rewrite ?LK.
    - intros i Hi. rewrite EP', HAE. replace (NB + 16 + 16 * off + i) with (NB + (16 + 16 * off + i)) by (clear; lia).
      replace (Bg + 16 + 16 * off + i) with (Bg + (16 + 16 * off + i)) by (clear; lia). apply COPY. subst k kt. clear - Hi HK0 FIT STR NDR Hoff; lia.
    - rewrite EP'; clear - NB0 Hoff; lia.
    - rewrite EP'; subst k; clear - NCEILv HK0 NDR Hoff; lia.
    - subst k; clear - AIMG0 HK0; lia.
    - rewrite EP'; subst k; clear - DRn HK0 NDR Hoff ND4096; lia. }
  assert (OLD2 : bytes_at rsegs m2 P' (firstn k oldbs)).
  { eapply rpres_except_bytes_at; [exact PE2| exact OLDmm|]. rewrite LK. cbv beta. intros x Hx. subst k. clear - Hx HK0 GF2 EP' NDR Hoff; lia. }
  assert (OLD' : bytes_at rsegs m' P' (firstn k oldbs)).
  { eapply rpres_except_bytes_at; [exact PE3| exact OLD2|]. rewrite LK. cbv beta. intros x Hx. subst k. clear - Hx HK0; lia. }
  assert (WRn : wr_at rsegs m' P' n).
  { eapply rpres_except_wr_at; [exact PE3| |cbv beta; intros x Hx; clear - Hx; lia].
    eapply rpres_except_wr_at; [exact PE2| eapply wr_at_sub; [exact WRN| rewrite EP'; clear - Hoff; lia| rewrite EP'; clear - NDR Hoff; lia]| cbv beta; intros x Hx; clear - Hx GF2 EP' NDR Hoff; lia]. }
  destruct (rwr_at_bytes_exist m' (P' + Z.of_nat k) (n - Z.of_nat k) ltac:(eapply wr_at_sub; [exact WRn| subst k; clear - HK0; lia| subst k; clear - HK0; lia]) ltac:(subst k; clear - HK0; lia) ltac:(rewrite EP'; subst k; clear - DRn HK0 NDR Hoff ND4096; lia)) as (junk & LJ & BJ).
  assert (BLK : rw_cells rsegs m' P' [Cells.CB (Z.to_nat n) (firstn k oldbs ++ junk)]).
  { split; [split|].
    - cbn. split; [| exact I]. rewrite length_app, LK, LJ. subst k. clear - HK0 HN; lia.
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split; [exact OLD'|]. rewrite LK. exact BJ.
    - cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (clear - HN; lia). exact WRn. }

  unfold POST, rrealloc_post. do 15 eexists. exists m', errv2. split; [reflexivity|].
  split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|].
  split. { intros x Hx. apply (proj1 (PE x ltac:(unfold RAUXV_CELL, RLIBC in Hx; clear - Hx; lia) ltac:(apply NCimg; unfold RAUXV_CELL, RLIBC, RERRNO in *; clear - Hx; lia))). }
  split. { intros x Hx HCx. apply PE; [exact Hx|]. destruct HCx as [X|[[X NS]|(b' & Hb' & Hab)]]; [apply NCstk; exact X| apply NCimg; unfold ralloc_static, RERRNO in *; clear - X NS; lia| exact (NCblk b' x Hb' Hab)]. }
  split; [reflexivity|]. split; [reflexivity|].
  exists P', junk.
  split; [rewrite EP'; reflexivity|].
  split. { pose_ceil; unfold rblock_range. rewrite EP'. clear - NB0 NBA HN NDR NCEILv Hoff DRn ND4096. Z.div_mod_to_equations. lia. }
  split.
  { exists (remap_full st c off n NB needed), (rLB' LB0 p n P'). split; [exact PERM'|].
    split. { rewrite strip_remap_full by (exists (g, idx); exact SL). rewrite SL. cbn [ps_m set_m]. rewrite Hst. reflexivity. }
    split; [exact RSS|]. split; [| exact ARR].
    unfold brk_link in HBL |- *. cbn [ps_brk set_m].
    change (ctx (remap_full st c off n NB needed)) with (s_ctx (remap_full st c off n NB needed)).
    rewrite <- (s_ctx_strip (remap_full st c off n NB needed)), strip_remap_full, SL, s_ctx_remap_update, s_ctx_strip by (exists (g, idx); exact SL).
    change (s_ctx st) with (ctx st).
    destruct (c_brk (ctx st)) as [| |brid boff]; [exact I| exact I|].
    rewrite HBL. unfold conc, get_region.
    rewrite <- (s_regions_strip (remap_full st c off n NB needed)), strip_remap_full, SL, s_regions_remap_update by (exists (g, idx); exact SL).
    cbn [fst snd]. rewrite lookup_insert_ne by (rewrite FC; clear - PC7; congruence). rewrite s_regions_strip. reflexivity. }
  exact BLK.
Qed.
End TAIL.

Section P.
Hypothesis HMAL : rmalloc_impl_stmt.
Hypothesis HFREE : rfree_impl_stmt.

Theorem remap_arm_proof : remap_arm_stmt.
Proof.
  unfold remap_arm_stmt.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 F fc m m1 s LB LB0 p A old n lo B errv oldbs st g bg idx r off.
  intros _ _ PERM Hst RMR HBL AR Hin0 SL HM Hr Kr FC Ec CB HA Hoff FIT HO S16 SMOD B0 BG16 Hidx LI SPAN RCEIL RB0 SSTR SC63 K3
         FR ST1 MI1 ERR1 AUX1 PRES1 OLDB OLEN SB CLO LO TP HN _ y7 a5v y28 THR SC.
  set (c := fst p) in *. set (mr := get_meta_rec st g) in *. set (stride := get_stride mr) in *. set (Bg := conc st bg) in *.
  set (E := Bg + 16 + stride * (idx + 1) - 4) in *. set (sp1 := bv_unsigned sp - 64) in *.
  set (POST := rrealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p A old n lo B oldbs m).
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof LO as LOr. unfold RREALLOC_STACK, RMALLOC_STACK in LO. pose proof CLO as CLOv. pose_ceil.
  assert (ETP : bv_unsigned tp + -164 = 422892) by (rewrite TP; unfold RATP; rewrite unsigned_lit by lia; reflexivity).

  destruct (realloc_bf ref_reserved st LB0 p A old AR Hin0 g bg idx SL HM) as (L & LS & BL & off' & ai & a & ar & ka & INV & CR & Hk & HA' & BF).
  change (fst p) with c in HA'. assert (off' = off) as -> by (rewrite HA in HA'; unfold UNIT in HA'; clear - HA'; lia). clear HA'.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as HgB. fold c in HgB.
  pose proof (ig_ok _ _ _ IG _ _ _ HgB) as GO.
  destruct (g_sc _ _ _ _ _ _ GO) as [[S48 _]|(_ & L0 & ML & _)]; [exfalso; change (MR st g) with mr in S48; clear - S48 SC; lia|].
  change (MR st g) with mr in L0, ML.
  destruct (g_top _ _ _ _ _ _ GO ML) as (SB0 & r0 & Hr0 & Kr0 & EOL & GE). change (MR st g) with mr in EOL, GE.
  rewrite Hr in Hr0. assert (r0 = r) as -> by congruence.
  assert (I0 : idx = 0) by (clear - Hidx L0; lia).
  assert (STR : stride = m_maplen mr * 4096 - 16).
  { subst stride. unfold get_stride. rewrite L0. cbn [Z.eqb andb]. destruct (Z.eqb_spec (m_maplen mr) 0); [exfalso; exact (ML ltac:(eassumption))| reflexivity]. }
  set (OL := m_maplen mr * 4096) in *.
  pose proof (g_maplen _ _ _ _ _ _ GO) as ML0. change (MR st g) with mr in ML0.
  assert (OL4096 : 4096 <= OL) by (subst OL; clear - ML ML0; lia).
  assert (EBg : Bg = r_base r) by (subst Bg; rewrite CB, SB0; clear; lia).
  assert (CC : conc st c = Bg + 16) by (subst c; rewrite (conc_region' st (fst p) r) by (rewrite FC; exact Hr); rewrite Ec; cbn [snd]; rewrite SB0, I0, EBg; unfold UNIT; clear; lia).
  assert (HAE : A = Bg + 16 + 16 * off) by (rewrite HA, CC; unfold UNIT; clear; lia).
  assert (HE : E = Bg + OL - 4) by (subst E; rewrite I0, STR; clear; lia).
  set (needed := remap_needed (UNIT * off) n).
  pose proof (remap_needed_ge (UNIT * off) n ltac:(clear - HN; lia) ltac:(unfold UNIT; clear - Hoff; lia)) as NDR. fold needed in NDR. unfold UNIT, IB in NDR.
  pose proof (remap_needed_pg (UNIT * off) n) as NDA. fold needed in NDA.
  assert (ND62 : needed < 2 ^ 62) by (clear - NDR HN Hoff; lia).
  assert (ND4096 : 4096 <= needed) by (clear - NDR NDA HN Hoff; Z.div_mod_to_equations; lia).
  set (kt := Z.min OL needed).
  pose proof RMR as (WF & CX & GL & ARS & GR & SH). pose proof WF as (Hres & WR & DISJr & WA & WG).
  destruct (WR _ _ Hr) as (RrB0 & RBAL & RL0 & RBC & RF). pose_ceil.
  pose proof (round_up_pg_ge (r_len r)) as RUP. rewrite <- EOL in RUP, RBC, RF.
  pose proof (rreserved_disjoint1 _ _ RF ltac:(clear - OL4096; lia)) as DRr. rewrite <- EBg in DRr, RBC, RrB0, RBAL, RF.
  destruct (SH _ _ Hr Kr) as [WRr RDr]. rewrite <- EBg, <- EOL in WRr.
  set (mword := m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr) in *.
  pose proof (g_freeable _ _ _ _ _ _ GO) as FB1. change (MR st g) with mr in FB1.
  assert (MWR : 0 <= mword < 2^64) by (subst mword OL; rewrite L0, FB1, SC; clear - ML0 RBC RrB0; lia).
  assert (MWP : mword - mword mod 4096 = OL).
  { subst mword OL. rewrite L0, FB1, SC. replace (0 + 32 * 1 + 64 * 63 + 4096 * m_maplen mr) with (4064 + m_maplen mr * 4096) by (clear; lia).
    rewrite Z.mod_add, Z.mod_small by (clear; lia). clear; lia. }
  assert (NDE : needed = (n + 4095 + 16 * off + 20) - (n + 4095 + 16 * off + 20) mod 4096).
  { subst needed. unfold remap_needed, UNIT, IB. clear - HN Hoff. Z.div_mod_to_equations. lia. }

  assert (RC : realloc_case (strip st) c A n = RcRemap (fst c) g Bg OL needed).
  { unfold realloc_case, realloc_geom. change (s_slots (strip st)) with (s_slots st). rewrite SL.
    change (get_meta_rec (strip st) g) with mr. change (conc (strip st) c) with (conc st c). fold stride. cbn [rg_g rg_start rg_end rg_idx rg_stride].
    unfold inplace_ok. cbn [rg_end rg_g]. change (get_meta_rec (strip st) g) with mr.
    replace (n <? MMAP_THRESHOLD) with false by (symmetry; apply Z.ltb_ge; clear - THR; lia). rewrite andb_false_r. cbn [andb].
    replace (MMAP_THRESHOLD <=? n) with true by (symmetry; apply Z.leb_le; exact THR).
    replace (48 <=? m_sizeclass mr) with true by (symmetry; apply Z.leb_le; clear - SC; lia). cbn [andb].
    rewrite HM. change (conc (strip st) bg) with Bg. subst needed. rewrite CC, HAE. f_equal. unfold UNIT. f_equal. clear; lia. }

  assert (DISJo : forall rid2 r2, s_regions st !! rid2 = Some r2 -> rid2 <> fst bg ->
                  let '(b2, l2) := region_live_range r2 in Bg + OL <= b2 \/ b2 + l2 <= Bg).
  { intros rid2 r2 H2 NE2. pose proof (DISJr _ _ _ _ H2 Hr NE2) as D. rewrite (lr_lo_group r Kr), <- EBg, <- EOL in D.
    unfold region_live_range. unfold lr_lo in D. destruct (r_kind r2); unfold PGSZ; clear - D; lia. }
  assert (SP1 : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; subst sp1; clear - SPR LO CLOv; lia).
  unfold realloc_body. rewrite <- Hst, RC. unfold realloc_remap.
  destruct (Z.eqb_spec OL needed) as [EQ|NEQ].
  -
    eapply (implM_bind rsegs _ _ _ (fun _ s' ms' => POST (Some p) s' ms')); [| intros [] s' ms' H'; apply implM_ret; apply evt_done; exact H'].
    apply implM_upd. rewrite Hst.

    step. step. rewrite (unsigned_lit (Bg + stride * idx + 16)) by (clear - RrB0 RBC OL4096 STR I0; subst stride; lia).
    replace (A + - (Bg + stride * idx + 16)) with (16 * off) by (rewrite I0, HAE; clear; lia).
    step. step. step. step. rewrite ?(unsigned_lit (16 * off)) by (clear - Hoff; lia). step.
    step. rewrite ?(unsigned_lit (n + 4095 + 16 * off + 20)) by (clear - Hoff HN; lia). rewrite land_pgmask by (clear - Hoff HN; lia). rewrite <- NDE.
    step. rewrite (wz_unsigned mword) by exact MWR. rewrite land_pgmask by exact MWR. rewrite MWP.
    step. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by (clear - OL4096 RBC RrB0 ND62 ND4096; lia). 2:{ exfalso. clear - K0 EQ. lia. } clear K0.
    change (wz Bg) with (Z_to_bv 64 Bg).
    apply (remap_tail ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 m1 s LB LB0 p A old n lo B errv oldbs st g bg idx r off Bg
             PERM Hst RMR HBL AR Hin0 SL HM Hr Kr FC Ec CB HA Hoff FIT HO B0 BG16 Hidx SPAN RB0 K3 FR ST1 MI1 ERR1 AUX1 PRES1 OLDB OLEN SB CLO LOr TP HN SC RC).
    + exact RrB0.
    + exact RBAL.
    + pose_ceil. fold needed. clear - RBC EQ. lia.
    + fold needed. rewrite <- EQ. exact RF.
    + fold needed. rewrite <- EQ. exact DISJo.
    + intros; reflexivity.
    + fold needed. intros i Hi. exfalso. clear - Hi EQ. subst OL mr. lia.
    + fold needed. rewrite <- EQ. exact WRr.
    + intros; reflexivity.
    + intros x _ _ _ W; exact W.
  -
    assert (AVX : forall x k, ranges_free (live_ranges_except (strip st) (fst c)) x k = true -> 0 < k -> x + k <= 0x10000 \/ 0x88000 <= x).
    { intros x k H Hk0. apply (rreserved_disjoint1 x k); [| exact Hk0]. unfold live_ranges_except in H. apply ranges_free_app_l in H.
      change (s_reserved (strip st)) with (s_reserved st) in H. rewrite Hres in H. exact H. }
    assert (AV : forall x k, ranges_free (live_ranges (strip st)) x k = true -> 0 < k -> x + k <= 0x10000 \/ 0x88000 <= x).
    { intros x k H Hk0. apply (rreserved_disjoint1 x k); [| exact Hk0]. unfold live_ranges in H. apply ranges_free_app_l in H.
      change (s_reserved (strip st)) with (s_reserved st) in H. rewrite Hres in H. exact H. }
    pose proof GL as (GL1 & GL2 & GL3 & GL4 & GL5).
    eapply (implM_bind rsegs _ _ _ (fun a' s' ms' => s' = s /\
              rmremap_post (Z_to_bv 64 0x49cf4) (Z_to_bv 64 sp1) gp tp (Z_to_bv 64 needed) (wz (conc st g)) (Z_to_bv 64 (A + old)) (Z_to_bv 64 (16 * off)) (Z_to_bv 64 4095)
                           (Z_to_bv 64 A) (Z_to_bv 64 n) s7 s8 s9 s10 s11 F fc Bg OL needed
                           (live_ranges_except (strip st) (fst c)) (live_ranges (strip st)) errv (wz ssp_canary) lo m1 a' ms')).
    { eapply implM_evt.
      { step. step. rewrite (unsigned_lit (Bg + stride * idx + 16)) by (clear - RrB0 RBC OL4096 STR I0; subst stride; lia).
        replace (A + - (Bg + stride * idx + 16)) with (16 * off) by (rewrite I0, HAE; clear; lia).
        step. step. step. step. rewrite ?(unsigned_lit (16 * off)) by (clear - Hoff; lia). step.
        step. rewrite ?(unsigned_lit (n + 4095 + 16 * off + 20)) by (clear - Hoff HN; lia). rewrite land_pgmask by (clear - Hoff HN; lia). rewrite <- NDE.
        step. rewrite (wz_unsigned mword) by exact MWR. rewrite land_pgmask by exact MWR. rewrite MWP.
        step. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by (clear - OL4096 RBC RrB0 ND62 ND4096; lia). { exfalso. clear - K0 NEQ. lia. } clear K0.

        step. step. step. step. step. step. step.
        lazymatch goal with |- evt _ ?P ?ms => unify P (fun ms1 : machine_state => ms1 = ms) end. apply evt_done. reflexivity. }
      cbv beta. intros ms' ->.
      apply implM_of_enode. eapply impl_epost_mono; [| cbv beta; intros a' ms1 H1; split; [reflexivity| exact H1]].
      change (wz Bg) with (Z_to_bv 64 Bg).
      eapply rmremap_spec; [rewrite SP1; exact ST1| exact ERR1| exact GL4| exact GL5| exact MI1| reflexivity| reflexivity| reflexivity| reflexivity
        | clear - OL4096; lia| clear - ND62 ND4096; lia| exact NEQ| clear - RrB0; lia| pose_ceil; clear - RBC; lia| exact DRr| exact AVX| exact AV
        | rewrite SP1; subst sp1; clear - LO; lia| exact CLO| exact TP]. }
    cbv beta. intros a' s' ms' [-> PO].
    destruct a' as [e| |nb].
    +
      destruct PO as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & ST' & ERR' & He).
      rewrite SP1 in MU, ST'. rewrite ETP in MU.
      replace (ret_pc (Z_to_bv 64 0x49cf4)) with (Z_to_bv 64 0x49cf4) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      assert (PEe : rpres_except (fun x => (sp1 - 112 <= x < sp1) \/ (422892 <= x < 422896)) m1 m').
      { eapply rpres_except_of_munch; [exact MU| exact WM|]. intros x Hx NC. cbn [outside]. clear - NC. repeat split; lia. }
      assert (RMR' : rmrep st m').
      { eapply (rmrep_transport_unowned st m1 m' _ RMR MU WM). intros lo' hi' x Hin Hx RFx.
        destruct (rrepfoot_where st m1 x RMR RFx) as [AC AW].
        destruct Hin as [E1|[E1|[]]]; injection E1 as <- <-; pose_ceil; unfold RCTX, RMLOCK, RLIBC, RGOT_SSP, RSSP_GUARD in *; subst sp1; clear - Hx AC AW CLOv LO; lia. }
      assert (FR' : rw_cells rsegs m' sp1 [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply rpres_except_rw_cells; [exact PEe| exact FR|]. cbn [cells_size csize Nat.add Z.of_nat]. cbv beta. intros x Hx. subst sp1. clear - Hx CLOv LO. lia. }
      assert (AUX' : rauxv_ok m' B).
      { eapply rauxv_ok_pres_B; [exact AUX1| exact PEe| cbv beta; intros x Hx; subst sp1; clear - Hx SB CLOv LO; lia| cbv beta; unfold RAUXV_CELL; intros x Hx; clear - Hx CLOv LO; lia]. }
      assert (PRES' : rpres_except (fun x => (lo <= x < bv_unsigned sp) \/ (RERRNO <= x < RERRNO + 4)) m m').
      { eapply rpres_except_trans; [exact PRES1|]. eapply rpres_except_mono; [exact PEe|]. cbv beta. unfold RERRNO. intros x Hx. subst sp1. clear - Hx LO. lia. }

      eapply implM_evt.
      { step. step. step. step. step. if_true.
        lazymatch goal with |- evt _ ?P ?ms => unify P (fun ms1 : machine_state => ms1 = ms) end. apply evt_done. reflexivity. }
      cbv beta. intros ms'' ->.
      exact (move_arm HMAL HFREE ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m' s LB LB0 p A old n lo B (Z_to_bv 64 e) oldbs st g bg idx r off
               PERM Hst RMR' HBL AR Hin0 SL FC Ec HA HO S16 B0 Hidx SPAN K3 FR' ST' MI' ERR' AUX' PRES' OLDB OLEN SB CLO LOr TP HN
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    +
      destruct PO as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m2' & -> & MU & WM & MI2 & MI' & ST' & ERR2 & GROW).
      rewrite SP1 in MU, ST'.
      replace (ret_pc (Z_to_bv 64 0x49cf4)) with (Z_to_bv 64 0x49cf4) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      assert (PE12 : rpres_except (fun x => sp1 - 112 <= x < sp1) m1 m2').
      { eapply rpres_except_of_munch; [exact MU| exact WM|]. intros x Hx NC. cbn [outside]. clear - NC. repeat split; lia. }
      assert (FR2' : rw_cells rsegs m2' sp1 [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply rpres_except_rw_cells; [exact PE12| exact FR|]. cbn [cells_size csize Nat.add Z.of_nat]. cbv beta. intros x Hx. clear - Hx. lia. }
      assert (W2 : wr_at rsegs m2' Bg OL).
      { eapply rpres_except_wr_at; [exact PE12| exact WRr|]. cbv beta. intros x Hx. subst sp1. clear - Hx RBC CLOv LO. lia. }
      assert (WV : forall x : word, m2' x = m1 x \/ wview rsegs m2' x <> None -> forall mx : mem, mx x = m2' x -> wview rsegs m1 x <> None -> wview rsegs mx x <> None).
      { intros x Hx mx Ex W. unfold wview in *. rewrite Ex. destruct Hx as [E1|W1]; [rewrite E1; exact W| exact W1]. }
      unfold rmremap_same_mem in MI', ST' |- *. destruct (needed <? OL) eqn:CMP; [apply Z.ltb_lt in CMP| apply Z.ltb_ge in CMP].
      *
        set (mm := apply_unmaps m2' [(wa (Bg + needed), Z_to_bv 64 (OL - needed))]) in *.
        assert (Ha : 0 <= Bg + needed < 2^64) by (clear - RrB0 RBC ND4096 CMP; lia).
        assert (Hn : 0 <= OL - needed < 2^64) by (clear - RrB0 RBC ND4096 CMP; lia).
        assert (Han : Bg + needed + (OL - needed) <= 2^64) by (clear - RrB0 RBC; lia).
        assert (OUT : forall x : word, (bv_unsigned x < Bg + needed \/ Bg + OL <= bv_unsigned x) -> mm x = m2' x).
        { intros x Hx. subst mm. apply (unmaps_outside m2' _ _ Ha Hn Han). clear - Hx. lia. }
        assert (FRmm : rw_cells rsegs mm sp1 [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
        { subst mm. apply (rw_cells_unmaps_other rsegs m2' _ _ Ha Hn Han _ _ FR2'). cbn [cells_size csize Nat.add Z.of_nat]. subst sp1. clear - RBC CLOv LO. lia. }
        assert (ERRmm : rw_cells rsegs mm (errno_addr tp) [C4 errv]).
        { subst mm. apply (rw_cells_unmaps_other rsegs m2' _ _ Ha Hn Han _ _ ERR2). rewrite ETP. cbn [cells_size csize Nat.add Z.of_nat]. clear - DRr ND4096; lia. }
        assert (PEM0 : rpres_except (fun x => (Bg + needed <= x < Bg + OL) \/ (sp1 - 112 <= x < sp1)) m1 mm).
        { intros x Hx NC. assert (E1 : mm (wa x) = m2' (wa x)) by (apply OUT; rewrite wa_unsigned by exact Hx; clear - NC ND4096; lia).
          destruct (PE12 x Hx ltac:(cbv beta; clear - NC; tauto)) as [E2 W2']. split; [rewrite E1; exact E2|]. intros W. apply (WV (wa x) (or_introl E2) mm E1 W). }
        assert (AUXmm : rauxv_ok mm B).
        { eapply rauxv_ok_pres_B; [exact AUX1| exact PEM0| cbv beta; intros x Hx; subst sp1; clear - Hx SB RBC CLOv LO; lia| cbv beta; unfold RAUXV_CELL; intros x Hx; subst sp1; clear - Hx DRr OL4096 ND4096 CLOv LO; lia]. }
        assert (NCEILx : Bg + needed <= alloc_ceiling) by (pose_ceil; clear - RBC CMP; lia).
        assert (RFRx : ranges_free ref_reserved Bg needed = true) by (eapply ranges_free_sub; [exact RF| clear; lia| clear - CMP; lia| clear - ND4096; lia]).
        assert (DISJx : forall rid2 r2, s_regions st !! rid2 = Some r2 -> rid2 <> fst bg -> let '(b2, l2) := region_live_range r2 in Bg + needed <= b2 \/ b2 + l2 <= Bg).
        { intros rid2 r2 H2 NE2. specialize (DISJo rid2 r2 H2 NE2). destruct (region_live_range r2) as [b2 l2]. clear - DISJo CMP. lia. }
        assert (COPYx : forall i, 0 <= i < kt -> mm (wa (Bg + i)) = m1 (wa (Bg + i))).
        { intros i Hi. subst kt. rewrite OUT by (rewrite wa_unsigned by (clear - Hi RrB0 RBC ND4096; lia); clear - Hi ND4096; lia).
          apply (proj1 (PE12 (Bg + i) ltac:(clear - Hi RrB0 RBC; lia) ltac:(cbv beta; subst sp1; clear - Hi RBC CLOv LO; lia))). }
        assert (ZEROx : forall i, kt <= i < needed -> mm (wa (Bg + i)) = Some (b8 0)) by (intros i Hi; exfalso; subst kt; clear - Hi CMP; lia).
        assert (WRNx : wr_at rsegs mm Bg needed).
        { subst mm. apply (wr_at_unmaps_other rsegs m2' _ _ Ha Hn Han); [| clear; lia]. eapply wr_at_sub; [exact W2| clear; lia| clear - CMP; lia]. }
        assert (AGMx : forall x, 0 <= x < 2^64 -> ~ (Bg <= x < Bg + OL) -> ~ (Bg <= x < Bg + needed) -> ~ (lo <= x < sp1) -> mm (wa x) = m1 (wa x)).
        { intros x Hx N1 N2 N3. apply (proj1 (PEM0 x Hx ltac:(cbv beta; subst sp1; clear - N1 N3 LO CLOv ND4096; lia))). }
        assert (WMMx : forall x, 0 <= x < 2^64 -> ~ (Bg <= x < Bg + OL) -> ~ (Bg <= x < Bg + needed) -> wview rsegs m1 (wa x) <> None -> wview rsegs mm (wa x) <> None).
        { intros x Hx N1 N2 W. apply (WV (wa x) (or_intror (WM _ W)) mm); [apply OUT; rewrite wa_unsigned by exact Hx; clear - N1 ND4096; lia| exact W]. }

        eapply implM_evt.
        { step. step. step. lazymatch goal with |- evt _ ?P ?ms => unify P (fun ms1 : machine_state => ms1 = ms) end. apply evt_done. reflexivity. }
        cbv beta. intros ms'' ->.
        eapply (implM_bind rsegs _ _ _ (fun _ s'' ms'' => POST (Some p) s'' ms'')); [| intros [] s'' ms'' H'; apply implM_ret; apply evt_done; exact H'].
        apply implM_upd. rewrite Hst.
        exact (remap_tail ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 mm s LB LB0 p A old n lo B errv oldbs st g bg idx r off Bg
                 PERM Hst RMR HBL AR Hin0 SL HM Hr Kr FC Ec CB HA Hoff FIT HO B0 BG16 Hidx SPAN RB0 K3 FRmm ST' MI' ERRmm AUXmm PRES1 OLDB OLEN SB CLO LOr TP HN SC RC
                 RrB0 RBAL NCEILx RFRx DISJx COPYx ZEROx WRNx AGMx WMMx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
      *
        assert (OLT : OL < needed) by (clear - CMP NEQ; lia).
        destruct (GROW CMP) as [NCEIL' RFA]. pose proof NCEIL' as NCEILv. pose_ceil.
        set (mm := apply_zeros m2' [(wa (Bg + OL), Z_to_bv 64 (needed - OL))]) in *.
        assert (Ha : 0 <= Bg + OL < 2^64) by (clear - RrB0 RBC OL4096; lia).
        assert (Hn : 0 <= needed - OL < 2^64) by (clear - OLT ND62 OL4096; lia).
        assert (Han : Bg + OL + (needed - OL) <= 2^64) by (clear - RrB0 NCEILv; lia).
        assert (IMGx : Bg + needed <= 0x10000 \/ 0x88000 <= Bg).
        { pose proof (AVX _ _ RFA ltac:(clear - OLT; lia)) as X. clear - X DRr OL4096 OLT. lia. }
        assert (OUT : forall x : word, (bv_unsigned x < Bg + OL \/ Bg + needed <= bv_unsigned x) -> mm x = m2' x).
        { intros x Hx. subst mm. apply (zeros_outside m2' _ _ Ha Hn Han). clear - Hx. lia. }
        assert (FRmm : rw_cells rsegs mm sp1 [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
        { subst mm. apply (rw_cells_zeros_other rsegs m2' _ _ Ha Hn Han _ _ FR2'). cbn [cells_size csize Nat.add Z.of_nat]. subst sp1. clear - NCEILv CLOv LO. lia. }
        assert (ERRmm : rw_cells rsegs mm (errno_addr tp) [C4 errv]).
        { subst mm. apply (rw_cells_zeros_other rsegs m2' _ _ Ha Hn Han _ _ ERR2). rewrite ETP. cbn [cells_size csize Nat.add Z.of_nat]. clear - IMGx OL4096; lia. }
        assert (PEM0 : rpres_except (fun x => (Bg + OL <= x < Bg + needed) \/ (sp1 - 112 <= x < sp1)) m1 mm).
        { intros x Hx NC. assert (E1 : mm (wa x) = m2' (wa x)) by (apply OUT; rewrite wa_unsigned by exact Hx; clear - NC ND4096; lia).
          destruct (PE12 x Hx ltac:(cbv beta; clear - NC; tauto)) as [E2 W2']. split; [rewrite E1; exact E2|]. intros W. apply (WV (wa x) (or_introl E2) mm E1 W). }
        assert (AUXmm : rauxv_ok mm B).
        { eapply rauxv_ok_pres_B; [exact AUX1| exact PEM0| cbv beta; intros x Hx; subst sp1; clear - Hx SB NCEILv CLOv LO; lia| cbv beta; unfold RAUXV_CELL; intros x Hx; subst sp1; clear - Hx IMGx OL4096 ND4096 CLOv LO; lia]. }
        assert (RFRx : ranges_free ref_reserved Bg needed = true) by (apply rreserved_free_intro; [clear - RrB0; lia| exact IMGx]).
        assert (LRPOS : forall q rq, s_regions st !! q = Some rq -> let '(b2, l2) := region_live_range rq in 0 < l2).
        { intros q rq Hq. destruct (ir_shape _ _ _ IR _ _ Hq) as (_ & _ & LEN & _ & _ & MK). pose proof (round_up_pg_ge (r_len rq)) as UP.
          unfold region_live_range, is_metakind in *. destruct (r_kind rq); unfold PGSZ in *;
            first [specialize (MK (or_introl eq_refl)); clear - LEN MK UP; lia| specialize (MK (or_intror eq_refl)); clear - LEN MK UP; lia| clear - LEN UP; lia]. }
        assert (DISJx : forall rid2 r2, s_regions st !! rid2 = Some r2 -> rid2 <> fst bg -> let '(b2, l2) := region_live_range r2 in Bg + needed <= b2 \/ b2 + l2 <= Bg).
        { intros rid2 r2 H2 NE2. specialize (DISJo rid2 r2 H2 NE2). specialize (LRPOS rid2 r2 H2).
          pose proof (In_live_ranges_except (strip st) (fst c) rid2 r2 H2 ltac:(rewrite FC; exact NE2)) as IN2.
          destruct (region_live_range r2) as [b2 l2]. pose proof (ranges_free_In _ _ _ _ _ RFA IN2) as D2. clear - DISJo LRPOS D2 OLT. lia. }
        assert (COPYx : forall i, 0 <= i < kt -> mm (wa (Bg + i)) = m1 (wa (Bg + i))).
        { intros i Hi. subst kt. rewrite OUT by (rewrite wa_unsigned by (clear - Hi RrB0 RBC ND4096; lia); clear - Hi ND4096; lia).
          apply (proj1 (PE12 (Bg + i) ltac:(clear - Hi RrB0 RBC; lia) ltac:(cbv beta; subst sp1; clear - Hi RBC CLOv LO; lia))). }
        assert (ZEROx : forall i, kt <= i < needed -> mm (wa (Bg + i)) = Some (b8 0)).
        { intros i Hi. subst kt mm. unfold b8. apply (zeros_inside m2' _ _ Ha Hn Han). rewrite wa_unsigned by (clear - Hi RrB0 NCEILv OL4096; lia). clear - Hi OLT; lia. }
        assert (WRNx : wr_at rsegs mm Bg needed).
        { replace needed with (OL + (needed - OL)) by (clear; lia). subst mm. apply wr_at_app; [| apply (wr_at_zeros_new rsegs m2' _ _ Ha Hn Han)| clear - OL4096; lia| clear - OLT; lia].
          apply (wr_at_zeros rsegs m2' _ _ Ha Hn Han). exact W2. }
        assert (AGMx : forall x, 0 <= x < 2^64 -> ~ (Bg <= x < Bg + OL) -> ~ (Bg <= x < Bg + needed) -> ~ (lo <= x < sp1) -> mm (wa x) = m1 (wa x)).
        { intros x Hx N1 N2 N3. apply (proj1 (PEM0 x Hx ltac:(cbv beta; subst sp1; clear - N2 N3 LO CLOv OL4096; lia))). }
        assert (WMMx : forall x, 0 <= x < 2^64 -> ~ (Bg <= x < Bg + OL) -> ~ (Bg <= x < Bg + needed) -> wview rsegs m1 (wa x) <> None -> wview rsegs mm (wa x) <> None).
        { intros x Hx N1 N2 W. apply (WV (wa x) (or_intror (WM _ W)) mm); [apply OUT; rewrite wa_unsigned by exact Hx; clear - N2 OL4096 ND4096; lia| exact W]. }

        eapply implM_evt.
        { step. step. step. lazymatch goal with |- evt _ ?P ?ms => unify P (fun ms1 : machine_state => ms1 = ms) end. apply evt_done. reflexivity. }
        cbv beta. intros ms'' ->.
        eapply (implM_bind rsegs _ _ _ (fun _ s'' ms'' => POST (Some p) s'' ms'')); [| intros [] s'' ms'' H'; apply implM_ret; apply evt_done; exact H'].
        apply implM_upd. rewrite Hst.
        exact (remap_tail ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 mm s LB LB0 p A old n lo B errv oldbs st g bg idx r off Bg
                 PERM Hst RMR HBL AR Hin0 SL HM Hr Kr FC Ec CB HA Hoff FIT HO B0 BG16 Hidx SPAN RB0 K3 FRmm ST' MI' ERRmm AUXmm PRES1 OLDB OLEN SB CLO LOr TP HN SC RC
                 RrB0 RBAL NCEIL' RFRx DISJx COPYx ZEROx WRNx AGMx WMMx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    +
      destruct PO as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m2' & -> & MU & WM & MI2 & MI' & ST' & ERR2 & (NBne & NBA' & NB0' & NCEIL' & RFA & OLT)).
      rewrite SP1 in MU, ST'. pose proof NCEIL' as NCEILv. pose_ceil.
      replace (ret_pc (Z_to_bv 64 0x49cf4)) with (Z_to_bv 64 0x49cf4) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      assert (PE12 : rpres_except (fun x => sp1 - 112 <= x < sp1) m1 m2').
      { eapply rpres_except_of_munch; [exact MU| exact WM|]. intros x Hx NC. cbn [outside]. clear - NC. repeat split; lia. }
      assert (FR2' : rw_cells rsegs m2' sp1 [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply rpres_except_rw_cells; [exact PE12| exact FR|]. cbn [cells_size csize Nat.add Z.of_nat]. cbv beta. intros x Hx. clear - Hx. lia. }
      assert (W2 : wr_at rsegs m2' Bg OL).
      { eapply rpres_except_wr_at; [exact PE12| exact WRr|]. cbv beta. intros x Hx. subst sp1. clear - Hx RBC CLOv LO. lia. }
      assert (WV : forall x : word, m2' x = m1 x \/ wview rsegs m2' x <> None -> forall mx : mem, mx x = m2' x -> wview rsegs m1 x <> None -> wview rsegs mx x <> None).
      { intros x Hx mx Ex W. unfold wview in *. rewrite Ex. destruct Hx as [E1|W1]; [rewrite E1; exact W| exact W1]. }
      assert (RFRx : ranges_free ref_reserved nb needed = true).
      { unfold live_ranges in RFA. pose proof (ranges_free_app_l _ _ _ _ RFA) as X. change (s_reserved (strip st)) with (s_reserved st) in X. rewrite Hres in X. exact X. }
      pose proof (rreserved_disjoint1 _ _ RFRx ltac:(clear - ND4096; lia)) as DRn.
      unfold rmremap_move_mem in MI', ST' |- *.
      set (mz := apply_zeros (apply_unmaps m2' [(wa Bg, Z_to_bv 64 OL)]) [(wa (nb + OL), Z_to_bv 64 (needed - OL))]) in *.
      set (mm := apply_copies m2' mz [ {| copy_src := wa Bg; copy_dst := Z_to_bv 64 nb; copy_len := Z_to_bv 64 OL |} ]) in *.
      assert (Hua : 0 <= Bg < 2^64) by (clear - RrB0 RBC OL4096; lia). assert (Hun : 0 <= OL < 2^64) by (clear - OL4096 RBC RrB0; lia). assert (Huan : Bg + OL <= 2^64) by (clear - RBC; lia).
      assert (Hza : 0 <= nb + OL < 2^64) by (clear - NB0' NCEILv OL4096 OLT; lia). assert (Hzn : 0 <= needed - OL < 2^64) by (clear - OLT ND62 OL4096; lia).
      assert (Hzan : nb + OL + (needed - OL) <= 2^64) by (clear - NCEILv; lia).
      assert (Hcs : 0 <= Bg /\ Bg + OL <= 2^64) by (clear - RrB0 RBC; lia). assert (Hcd : 0 <= nb /\ nb + OL <= 2^64) by (clear - NB0' NCEILv OLT; lia).
      assert (Hcl : 0 < OL < 2^64) by (clear - OL4096 RBC RrB0; lia).
      assert (OUTz : forall x : word, (bv_unsigned x < Bg \/ Bg + OL <= bv_unsigned x) -> (bv_unsigned x < nb + OL \/ nb + needed <= bv_unsigned x) -> mz x = m2' x).
      { intros x H1 H2. subst mz. rewrite (zeros_outside _ _ _ Hza Hzn Hzan) by (clear - H2; lia). apply (unmaps_outside m2' _ _ Hua Hun Huan). exact H1. }
      assert (OUT : forall x : word, (bv_unsigned x < Bg \/ Bg + OL <= bv_unsigned x) -> (bv_unsigned x < nb \/ nb + needed <= bv_unsigned x) -> mm x = m2' x).
      { intros x H1 H2. subst mm. rewrite (copies_outside m2' mz Bg nb OL Hcs Hcd Hcl) by (clear - H2 OLT; lia). apply OUTz; [exact H1| clear - H2 OL4096; lia]. }
      assert (FRmm : rw_cells rsegs mm sp1 [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { subst mm mz. apply (rw_cells_copies_other rsegs m2' _ Bg nb OL Hcs Hcd Hcl); [| cbn [cells_size csize Nat.add Z.of_nat]; subst sp1; clear - NCEILv OLT CLOv LO; lia].
        apply (rw_cells_zeros_other rsegs _ _ _ Hza Hzn Hzan); [| cbn [cells_size csize Nat.add Z.of_nat]; subst sp1; clear - NCEILv CLOv LO; lia].
        apply (rw_cells_unmaps_other rsegs m2' _ _ Hua Hun Huan _ _ FR2'). cbn [cells_size csize Nat.add Z.of_nat]. subst sp1. clear - RBC CLOv LO. lia. }
      assert (ERRmm : rw_cells rsegs mm (errno_addr tp) [C4 errv]).
      { subst mm mz. rewrite ETP. apply (rw_cells_copies_other rsegs m2' _ Bg nb OL Hcs Hcd Hcl); [| cbn [cells_size csize Nat.add Z.of_nat]; clear - DRn OL4096 OLT; lia].
        apply (rw_cells_zeros_other rsegs _ _ _ Hza Hzn Hzan); [| cbn [cells_size csize Nat.add Z.of_nat]; clear - DRn OL4096 OLT; lia].
        rewrite <- ETP. apply (rw_cells_unmaps_other rsegs m2' _ _ Hua Hun Huan _ _ ERR2). rewrite ETP. cbn [cells_size csize Nat.add Z.of_nat]. clear - DRr OL4096; lia. }
      assert (PEM0 : rpres_except (fun x => (Bg <= x < Bg + OL) \/ (nb <= x < nb + needed) \/ (sp1 - 112 <= x < sp1)) m1 mm).
      { intros x Hx NC. assert (E1 : mm (wa x) = m2' (wa x)) by (apply OUT; rewrite wa_unsigned by exact Hx; clear - NC ND4096; lia).
        destruct (PE12 x Hx ltac:(cbv beta; clear - NC; tauto)) as [E2 W2']. split; [rewrite E1; exact E2|]. intros W. apply (WV (wa x) (or_introl E2) mm E1 W). }
      assert (AUXmm : rauxv_ok mm B).
      { eapply rauxv_ok_pres_B; [exact AUX1| exact PEM0| cbv beta; intros x Hx; subst sp1; clear - Hx SB NCEILv RBC CLOv LO; lia| cbv beta; unfold RAUXV_CELL; intros x Hx; subst sp1; clear - Hx DRr DRn OL4096 ND4096 CLOv LO; lia]. }
      assert (DISJx : forall rid2 r2, s_regions st !! rid2 = Some r2 -> rid2 <> fst bg -> let '(b2, l2) := region_live_range r2 in nb + needed <= b2 \/ b2 + l2 <= nb).
      { intros rid2 r2 H2 NE2. pose proof (In_live_ranges (strip st) rid2 r2 H2) as IN2.
        destruct (region_live_range r2) as [b2 l2]. exact (ranges_free_In _ _ _ _ _ RFA IN2). }
      assert (COPYx : forall i, 0 <= i < kt -> mm (wa (nb + i)) = m1 (wa (Bg + i))).
      { intros i Hi. subst kt mm. rewrite (copies_inside m2' mz Bg nb OL Hcs Hcd Hcl) by (clear - Hi; lia).
        apply (proj1 (PE12 (Bg + i) ltac:(clear - Hi RrB0 RBC; lia) ltac:(cbv beta; subst sp1; clear - Hi RBC CLOv LO; lia))). }
      assert (ZEROx : forall i, kt <= i < needed -> mm (wa (nb + i)) = Some (b8 0)).
      { intros i Hi. subst kt mm. unfold b8. rewrite (copies_outside m2' mz Bg nb OL Hcs Hcd Hcl) by (rewrite wa_unsigned by (clear - Hi NB0' NCEILv OL4096; lia); clear - Hi; lia).
        subst mz. apply (zeros_inside _ _ _ Hza Hzn Hzan). rewrite wa_unsigned by (clear - Hi NB0' NCEILv OL4096; lia). clear - Hi OLT; lia. }
      assert (WRNx : wr_at rsegs mm nb needed).
      { replace needed with (OL + (needed - OL)) by (clear; lia). apply wr_at_app; [| | clear - OL4096; lia| clear - OLT; lia].
        - split; [clear - NB0'; lia|]. split; [clear - NCEILv OLT; lia|]. intros i Hi. subst mm.
          rewrite ref_wview_overlay by (rewrite wa_unsigned by (clear - Hi NB0' NCEILv OLT; lia); clear - Hi DRn OLT; lia).
          rewrite (copies_inside m2' mz Bg nb OL Hcs Hcd Hcl i Hi).
          destruct W2 as (_ & _ & W2i). specialize (W2i i Hi). rewrite ref_wview_overlay in W2i by (rewrite wa_unsigned by (clear - Hi RrB0 RBC; lia); clear - Hi DRr; lia). exact W2i.
        - subst mm. apply (wr_at_copies_other rsegs m2' mz Bg nb OL Hcs Hcd Hcl); [| clear; lia]. subst mz. apply (wr_at_zeros_new rsegs _ _ _ Hza Hzn Hzan). }
      assert (AGMx : forall x, 0 <= x < 2^64 -> ~ (Bg <= x < Bg + OL) -> ~ (nb <= x < nb + needed) -> ~ (lo <= x < sp1) -> mm (wa x) = m1 (wa x)).
      { intros x Hx N1 N2 N3. apply (proj1 (PEM0 x Hx ltac:(cbv beta; subst sp1; clear - N1 N2 N3 LO CLOv; lia))). }
      assert (WMMx : forall x, 0 <= x < 2^64 -> ~ (Bg <= x < Bg + OL) -> ~ (nb <= x < nb + needed) -> wview rsegs m1 (wa x) <> None -> wview rsegs mm (wa x) <> None).
      { intros x Hx N1 N2 W. apply (WV (wa x) (or_intror (WM _ W)) mm); [apply OUT; rewrite wa_unsigned by exact Hx; [clear - N1; lia| clear - N2; lia]| exact W]. }

      eapply implM_evt.
      { step. step. step. lazymatch goal with |- evt _ ?P ?ms => unify P (fun ms1 : machine_state => ms1 = ms) end. apply evt_done. reflexivity. }
      cbv beta. intros ms'' ->.
      eapply (implM_bind rsegs _ _ _ (fun _ s'' ms'' => POST (Some p) s'' ms'')); [| intros [] s'' ms'' H'; apply implM_ret; apply evt_done; exact H'].
      apply implM_upd. rewrite Hst.
      exact (remap_tail ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 mm s LB LB0 p A old n lo B errv oldbs st g bg idx r off nb
               PERM Hst RMR HBL AR Hin0 SL HM Hr Kr FC Ec CB HA Hoff FIT HO B0 BG16 Hidx SPAN RB0 K3 FRmm ST' MI' ERRmm AUXmm PRES1 OLDB OLEN SB CLO LOr TP HN SC RC
               NB0' NBA' NCEIL' RFRx DISJx COPYx ZEROx WRNx AGMx WMMx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
Qed.
End P.

End CEIL.

From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Ubsan.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Image OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.SysCopy OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Decode.
Import OSSVerify.msgpack_c.unpack_pack_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_F_malloc_free OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_F_malloc_fast OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_F_malloc_enframe OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_F_free OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_F_free_spec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocKit_AB OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocKit_A OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocBlocks OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocHINV OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocFacts_B OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_Malloc_iface.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Malloc OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MallocCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MallocInv OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Arith OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Inv OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Kit OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Read OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Geom OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Pres2 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Cnt OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_WFree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_WGroup OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MI_Realloc2 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Realloc.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Monad OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Prog OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.ProgR OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_Realloc OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_Realloc2 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocFacts_Bpres OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocKit_A2.
Import RMallocRep.TwinB RMallocTree.TwinB RMallocKit_A.TwinB RMallocKit_B.TwinB RMallocKit_A2.TwinB RMalloc_iface.TwinB RMalloc_ifaceP.TwinB RF_free.TwinB RF_free_spec.TwinB RRealloc_iface.TwinB RF_realloc_inpl.TwinB RF_realloc_dec.TwinB RF_mremap.TwinB RF_realloc_rrep.TwinB RF_realloc_inplS.TwinB RF_realloc_moveS.TwinB RMemEq.TwinB RF_enframe.TwinB.

Set Keyed Unification.
Import ListNotations.
Import ITree.Exc.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.CeilLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Definition remap_arm_stmt : Prop :=
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m1 : mem)
    (s : PState) (LB LB0 : list block) (p : bptr) (A old n lo B : Z) (errv : word) (oldbs : list byte)
    (st : mstate) (g bg : aptr) (idx : Z) (r : region) (off : Z),
  let c : cptr := fst p in
  let mr := get_meta_rec st g in
  let stride := get_stride mr in
  let Bg := conc st bg in
  let E := Bg + 16 + stride * (idx + 1) - 4 in
  let sp1 := bv_unsigned sp - 64 in
  let POST := rrealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p A old n lo B oldbs m in
  rmalloc_impl_stmt -> rfree_impl_stmt ->
  Permutation LB0 LB -> strip st = ps_m s -> rmrep st m1 -> brk_link st (ps_brk s) ->
  AREACH_from ref_reserved st LB0 -> In (p, A, old) LB0 ->
  s_slots st !! c = Some (g, idx) -> m_mem mr = Some bg -> s_regions st !! (fst bg) = Some r -> r_kind r = RKGroup ->
  fst c = fst bg -> c = (fst bg, snd bg + UNIT + stride * idx) -> Bg = r_base r + snd bg ->
  A = conc st c + UNIT * off -> 0 <= off <= 255 -> UNIT * off + old <= stride - IB -> 0 <= old ->
  UNIT <= stride -> stride mod UNIT = 0 -> 0 <= snd bg -> snd bg mod UNIT = 0 -> 0 <= idx <= m_last_idx mr -> m_last_idx mr <= 31 ->
  snd bg + UNIT + stride * (idx + 1) <= round_up_pg (r_len r) -> r_base r + round_up_pg (r_len r) <= alloc_ceiling -> 0 <= r_base r ->
  (m_sizeclass mr < 48 -> stride < 2 ^ 20) -> (48 <= m_sizeclass mr -> m_sizeclass mr = 63) ->
  known st (fst c, snd c + UNIT * off - 3) (idx + 32 * Z.min (snd c + stride - IB - (snd c + UNIT * off) - old) 5) ->
  rw_cells rsegs m1 sp1 [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m1 lo sp1 -> mem_inv rsegs m1 -> rw_cells rsegs m1 (errno_addr tp) [C4 errv] ->
  rauxv_ok m1 B -> rpres_except (fun a => (lo <= a < bv_unsigned sp) \/ (RERRNO <= a < RERRNO + 4)) m m1 ->
  bytes_at rsegs m A oldbs -> Z.of_nat (length oldbs) = old ->
  bv_unsigned sp <= B -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RREALLOC_STACK ->
  tp = Z_to_bv 64 RATP -> 0 <= n < 2^48 -> True ->
  forall (y7 a5v y28 : word),
  MMAP_THRESHOLD <= n -> m_sizeclass mr = 63 ->
  implM rsegs (realloc_body p A n (ps_m s)) s POST
      (MS (mkR ra (Z_to_bv 64 sp1) gp tp (Z_to_bv 64 E) (Z_to_bv 64 (Bg + stride * idx + 16)) y7 s0 (wz (conc st g)) (Z_to_bv 64 A) (Z_to_bv 64 n)
               (wz Bg) (Z_to_bv 64 (m_sizeclass mr)) (wz (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr)) a5v
               (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - A)) (Z_to_bv 64 (A + old)) s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 t4 t5 t6)
          F (Z_to_bv 64 0x4b4b4) fc None m1 (seg_rom rsegs)).

Lemma implM_of_enode {A} (n0 : node) (dec : resp -> option A) (s : PState) (Q : A -> PState -> machine_state -> Prop) ms :
  impl rsegs (at_node rsegs) (enode n0 dec) (epost (fun a ms' => Q a s ms')) ms -> implM rsegs (msys n0 dec) s Q ms.
Proof.
  intros H. unfold implM, msys, enode in *. cbn [impl] in *. eapply evt_mono; [exact H|].
  intros ms1 [AT K]. split; [exact AT|]. intros rsp. specialize (K rsp). destruct (dec rsp) as [a|]; cbn in *; exact K.
Qed.

Lemma rptrs_remap st LB (m : mem) rid r (g bg : aptr) ai :
  CINV st LB -> rmrep st m ->
  (s_regions st) !! rid = Some r -> r_kind r = RKGroup ->
  (s_groups st) !! bg = Some (mkGhdr (Some g) ai) ->
  (forall b gh, (s_groups st) !! b = Some gh -> fst b = rid -> b = bg) ->
  let P := fun q : N => q <> rid in
  optr_in P (c_free_meta_head (ctx st)) /\ optr_in P (c_avail_meta (ctx st)) /\ optr_in P (c_meta_area_head (ctx st))
  /\ optr_in P (c_meta_area_tail (ctx st)) /\ optr_in P (c_avail_meta_areas (ctx st))
  /\ (forall sc, optr_in P (active st sc))
  /\ match c_brk (ctx st) with BrkLive q _ => P q | _ => True end
  /\ (forall g', optr_in P (m_prev (get_meta_rec st g')) /\ optr_in P (m_next (get_meta_rec st g')) /\ (g' <> g -> optr_in P (m_mem (get_meta_rec st g'))))
  /\ (forall a ar, (s_areas st) !! a = Some ar -> P (fst a) /\ optr_in P (a_next ar))
  /\ (forall b gh, (s_groups st) !! b = Some gh -> optr_in P (g_meta gh)).
Proof.
  intros C MR Hr Kr Hg ONLYG P. pose proof (KINV_of_CINV _ _ C) as K. destruct (ci_mp _ _ C) as (M1 & M2 & M3 & M4 & M5).
  pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
  assert (MSr : forall q, meta_slot st q -> fst q <> rid).
  { intros q (a & ar & k & Ha & Hk & ->) E. cbn in E. destruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _).
    rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr). }
  assert (NGr : forall p, ng_ptr st p -> optr_in P p).
  { intros [q|]; cbn; [| exact (fun _ => I)]. intros (r' & Hr' & NK) E. rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. exact (NK Kr). }
  assert (OM : forall p, (forall q, p = Some q -> meta_slot st q) -> optr_in P p).
  { intros [q|] H; cbn; [apply MSr; apply H; reflexivity| exact I]. }
  pose proof (ki_links _ _ _ K) as [LN LP LNN LS].
  split; [apply OM; intros h Hh; exact (proj1 (kinv_free_head st LB 0 h K Hh))|].
  split; [apply NGr; exact M1|]. split; [apply NGr; exact M2|]. split; [apply NGr; exact M3|]. split; [apply NGr; exact M4|].
  split; [intros sc; apply OM; intros a Ha; exact (proj1 (proj2 (kinv_active st LB 0 sc a K Ha)))|].
  split.
  { destruct (c_brk (ctx st)) as [| |brid boff] eqn:HB; try exact I.
    intros E. destruct (ki_bk _ _ _ K brid boff HB) as (r' & Hr' & K'). rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. rewrite Kr in K'. discriminate. }
  split.
  { intros g'. split; [apply OM; intros pv Hp; exact (proj2 (LP g' pv Hp))|]. split; [apply OM; intros nx Hn; exact (proj2 (LN g' nx Hn))|].
    intros NE. destruct (m_mem (get_meta_rec st g')) as [b|] eqn:MB; cbn; [| exact I]. intros E.
    pose proof (ci_memh _ _ C g' b MB) as [ai' Hb']. pose proof (ONLYG b _ Hb' E) as ->. rewrite Hg in Hb'. apply NE. congruence. }
  split.
  { intros a ar Ha. split; [| apply NGr; exact (M5 a ar Ha)].
    intros E. destruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _). rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr). }
  intros b gh Hb. destruct (ki_grps _ _ _ K b gh Hb) as (g' & Hg' & _). rewrite Hg'. cbn. apply MSr.
  assert (HB : A_MallocFacts_B.hosts st b g') by (exists (g_active_idx gh); rewrite Hb; destruct gh; cbn in Hg' |- *; subst; reflexivity).
  exact (go_slot _ _ _ (ki_gmetas _ _ _ K b g' HB)).
Qed.

Lemma ticks_ok_trim_shadow st rid k : ticks_ok st -> ticks_ok (trim_shadow rid k st).
Proof.
  intros [T1 T2]. unfold trim_shadow, upd_shadow. split; cbn [s_shadow s_tick set_shadow].
  - intros q sh u hl ch Hs Hu Hin. destruct (N.eq_dec q rid) as [->|NE].
    + rewrite lookup_insert_eq in Hs. injection Hs as <-. cbn in Hu.
      unfold get_shadow in Hu. destruct (s_shadow st !! rid) as [sh0|] eqn:E; cbn in Hu; [eapply T1; eauto| rewrite lookup_empty in Hu; discriminate].
    + rewrite lookup_insert_ne in Hs by congruence. eapply T1; eauto.
  - intros q sh pg t Hs Hp. destruct (N.eq_dec q rid) as [->|NE].
    + rewrite lookup_insert_eq in Hs. injection Hs as <-. cbn in Hp.
      unfold get_shadow in Hp. destruct (s_shadow st !! rid) as [sh0|] eqn:E; cbn in Hp; [eapply T2; eauto| rewrite lookup_empty in Hp; discriminate].
    + rewrite lookup_insert_ne in Hs by congruence. eapply T2; eauto.
Qed.

Lemma rinplace_pres (mx : mem) (P E n b3 lo hi : Z) :
  lo <= P - 3 -> P + n <= E -> E + 1 <= hi -> 0 <= lo -> hi <= 2^64 -> 0 <= n -> 3 <= P ->
  rpres_except (fun x => x = P - 3 \/ P + n <= x < hi) mx (rinplace_mem (write_to_mem mx (wa E) [b8 0]) P E n b3).
Proof.
  intros H1 H2 H3 H4 H5 H6 H7. unfold rinplace_mem. cbv zeta.
  assert (L4 : forall w, length (le4 w) = 4%nat) by (intros; reflexivity).
  set (rr := E - P - n) in *.
  assert (P30 : rpres_except (fun x => x = P - 3 \/ P + n <= x < hi) mx (write_to_mem mx (wa E) [b8 0])).
  { apply rpres_write; [apply rpres_except_refl| lia| cbn; lia| cbn; intros; right; lia]. }
  set (mw := write_to_mem mx (wa E) [b8 0]) in *. clearbody mw.
  set (m3' := if rr =? 0 then _ else _).
  assert (P3 : rpres_except (fun x => x = P - 3 \/ P + n <= x < hi) mx m3').
  { subst m3'. destruct (Z.eqb_spec rr 0); [exact P30|]. apply rpres_write; [exact P30| lia| cbn; lia| cbn; intros; right; lia]. }
  clearbody m3'.
  set (m4 := if 5 <=? rr then _ else _).
  assert (P4 : rpres_except (fun x => x = P - 3 \/ P + n <= x < hi) mx (fst m4) /\ 0 <= snd m4 <= 5).
  { subst m4. destruct (Z.leb_spec 5 rr); cbn [fst snd].
    - split; [| lia]. apply rpres_write; [| lia| rewrite L4; lia| rewrite L4; intros; right; lia].
      apply rpres_write; [exact P3| lia| cbn; lia| cbn; intros; right; lia].
    - split; [exact P3| lia]. }
  clearbody m4. destruct m4 as [m4 r5]. cbn [fst snd] in P4 |- *. destruct P4 as [P4 _].
  apply rpres_write; [exact P4| lia| cbn; lia| cbn; intros; left; lia].
Qed.

Lemma rreserved_free_intro b n : 0 <= b -> (b + n <= 0x10000 \/ 0x8a000 <= b) -> ranges_free ref_reserved b n = true.
Proof.
  intros Hb H. unfold ref_reserved. apply ranges_free_intro. intros b' k Hin.
  cbn in Hin. destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-; lia.
Qed.

Lemma ranges_free_app_l l1 l2 a n : ranges_free (l1 ++ l2) a n = true -> ranges_free l1 a n = true.
Proof. intros H. apply ranges_free_intro. intros b k Hin. eapply ranges_free_In; [exact H|]. apply in_or_app. left. exact Hin. Qed.

Lemma In_live_ranges_except cs rid q rq : (s_regions cs) !! q = Some rq -> q <> rid -> In (region_live_range rq) (live_ranges_except cs rid).
Proof.
  intros Hq NE. unfold live_ranges_except. apply in_or_app. right. apply in_map_iff. exists (q, rq). split; [reflexivity|].
  apply (proj1 (list_elem_of_In _ _)). apply (proj2 (list_elem_of_filter _ _ _)).
  split; [cbn; destruct (N.eqb_spec q rid); [congruence| exact I]| apply elem_of_map_to_list; exact Hq].
Qed.

Lemma wr_at_app m a n1 n2 : wr_at rsegs m a n1 -> wr_at rsegs m (a + n1) n2 -> 0 <= n1 -> 0 <= n2 -> wr_at rsegs m a (n1 + n2).
Proof.
  intros (A0 & A1 & W1) (B0 & B1 & W2) H1 H2. split; [exact A0|]. split; [lia|]. intros i Hi.
  destruct (Z.lt_ge_cases i n1) as [LT|GE]; [apply W1; lia|]. replace (a + i) with (a + n1 + (i - n1)) by lia. apply W2. lia.
Qed.

Definition rtail_post (sp gp tp s7 s8 s9 s10 s11 t4 t5 t6 rav s0v s1v s2v s3v s4v s5v s6v gw w0 w1 w2 : word) (w3 w4 : word)
   (F : bvmap 5 word) (fc : bv 32) (m : mem) (G NB needed n off b3 : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 m2 m',
    ms' = MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + 64)) gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 (NB + 16 + 16 * off)) a1 a2 a3 a4 a5 a6 a7
                  s2v s3v s4v s5v s6v s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc rav) fc None m' (seg_rom rsegs)
    /\ m' = rinplace_mem (write_to_mem m2 (wa (NB + needed - 4)) [b8 0]) (NB + 16 + 16 * off) (NB + needed - 4) n b3
    /\ munch [(G + 16, G + 24); (G + 32, G + 40)] m m2 /\ wmono rsegs m m2
    /\ mem_inv rsegs m'
    /\ rw_cells rsegs m2 (bv_unsigned gw) [C8 w0; C8 w1; C8 (wz NB); C4 w3; C4 w4; C8 (wz (4064 + needed))]
    /\ rw_cells rsegs m' (bv_unsigned sp) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].

Section TAIL_W.
Variables (ra1 sp gp tp s7 s8 s9 s10 s11 t4 t5 t6 rav s0v s1v s2v s3v s4v s5v s6v gw w0 w1 w2 : word) (w3 w4 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (G NB needed n off mword b3 : Z).
Hypotheses (HGW : bv_unsigned gw = G) (G0 : 0 <= G) (NB0 : 0 < NB) (HN : 0 <= n) (Hoff : 0 <= off) (B3R : 0 <= b3 < 256)
    (NDR : n + 16 * off + 20 <= needed < n + 16 * off + 20 + 4096) (NDA : needed mod 4096 = 0) (ND62 : needed < 2^62)
    (MWM : mword mod 4096 = 4064) (MW64 : 0 <= mword < 2^64)
    (GFR : G + 40 <= NB \/ NB + needed <= G) (GSP : G + 40 <= bv_unsigned sp) (NSP : NB + needed <= bv_unsigned sp) (SPH : bv_unsigned sp + 64 <= 2^64)
    (MM : rw_cells rsegs m (bv_unsigned gw) [C8 w0; C8 w1; C8 w2; C4 w3; C4 w4; C8 (wz mword)])
    (WRN : wr_at rsegs m NB needed) (BK : bytes_at rsegs m (NB + 13 + 16 * off) [b8 b3])
    (FR : rw_cells rsegs m (bv_unsigned sp) [C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav])
    (MI : mem_inv rsegs m).
Let POST := rtail_post sp gp tp s7 s8 s9 s10 s11 t4 t5 t6 rav s0v s1v s2v s3v s4v s5v s6v gw w0 w1 w2 w3 w4 F fc m G NB needed n off b3.

Lemma tail_6c0 : forall (t0v t1v t2v a0v a3v a4v a5v a6v a7v s2 s5 s6 t3v : word),
  evt rsegs POST
      (MS (mkR ra1 sp gp tp t0v t1v t2v (Z_to_bv 64 needed) gw a0v (Z_to_bv 64 n) (Z_to_bv 64 NB)
               a3v a4v a5v a6v a7v s2 (Z_to_bv 64 (16 * off)) (Z_to_bv 64 4095) s5 s6 s7 s8 s9 s10 s11 t3v t4 t5 t6)
          F (Z_to_bv 64 0x4b504) fc None m (seg_rom rsegs)).
Proof.
  intros.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  set (P' := NB + 16 + 16 * off). set (E' := NB + needed - 4).
  assert (EP' : P' = NB + 16 + 16 * off) by reflexivity. assert (EE' : E' = NB + needed - 4) by reflexivity. clearbody P' E'.
  replace (NB + 13 + 16 * off) with (P' - 3) in BK by lia.
  pose proof (munch_refl [(G + 16, G + 24); (G + 32, G + 40)] m) as MU. pose proof (wmono_refl rsegs m) as WM.

  step. step. if_cases K0; zify_cond K0. { exfalso. rewrite ?unsigned_lit in K0 by lia. cbn in K0. lia. } clear K0.

  step. step. rewrite ?(unsigned_lit NB), ?(unsigned_lit (16 * off)) by lia.
  step. rewrite ?(unsigned_lit needed) by lia.
  step. step. step. step. rewrite ?(unsigned_lit n), ?(unsigned_lit (NB + 16 * off + 16)) by lia.
  step. step.

  rewrite (wz_unsigned mword) by exact MW64.
  replace (Z.land mword 4095) with 4064 by (change 4095 with (Z.ones 12); rewrite Z.land_ones by lia; change (2 ^ 12) with 4096; symmetry; exact MWM).
  rewrite (unsigned_lit 4064) by lia. rewrite (unsigned_lit needed) by lia.
  rewrite (StrFun.lor_add' 4064 needed 12) by (change (2^12) with 4096; first [exact NDA| lia]).
  replace (NB + 16 * off + 16) with P' by lia. replace (n + P') with (P' + n) by lia.
  rewrite (unsigned_lit (NB + needed + -4)), (unsigned_lit (P' + n)) by lia.
  rewrite (swrap32_small (NB + needed + -4 - (P' + n))) by lia.
  replace (NB + needed + -4 - (P' + n)) with (E' - P' - n) by lia.
  replace (NB + needed + -4) with E' by lia. replace (NB + needed) with (E' + 4) by lia.

  step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
    rename MU into MU2; unfold munch in MU2; assert (WM2 : id (wmono rsegs m mx)) by exact WM;
    lazymatch goal with H : rw_cells rsegs mx (bv_unsigned gw) ?cs |- _ => assert (MM2 : id (rw_cells rsegs mx (bv_unsigned gw) cs)) by exact H end;
    pose proof (wr_at_store_ok rsegs mx NB needed (needed - 4) 1%nat WRN ltac:(lia) ltac:(lia)) as SO;
    replace (NB + (needed - 4)) with (E' + 4 + -4) in SO by lia; change (wa (E' + 4 + -4)) with (Z_to_bv 64 (E' + 4 + -4)) in SO end.

  step. change (le1 (Z_to_bv 64 0)) with [b8 0]. sdk.
  replace (E' + 4 + -4) with E' in * by lia.
  eapply evt_mono.
  { lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      apply (inpl_6f8 ra1 sp gp tp s7 s8 s9 s10 s11 t4 t5 t6 rav s0v s1v s2v s3v s4v s5v s6v F fc mx P' n E' b3) end;
      try eassumption; try lia.
    lazymatch goal with W : wr_at rsegs ?mx NB needed |- wr_at rsegs ?mx _ _ => eapply wr_at_sub; [exact W| lia| lia] end. }
  intros ms' (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & m' & -> & EM & MI' & FR').
  unfold POST, rtail_post. do 11 eexists.
  lazymatch goal with E3 : ?m3 = write_to_mem ?m2 _ _ |- _ => exists m2, m'; rewrite E3 in EM end.
  split; [rewrite EP'; reflexivity|]. split; [rewrite <- EE', <- EP'; exact EM|].
  split; [exact MU2|]. split; [exact WM2|]. split; [exact MI'|]. split; [| exact FR'].
  exact MM2.
Qed.
End TAIL_W.

Section TAIL.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m m1 mm : mem)
    (s : PState) (LB LB0 : list block) (p : bptr) (A old n lo B : Z) (errv errv2 : word) (oldbs : list byte)
    (st : mstate) (g bg : aptr) (idx : Z) (r : region) (off : Z) (NB : Z).
Let c : cptr := fst p.
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let Bg := conc st bg.
Let E := Bg + 16 + stride * (idx + 1) - 4.
Let sp1 := bv_unsigned sp - 64.
Let OL := m_maplen mr * 4096.
Let needed := remap_needed (UNIT * off) n.
Let kt := Z.min OL needed.
Let mword := m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr.
Let POST := rrealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p A old n lo B oldbs m.
Hypotheses (PERM : Permutation LB0 LB) (Hst : strip st = ps_m s) (RMR : rmrep st m1) (HBL : brk_link st (ps_brk s))
    (AR : AREACH_from ref_reserved st LB0) (Hin0 : In (p, A, old) LB0)
    (SL : s_slots st !! c = Some (g, idx)) (HM : m_mem mr = Some bg) (Hr : s_regions st !! (fst bg) = Some r) (Kr : r_kind r = RKGroup)
    (FC : fst c = fst bg) (Ec : c = (fst bg, snd bg + UNIT + stride * idx)) (CB : Bg = r_base r + snd bg)
    (HA : A = conc st c + UNIT * off) (Hoff : 0 <= off <= 255) (FIT : UNIT * off + old <= stride - IB) (HO : 0 <= old)
    (S16 : UNIT <= stride) (SMOD : stride mod UNIT = 0) (B0 : 0 <= snd bg) (BG16 : snd bg mod UNIT = 0) (Hidx : 0 <= idx <= m_last_idx mr) (LI : m_last_idx mr <= 31)
    (SPAN : snd bg + UNIT + stride * (idx + 1) <= round_up_pg (r_len r)) (RCEIL : r_base r + round_up_pg (r_len r) <= alloc_ceiling) (RB0 : 0 <= r_base r)
    (SC63 : 48 <= m_sizeclass mr -> m_sizeclass mr = 63)
    (K3 : known st (fst c, snd c + UNIT * off - 3) (idx + 32 * Z.min (snd c + stride - IB - (snd c + UNIT * off) - old) 5)).
Hypotheses (FR : rw_cells rsegs mm sp1 [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    (ST1 : stk rsegs mm lo sp1) (MI1 : mem_inv rsegs mm) (ERR1 : rw_cells rsegs mm (errno_addr tp) [C4 errv2])
    (AUX1 : rauxv_ok mm B)
    (PRES1 : rpres_except (fun a => (lo <= a < bv_unsigned sp) \/ (RERRNO <= a < RERRNO + 4)) m m1)
    (OLDB : bytes_at rsegs m A oldbs) (OLEN : Z.of_nat (length oldbs) = old)
    (SB : bv_unsigned sp <= B) (CLO : alloc_ceiling <= lo) (LO : lo <= bv_unsigned sp - RREALLOC_STACK)
    (TP : tp = Z_to_bv 64 RATP) (HN : 0 <= n < 2^48) (THR : MMAP_THRESHOLD <= n) (SC : m_sizeclass mr = 63)
    (RC : realloc_case (strip st) c A n = RcRemap (fst c) g Bg OL needed).

Hypotheses (NB0 : 0 < NB) (NBA : NB mod 4096 = 0) (NCEIL : NB + needed <= alloc_ceiling) (RFR : ranges_free ref_reserved NB needed = true)
    (DISJ : forall rid2 r2, s_regions st !! rid2 = Some r2 -> rid2 <> fst bg -> let '(b2, l2) := region_live_range r2 in NB + needed <= b2 \/ b2 + l2 <= NB)
    (COPY : forall i, 0 <= i < kt -> mm (wa (NB + i)) = m1 (wa (Bg + i)))
    (ZERO : forall i, kt <= i < needed -> mm (wa (NB + i)) = Some (b8 0))
    (WRN : wr_at rsegs mm NB needed)
    (AGM : forall x, 0 <= x < 2^64 -> ~ (Bg <= x < Bg + OL) -> ~ (NB <= x < NB + needed) -> ~ (lo <= x < sp1) -> mm (wa x) = m1 (wa x))
    (WMM : forall x, 0 <= x < 2^64 -> ~ (Bg <= x < Bg + OL) -> ~ (NB <= x < NB + needed) -> wview rsegs m1 (wa x) <> None -> wview rsegs mm (wa x) <> None).

Lemma remap_tail : forall (rax t0v t1v t2v a3v a4v a5v a6v a7v s5v s6v t3v t4v t5v t6v : word),
  evt rsegs (POST (Some p) (set_m (remap_update (ps_m s) (fst c) g NB needed) s))
      (MS (mkR rax (Z_to_bv 64 sp1) gp tp t0v t1v t2v (Z_to_bv 64 needed) (wz (conc st g)) (Z_to_bv 64 A) (Z_to_bv 64 n) (Z_to_bv 64 NB)
               a3v a4v a5v a6v a7v (Z_to_bv 64 (A + old)) (Z_to_bv 64 (16 * off)) (Z_to_bv 64 4095) s5v s6v s7 s8 s9 s10 s11 t3v t4v t5v t6v)
          F (Z_to_bv 64 0x4b504) fc None mm (seg_rom rsegs)).
Proof.
  intros.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold RREALLOC_STACK, RMALLOC_STACK in LO. pose proof CLO as CLOv. pose_ceil. pose proof NCEIL as NCEILv. pose_ceil.
  assert (ETP : bv_unsigned tp + -164 = 429036) by (rewrite TP; unfold RATP; rewrite unsigned_lit by lia; reflexivity).

  destruct (realloc_bf ref_reserved st LB0 p A old AR Hin0 g bg idx SL HM) as (L & LS & BL & off' & ai & a & ar & ka & INV & CR & Hk & HA' & BF).
  change (fst p) with c in HA'. assert (off' = off) as -> by (rewrite HA in HA'; unfold UNIT in HA'; clear - HA'; lia). clear HA'.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as HgB. fold c in HgB.
  pose proof (ig_ok _ _ _ IG _ _ _ HgB) as GO.
  destruct (realloc_region_private ref_reserved st LB0 p A old AR Hin0 g bg idx SL HM SC r Hr) as (RPRIV & ONLYG & SB0 & I0 & L0 & EOL & _).
  change (MR st g) with mr in L0, EOL. fold OL in EOL.
  assert (Ebg : bg = (fst bg, 0)) by (destruct bg; cbn in SB0 |- *; subst; reflexivity).
  assert (HgB0 : s_groups st !! (fst bg, 0) = Some (mkGhdr (Some g) ai)) by (rewrite <- Ebg; exact HgB).
  assert (ONLYG0 : forall b gh, s_groups st !! b = Some gh -> fst b = fst bg -> b = (fst bg, 0)) by (intros b gh Hb Hf; rewrite <- Ebg; exact (ONLYG b gh Hb Hf)).
  assert (HM0 : m_mem mr = Some (fst bg, 0)) by (rewrite HM, <- Ebg; reflexivity).
  pose proof (g_maplen _ _ _ _ _ _ GO) as ML0. change (MR st g) with mr in ML0.
  destruct (g_sc _ _ _ _ _ _ GO) as [[S48 _]|(_ & _ & ML & _)]; [exfalso; change (MR st g) with mr in S48; clear - S48 SC; lia|]. change (MR st g) with mr in ML.
  assert (STR : stride = OL - 16).
  { subst stride OL. unfold get_stride. rewrite L0. cbn [Z.eqb andb]. destruct (Z.eqb_spec (m_maplen mr) 0); [exfalso; exact (ML ltac:(eassumption))| reflexivity]. }
  assert (OL4096 : 4096 <= OL) by (subst OL; clear - ML ML0; lia).
  assert (EBg : Bg = r_base r) by (subst Bg; rewrite CB, SB0; clear; lia).
  assert (Sc16 : snd c = 16) by (rewrite Ec; cbn [snd]; rewrite SB0, I0; unfold UNIT; clear; lia).
  assert (Ec16 : c = (fst bg, 16)) by (rewrite Ec at 1; cbn; f_equal; rewrite SB0, I0; unfold UNIT; clear; lia).
  assert (CC : conc st c = Bg + 16).
  { rewrite (conc_region' st c r) by (rewrite FC; exact Hr). rewrite Sc16, EBg. reflexivity. }
  assert (HAE : A = Bg + 16 + 16 * off) by (rewrite HA, CC; unfold UNIT; clear; lia).
  assert (HE : E = Bg + OL - 4) by (subst E; rewrite I0, STR; clear; lia).
  pose proof (remap_needed_ge (UNIT * off) n ltac:(clear - HN; lia) ltac:(unfold UNIT; clear - Hoff; lia)) as NDR. fold needed in NDR. unfold UNIT, IB in NDR.
  pose proof (remap_needed_pg (UNIT * off) n) as NDA. fold needed in NDA.
  assert (ND62 : needed < 2 ^ 62) by (clear - NDR HN Hoff; lia).
  assert (ND4096 : 4096 <= needed) by (clear - NDR NDA HN Hoff; Z.div_mod_to_equations; lia).
  assert (NDround : round_up_pg needed = needed) by (apply MI_WAMeta.round_up_pg_id; exact NDA).
  assert (KT : 4096 <= kt <= needed /\ kt <= OL) by (subst kt; clear - ND4096 OL4096; lia).
  pose proof RMR as (WF & CX & GL & ARS & GR & SH). pose proof WF as (Hres & WR & DISJr & WA & WG).
  destruct (WR _ _ Hr) as (RrB0 & RBAL & RL0 & RBC & RF). pose_ceil.
  pose proof (round_up_pg_ge (r_len r)) as RUP. rewrite <- EOL in RUP, RBC, RF.
  pose proof (rreserved_disjoint1 _ _ RF ltac:(clear - OL4096; lia)) as DRr. rewrite <- EBg in DRr, RBC, RrB0.
  pose proof (rreserved_disjoint1 _ _ RFR ltac:(clear - ND4096; lia)) as DRn.
  pose proof (g_freeable _ _ _ _ _ _ GO) as FB1. change (MR st g) with mr in FB1.
  assert (EMW : mword = 4064 + OL) by (subst mword OL; rewrite L0, FB1, SC; clear; lia).
  assert (MW64 : 0 <= mword < 2^64) by (rewrite EMW; clear - OL4096 RBC RrB0; lia).
  assert (MWM : mword mod 4096 = 4064).
  { rewrite EMW. subst OL. clear. rewrite Z.mod_add by lia. reflexivity. }
  pose proof (A_MallocFacts_inv3.areach_cinv_proof _ _ AR) as CINV0.
  assert (MSL : meta_slot st g).
  { destruct (bf_area _ _ _ _ _ _ _ _ _ _ _ BF) as (Ha & _ & _ & Hka & Emm). exists a, ar, ka. split; [exact Ha|]. split; [exact Hka| exact Emm]. }
  destruct (rarea_conc st _ _ WF (proj1 (bf_area _ _ _ _ _ _ _ _ _ _ _ BF))) as (rga & Hrga & Cga & Sga0 & Sga1 & SgaL & NKg & RgB0 & RgAL & RgC). pose_ceil.
  assert (HG : conc st g = conc st a + (24 + 40 * ka)).
  { destruct (bf_area _ _ _ _ _ _ _ _ _ _ _ BF) as (Ha & _ & _ & Hka & Emm). rewrite Emm. unfold mslot, AREA_HDR, META_SIZE. apply conc_aadd. rewrite Hrga. eauto. }
  pose proof (proj1 (proj2 (proj2 (proj2 (bf_area _ _ _ _ _ _ _ _ _ _ _ BF))))) as Hka.
  set (G := conc st g) in *.

  assert (DJ' : forall q rq, (s_regions st) !! q = Some rq -> q <> fst bg -> NB + needed <= lr_lo rq \/ r_base rq + round_up_pg (r_len rq) <= NB).
  { intros q rq Hq NE. specialize (DISJ q rq Hq NE). unfold region_live_range in DISJ. unfold lr_lo. destruct (r_kind rq); unfold PGSZ in DISJ; clear - DISJ; lia. }

  assert (NEra : fst a <> fst bg) by (intros E0; rewrite E0, Hr in Hrga; assert (rga = r) by congruence; subst rga; exact (NKg Kr)).
  assert (GFAR : (G + 40 <= Bg \/ Bg + OL <= G) /\ (G + 40 <= NB \/ NB + needed <= G) /\ G + 40 <= alloc_ceiling /\ (0x8a000 <= G \/ G + 40 <= 0x10000)).
  { pose proof (DISJr _ _ _ _ Hrga Hr NEra) as D1. pose proof (DJ' _ _ Hrga NEra) as D2.
    pose proof (rarea_lr_lo st _ _ rga WF (proj1 (bf_area _ _ _ _ _ _ _ _ _ _ _ BF)) Hrga) as LRa. pose proof (lr_lo_group r Kr) as LRr.
    destruct (WR _ _ Hrga) as (_ & _ & _ & _ & RFa). pose proof (rreserved_disjoint1 _ _ RFa ltac:(clear - Sga0 Sga1; lia)) as DRa.
    unfold NSLOTS in Hka. rewrite <- EOL, LRr, <- EBg in D1. pose_ceil. clear - D1 D2 LRa Cga Sga0 Sga1 HG Hka RgC DRa. lia. }
  destruct GFAR as (GF1 & GF2 & GF3 & GF4). pose_ceil.
  assert (GR64 : 0 <= G < 2^64) by (clear - GF3 Cga RgB0 HG Hka Sga0; unfold NSLOTS in Hka; lia).

  assert (PEM : rpres_except (fun x => (Bg <= x < Bg + OL) \/ (NB <= x < NB + needed) \/ (lo <= x < sp1)) m1 mm).
  { intros x Hx NC. split; [apply AGM; clear - Hx NC; try lia; tauto| apply WMM; clear - Hx NC; try lia; tauto]. }
  pose proof (rmrep_meta_chunk st m1 g RMR MSL) as MM0. change (get_meta_rec st g) with mr in MM0. fold G in MM0.
  assert (MM : rw_cells rsegs mm G (meta_cells st mr)).
  { eapply rpres_except_rw_cells; [exact PEM| exact MM0|]. unfold meta_cells. cbn [cells_size csize Nat.add Z.of_nat]. intros x Hx [X|[X|X]]; subst sp1; clear - Hx X GF1 GF2 GF3 CLOv LO SPR; lia. }
  unfold meta_cells in MM. rewrite HM in MM. change (pw st (Some bg)) with (wz (conc st bg)) in MM. fold Bg in MM.
  change (meta_word mr) with mword in MM.

  destruct (SH _ _ Hr Kr) as [WRr RDr].
  destruct (RDr (snd c + UNIT * off - 3) _ ltac:(rewrite Sc16, <- EOL; unfold UNIT; clear - Hoff OL4096 NDR KT; lia) ltac:(rewrite <- FC; exact K3)) as [BK0 B3R].
  set (b3 := idx + 32 * Z.min (snd c + stride - IB - (snd c + UNIT * off) - old) 5) in *.
  assert (B3K : Z.land b3 31 = 0).
  { subst b3. rewrite I0. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. change (2^5) with 32.
    lazymatch goal with |- context [Z.min ?u 5] => destruct (Z.min_spec u 5) as [[X1 X2]|[X1 X2]]; rewrite X2 end;
      clear - FIT Hoff HO X1; Z.div_mod_to_equations; lia. }
  set (P' := NB + 16 + 16 * off). set (E' := NB + needed - 4).
  assert (EP' : P' = NB + 16 + 16 * off) by reflexivity. assert (EE' : E' = NB + needed - 4) by reflexivity. clearbody P' E'.
  assert (BK : bytes_at rsegs mm (NB + 13 + 16 * off) [b8 b3]).
  { destruct BK0 as (_ & _ & HB). split; [clear - NB0 Hoff; lia|]. split; [cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - NCEILv Hoff NDR HN; lia|].
    intros i Hi. destruct i; [| cbn in Hi; lia]. specialize (HB 0%nat Hi). cbn [nth_error] in HB |- *. rewrite Z.add_0_r in HB |- *.
    rewrite ref_mrd_overlay in HB |- * by (rewrite wa_unsigned; rewrite ?Sc16; unfold UNIT; clear - NB0 NCEILv Hoff NDR DRn DRr RrB0 RBC EBg OL4096 KT HN FIT HO STR; lia).
    rewrite <- HB. replace (NB + 13 + 16 * off) with (NB + (13 + 16 * off)) by (clear; lia).
    rewrite Sc16, <- EBg. unfold UNIT. replace (Bg + (16 + 16 * off - 3)) with (Bg + (13 + 16 * off)) by (clear; lia).
    apply COPY. clear - Hoff NDR KT FIT HO STR; lia. }
  assert (FR' : rw_cells rsegs mm (bv_unsigned (Z_to_bv 64 sp1)) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) by (rewrite unsigned_lit by (subst sp1; lia); exact FR).
  set (gw := wz G) in *. assert (HGW : bv_unsigned gw = G) by (subst gw; apply wz_unsigned; exact GR64). rewrite <- HGW in MM.

  eapply evt_mono.
  { apply (tail_6c0 rax (Z_to_bv 64 sp1) gp tp s7 s8 s9 s10 s11 t4v t5v t6v ra s0 s1 s2 s3 s4 s5 s6 gw _ _ _ _ _ F fc mm G NB needed n off mword b3
             HGW ltac:(clear - GR64; lia) NB0 ltac:(clear - HN; lia) ltac:(clear - Hoff; lia) B3R ltac:(clear - NDR; lia) NDA ND62 MWM MW64 GF2
             ltac:(rewrite unsigned_lit by (subst sp1; clear - SPR LO CLOv; lia); subst sp1; clear - GF3 CLOv LO; lia)
             ltac:(rewrite unsigned_lit by (subst sp1; clear - SPR LO CLOv; lia); subst sp1; clear - NCEILv CLOv LO; lia)
             ltac:(rewrite unsigned_lit by (subst sp1; clear - SPR LO CLOv; lia); subst sp1; clear - SPR LO; lia)
             MM WRN BK FR' MI1). }
  intros ms' (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & m2 & m' & -> & EM & MU2 & WM2 & MI' & MM2 & FR2).
  rewrite unsigned_lit in FR2 |- * by (subst sp1; clear - SPR LO CLOv; lia).
  replace (Z_to_bv 64 (sp1 + 64)) with sp by (apply bv_eq; rewrite unsigned_lit by (subst sp1; clear - SPR LO CLOv; lia); subst sp1; clear; lia).
  rewrite HGW in MM2.
  set (m3 := write_to_mem m2 (wa (NB + needed - 4)) [b8 0]) in EM.

  assert (PE2 : rpres_except (fun x => (G + 16 <= x < G + 24) \/ (G + 32 <= x < G + 40)) mm m2).
  { eapply rpres_except_of_munch; [exact MU2| exact WM2|]. intros x Hx NC. cbn [outside]. clear - NC. repeat split; lia. }
  assert (AG2 : forall x, 0 <= x < 2^64 -> ~ (Bg <= x < Bg + OL) -> ~ (NB <= x < NB + needed) -> ~ (lo <= x < sp1) -> ~ (G + 16 <= x < G + 24) -> ~ (G + 32 <= x < G + 40) ->
                 m2 (wa x) = m1 (wa x)).
  { intros x Hx N1 N2 N3 N4 N5. rewrite <- (AGM x Hx N1 N2 N3). apply (proj1 (PE2 x Hx ltac:(clear - N4 N5; tauto))). }

  assert (EMW' : meta_word (m_set_maplen (needed / 4096) mr) = 4064 + needed).
  { unfold meta_word, m_set_maplen. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. change (2 ^ 52 - 1) with (Z.ones 52).
    rewrite Z.land_ones by (clear; lia). rewrite Z.mod_small by (clear - ND62 ND4096; Z.div_mod_to_equations; lia).
    rewrite L0, FB1, SC. clear - NDA. Z.div_mod_to_equations. lia. }
  lazymatch type of MM2 with rw_cells _ _ _ [C8 ?u0; C8 ?u1; _; C4 ?u3; C4 ?u4; _] =>
    pose proof (rw_cells_app_inv m2 G [C8 u0; C8 u1] _ MM2) as [_ MMb]; cbn [cells_size csize Nat.add Z.of_nat app] in MMb;
    pose proof (rw_cells_app_inv m2 (G + 16) [C8 (wz NB)] _ MMb) as [NEWM MMc]; cbn [cells_size csize Nat.add Z.of_nat app] in MMc;
    pose proof (rw_cells_app_inv m2 (G + 16 + 8) [C4 u3; C4 u4] _ MMc) as [_ NEWW]; cbn [cells_size csize Nat.add Z.of_nat Pos.to_nat app] in NEWW end.
  replace (G + 16 + 8 + 8) with (G + 32) in NEWW by (clear; lia). rewrite <- EMW' in NEWW.
  destruct (rptrs_remap st LB0 m1 (fst bg) r g (fst bg, 0) ai CINV0 RMR Hr Kr HgB0 ONLYG0) as (PC1 & PC2 & PC3 & PC4 & PC5 & PC6 & PC7 & PM & PA & PG).

  assert (AGst : forall x, 0x10000 <= x < 0x8a000 -> m2 (wa x) = m1 (wa x)).
  { intros x Hx. apply AG2; clear - Hx DRr DRn CLOv GF4 OL4096 ND4096; lia. }
  assert (MR2 : rmrep (rstT st (fst bg) g NB needed) m2).
  { apply (rmrep_remap st m1 m2 (fst bg) r g ai NB needed RMR Hr Kr HgB0 HM0 MSL EOL); try assumption.
    - clear - ND4096; lia.
    - intros x Hx. apply AGst. unfold RMLOCK in Hx. clear - Hx; lia.
    - intros x Hx. apply AGst. unfold RLIBC in Hx. clear - Hx; lia.
    - intros x Hx. apply AGst. unfold RGOT_SSP in Hx. clear - Hx; lia.
    - intros x Hx. apply AGst. unfold RSSP_GUARD in Hx. clear - Hx; lia.
    -
      intros a' ar' Ha' x Hx N4 N5.
      destruct (rarea_conc st _ _ WF Ha') as (ra' & Hra' & Ca' & Sa0 & Sa1 & SaL & NKa & RaB0 & RaAL & RaC). pose_ceil.
      assert (NEa : fst a' <> fst bg) by (intros E0; rewrite E0, Hr in Hra'; assert (ra' = r) by congruence; subst ra'; exact (NKa Kr)).
      pose proof (DISJr _ _ _ _ Hra' Hr NEa) as D1. pose proof (DJ' _ _ Hra' NEa) as D2.
      pose proof (rarea_lr_lo st _ _ ra' WF Ha' Hra') as LRa. pose proof (lr_lo_group r Kr) as LRr. rewrite <- EOL, LRr, <- EBg in D1.
      apply AG2; [clear - Hx Ca' Sa0 Sa1 RaB0 RaC; lia| clear - Hx D1 LRa Ca' Sa1; lia| clear - Hx D2 LRa Ca' Sa1; lia| subst sp1; clear - Hx Ca' Sa1 RaC CLOv LO; lia| exact N4| exact N5].
    -
      intros b' gh' Hb' NEb x Hx. destruct (WG b' gh' Hb') as (rb & Hrb & Krb & Sb0 & Sb1 & _).
      rewrite (conc_region' st b' rb Hrb) in Hx.
      pose proof (DISJr _ _ _ _ Hrb Hr NEb) as D1. pose proof (DJ' _ _ Hrb NEb) as D2. rewrite (lr_lo_group rb Krb) in D1, D2. rewrite <- EOL, (lr_lo_group r Kr), <- EBg in D1.
      assert (NEg : fst b' <> fst a) by (intros E0; rewrite E0, Hrga in Hrb; assert (rb = rga) by congruence; subst rb; exact (NKg Krb)).
      pose proof (DISJr _ _ _ _ Hrb Hrga NEg) as D3. rewrite (lr_lo_group rb Krb) in D3.
      pose proof (rarea_lr_lo st _ _ rga WF (proj1 (bf_area _ _ _ _ _ _ _ _ _ _ _ BF)) Hrga) as LRa.
      destruct (WR _ _ Hrb) as (RbB0 & _ & _ & RbC & _). pose_ceil. unfold NSLOTS in Hka.
      apply AG2; [clear - Hx Sb0 Sb1 RbB0 RbC; lia| clear - Hx D1 Sb0 Sb1; lia| clear - Hx D2 Sb0 Sb1; lia| subst sp1; clear - Hx Sb0 Sb1 RbC CLOv LO; lia
                | clear - Hx D3 LRa Cga Sga1 HG Hka Sb0 Sb1; lia| clear - Hx D3 LRa Cga Sga1 HG Hka Sb0 Sb1; lia].
    -
      intros q rq Hq Kq NEq x Hx.
      pose proof (DISJr _ _ _ _ Hq Hr NEq) as D1. pose proof (DJ' _ _ Hq NEq) as D2. rewrite (lr_lo_group rq Kq) in D1, D2. rewrite <- EOL, (lr_lo_group r Kr), <- EBg in D1.
      assert (NEg : q <> fst a) by (intros E0; rewrite E0, Hrga in Hq; assert (rq = rga) by congruence; subst rq; exact (NKg Kq)).
      pose proof (DISJr _ _ _ _ Hq Hrga NEg) as D3. rewrite (lr_lo_group rq Kq) in D3.
      pose proof (rarea_lr_lo st _ _ rga WF (proj1 (bf_area _ _ _ _ _ _ _ _ _ _ _ BF)) Hrga) as LRa.
      destruct (WR _ _ Hq) as (RqB0 & _ & _ & RqC & _). pose_ceil. unfold NSLOTS in Hka.
      apply AG2; [clear - Hx RqB0 RqC; lia| clear - Hx D1; lia| clear - Hx D2; lia| subst sp1; clear - Hx RqC CLOv LO; lia
                | clear - Hx D3 LRa Cga Sga1 HG Hka; lia| clear - Hx D3 LRa Cga Sga1 HG Hka; lia].
    - intros i Hi. assert (Hi' : 0 <= i < needed) by (clear - Hi; lia).
      rewrite <- EBg, <- (COPY i Hi). apply (proj1 (PE2 (NB + i) ltac:(clear - Hi' NB0 NCEILv; lia) ltac:(cbv beta; clear - Hi' GF2; lia))).
    - intros i Hi. assert (Hi' : 0 <= i < needed) by (clear - Hi KT; subst kt OL mr; lia).
      rewrite <- (ZERO i Hi). apply (proj1 (PE2 (NB + i) ltac:(clear - Hi' NB0 NCEILv; lia) ltac:(cbv beta; clear - Hi' GF2; lia))).
    - eapply rpres_except_wr_at; [exact PE2| exact WRN| cbv beta; intros x Hx; clear - Hx GF2; lia]. }

  pose proof (realloc_ticks _ _ _ AR) as TK.
  set (stR := rstT st (fst bg) g NB needed) in MR2.
  assert (TKR : ticks_ok stR).
  { subst stR. unfold rstT. apply ticks_ok_trim_shadow. unfold rstR. apply ticks_ok_upd_meta. eapply A_ASlot_M0.ticks_ok_same; [| | exact TK]; reflexivity. }
  set (st0 := set_tick (N.succ (s_tick st)) stR).
  assert (MR0 : rmrep st0 m2) by (apply rmrep_set_tick; exact MR2).
  assert (TK0 : ticks_ok st0) by (apply ticks_ok_set_tick; [change (s_tick stR) with (s_tick st); clear; lia| exact TKR]).
  set (r' := mkRegion RKGroup NB needed).
  assert (Hr' : s_regions st0 !! (fst bg) = Some r') by (subst st0 stR; cbn [s_regions set_tick]; apply rr_lookup_new).
  assert (GR0 : s_groups st0 = s_groups st) by reflexivity.
  pose proof (rmrep_wr8 st0 m2 (fst bg, needed - 4) 0 r' MR0 TK0 Hr' eq_refl ltac:(cbn [snd r_len r']; rewrite NDround; clear - ND4096; lia)
                ltac:(cbn [fst snd]; intros b' gh' Hb' Hf'; rewrite GR0 in Hb'; pose proof (ONLYG0 _ _ Hb' Hf') as ->; cbn [snd]; clear - ND4096; lia)
                ltac:(clear; lia)) as MR3.
  cbn [fst snd r_base r'] in MR3. replace (NB + (needed - 4)) with (NB + needed - 4) in MR3 by (clear; lia). fold m3 in MR3.
  pose proof (ticks_ok_wr8 st0 (fst bg, needed - 4) 0 TK0) as TK3.
  destruct (rss_mrep (wr8 (fst bg, needed - 4) 0 st0) m3 (fst bg, 0) r' (needed - 16) 0 n off b3 MR3 TK3
              ltac:(cbn [fst]; change (s_regions (wr8 ?q ?v ?X)) with (s_regions X); exact Hr') eq_refl ltac:(cbn [snd]; clear; lia) ltac:(clear; lia)
              ltac:(cbn [snd r_len r']; rewrite NDround; clear - ND4096; lia) ltac:(clear - ND4096; lia)
              ltac:(cbn [fst snd]; intros b' gh' Hb' Hf'; change (s_groups (wr8 ?q ?v ?X)) with (s_groups X) in Hb'; rewrite GR0 in Hb';
                    pose proof (ONLYG0 _ _ Hb' Hf') as ->; cbn [snd]; clear - ND4096; lia)
              ltac:(clear - Hoff; lia) ltac:(clear - HN; lia) ltac:(clear - NDR; lia) ltac:(clear - NDR; lia)
              B3K) as [RSS TKS].
  cbn [fst snd r_base r'] in RSS, TKS.
  replace (NB + (0 + 16 + (needed - 16) * 0 + 16 * off)) with P' in RSS by (rewrite EP'; clear; lia).
  replace (NB + (0 + 16 + (needed - 16) * 0 + (needed - 16 - 4))) with E' in RSS by (rewrite EE'; clear; lia).
  rewrite <- EP', <- EE' in EM. rewrite <- EM in RSS.
  lazymatch type of RSS with rmrep ?stF _ => assert (EFULL : remap_full st c off n NB needed = stF) end.
  { unfold remap_full. rewrite SL. cbv zeta.
    lazymatch goal with |- context [get_stride (get_meta_rec ?sx g)] =>
      replace (get_stride (get_meta_rec sx g)) with (needed - 16) end.
    2:{ change (get_meta_rec (set_tick _ (trim_shadow _ _ ?X)) g) with (get_meta_rec X g). unfold remap_update. rewrite MI_Kit.get_meta_rec_upd_same.
        change (get_meta_rec (set_regions _ st) g) with mr. unfold get_stride, m_set_maplen. cbn [m_last_idx m_sizeclass m_maplen]. rewrite L0.
        change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by (clear; lia). rewrite Z.mod_small by (clear - ND62 ND4096; Z.div_mod_to_equations; lia).
        cbn [Z.eqb andb]. destruct (Z.eqb_spec (needed / 4096) 0) as [X|X]; [exfalso; clear - X ND4096; Z.div_mod_to_equations; lia|]. cbn.
        unfold UNIT. clear - NDA. Z.div_mod_to_equations. lia. }
    rewrite I0, Ec16. subst st0 stR. unfold rstT, rstR, remap_update, aadd, UNIT, IB. cbn [fst snd].
    replace (0 + 16 + (needed - 16) * 0 + 16 * off) with (16 + 16 * off) by (clear; lia).
    replace (0 + 16 + (needed - 16) * 0 + (needed - 16 - 4)) with (needed - 4) by (clear; lia).
    replace (16 + (needed - 16 - 4)) with (needed - 4) by (clear; lia). reflexivity. }
  rewrite <- EFULL in RSS, TKS.

  assert (DISJc : forall rid2 r2, s_regions st !! rid2 = Some r2 -> rid2 <> fst c -> let '(b2, l2) := region_live_range r2 in NB + needed <= b2 \/ b2 + l2 <= NB).
  { intros rid2 r2 H2 NE2. apply (DISJ rid2 r2 H2). rewrite <- FC. exact NE2. }
  destruct (areach_realloc_remap ref_reserved st LB0 p A old n off AR Hin0 HN HA (fst c) g Bg OL needed NB RC NB0 NBA NCEIL DISJc) as (ARR & _).
  fold c in ARR. replace (NB + UNIT + UNIT * off) with P' in ARR by (rewrite EP'; unfold UNIT; clear; lia).

  unfold UNIT, IB in FIT, S16.
  assert (PE3 : rpres_except (fun x => x = P' - 3 \/ P' + n <= x < NB + needed) m2 m').
  { rewrite EM. subst m3. rewrite <- EE'. apply (rinplace_pres m2 P' E' n b3 NB (NB + needed)); rewrite ?EE', ?EP'; clear - NB0 NCEILv NDR Hoff HN ND4096; lia. }
  assert (PE23 : rpres_except (fun x => (NB <= x < NB + needed) \/ (G + 16 <= x < G + 24) \/ (G + 32 <= x < G + 40)) mm m').
  { eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE2| cbv beta; intros x Hx; clear - Hx; tauto]|].
    eapply rpres_except_mono; [exact PE3| cbv beta; intros x Hx; left; rewrite EP' in Hx; clear - Hx Hoff HN NDR; lia]. }
  set (C := fun x : Z => ((lo <= x < bv_unsigned sp) \/ (RERRNO <= x < RERRNO + 4)) \/ (Bg <= x < Bg + OL) \/ (NB <= x < NB + needed) \/ (G + 16 <= x < G + 24) \/ (G + 32 <= x < G + 40)).
  assert (PE : rpres_except C m m').
  { eapply rpres_except_trans; [eapply rpres_except_mono; [exact PRES1| subst C; cbv beta; intros x Hx; clear - Hx; tauto]|].
    eapply rpres_except_trans; [eapply rpres_except_mono; [exact PEM|]|].
    { subst C; cbv beta. intros x [X|[X|X]]; [right; left; exact X| right; right; left; exact X| left; left; subst sp1; clear - X; lia]. }
    eapply rpres_except_mono; [exact PE23| subst C; cbv beta; intros x Hx; clear - Hx; tauto]. }

  assert (NCstk : forall x, bv_unsigned sp <= x -> ~ C x).
  { intros x Hx. subst C; cbv beta. subst sp1. unfold RERRNO. clear - Hx LO CLOv RBC NCEILv GF3 SPR. lia. }
  assert (NCimg : forall x, x < 0x8a000 -> 0x10000 <= x -> ~ (RERRNO <= x < RERRNO + 4) -> ~ C x).
  { intros x H1 H2 H3. subst C; cbv beta. clear - H1 H2 H3 CLOv DRr DRn GF4 OL4096 ND4096. lia. }
  pose proof (rarea_lr_lo st _ _ rga WF (proj1 (bf_area _ _ _ _ _ _ _ _ _ _ _ BF)) Hrga) as LRa. unfold NSLOTS in Hka.
  assert (NCblk : forall b' x, In b' (lb_remove p LB) -> blk_addr b' <= x < blk_addr b' + blk_size b' -> ~ C x).
  { intros b' x Hb' Hab. unfold lb_remove in Hb'. apply In_filter_b in Hb' as [Hb' NEQ].
    assert (Hb0 : In b' LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hb']).
    assert (NE : blk_slot b' <> c).
    { intros EQ. pose proof (nodup_slot_unique LB0 (p, A, old) b' (realloc_nodup _ _ _ AR) Hin0 Hb0 EQ) as ->.
      unfold bptr_eqb, blk_id in NEQ. cbn [fst snd] in NEQ. rewrite aptr_eqb_refl, Z.eqb_refl in NEQ. discriminate. }
    destruct (RHEAP_block_range_proof s LB0 m1 b' ltac:(exists st, LB0; split; [apply Permutation_refl|]; split; [exact Hst|]; split; [exact RMR|]; split; [exact HBL| exact AR]) Hb0) as (_ & _ & _ & BC' & BI').
    pose_ceil.
    destruct (realloc_blk_in_region ref_reserved st LB0 p A old AR Hin0 g bg idx SL HM b' Hb0 x Hab) as (rq & Hrq & Krq & Haq).
    pose proof (RPRIV b' Hb0 NE x) as PRV. rewrite <- EOL, <- EBg in PRV.
    assert (NQB : ~ (NB <= x < NB + needed)).
    { intros X. destruct (N.eq_dec (fst (blk_slot b')) (fst bg)) as [EQ|NEq].
      - rewrite EQ, Hr in Hrq. assert (rq = r) as -> by congruence. rewrite <- EOL, <- EBg in Haq. exact (PRV Haq Hab).
      - pose proof (DISJ _ _ Hrq NEq) as D. unfold region_live_range in D. rewrite Krq in D. clear - D X Haq. lia. }
    assert (NEg : fst (blk_slot b') <> fst a) by (intros E0; rewrite E0, Hrga in Hrq; assert (rq = rga) by congruence; subst rq; exact (NKg Krq)).
    pose proof (DISJr _ _ _ _ Hrq Hrga NEg) as D3. rewrite (lr_lo_group rq Krq) in D3.
    subst C; cbv beta. intros [[X|X]|[X|[X|[X|X]]]].
    - clear - X Hab BC' CLOv. lia.
    - unfold RERRNO in X. clear - X Hab BI'. lia.
    - exact (PRV X Hab).
    - exact (NQB X).
    - clear - X Haq D3 LRa Cga Sga1 HG Hka. lia.
    - clear - X Haq D3 LRa Cga Sga1 HG Hka. lia. }

  assert (ST' : stk rsegs m' lo sp1) by (eapply rpres_except_stk; [exact PE23| exact ST1| cbv beta; intros x Hx; subst sp1; clear - Hx NCEILv CLOv GF3 LO; lia]).
  eapply stk_release in FR2; [| exact ST'| subst sp1; clear - LO CLOv; lia]. clear ST'. rename FR2 into ST'. cbn [cells_size csize Nat.add] in ST'.
  lazymatch type of ST' with stk _ _ _ ?h => replace h with (bv_unsigned sp) in ST' by (subst sp1; clear; lia) end.
  rewrite ETP in ERR1.
  assert (ERR' : rw_cells rsegs m' (errno_addr tp) [C4 errv2]).
  { rewrite ETP. eapply rpres_except_rw_cells; [exact PE23| exact ERR1|]. cbn [cells_size csize Nat.add Z.of_nat]. cbv beta. intros x Hx. clear - Hx DRn GF4 ND4096; lia. }
  assert (AUX' : rauxv_ok m' B).
  { eapply rauxv_ok_pres_B; [exact AUX1| exact PE23| cbv beta; intros x Hx; clear - Hx SB LO CLOv NCEILv GF3; lia| cbv beta; unfold RAUXV_CELL, RLIBC; intros x Hx; clear - Hx DRn GF4 ND4096; lia]. }

  pose proof (realloc_nodup _ _ _ AR) as ND0.
  assert (PERM' : Permutation (rLB' LB0 p n P') ((p, P', n) :: lb_remove p LB)).
  { unfold rLB'. apply perm_skip. rewrite (lb_remove_lbrm LB p A old (NoDup_map_perm blk_slot LB0 LB PERM ND0) ltac:(eapply Permutation_in; [exact PERM| exact Hin0])).
    unfold lbrm. cbn [blk_slot fst]. fold c. apply filter_Permutation. exact PERM. }

  assert (AIMG0 : A + old <= 0x10000 \/ 0x8a000 <= A) by (clear - DRr HAE FIT Hoff HO STR OL4096; lia).
  assert (HK0 : 0 <= Z.min old n <= old /\ Z.min old n <= n) by (clear - HO HN; lia).
  set (k := Z.to_nat (Z.min old n)).
  assert (OLDk : bytes_at rsegs m A (firstn k oldbs)).
  { rewrite <- (firstn_skipn k oldbs) in OLDB. apply bytes_at_app in OLDB as [X _]. exact X. }
  assert (LK : length (firstn k oldbs) = k) by (rewrite length_firstn; subst k; clear - HK0 OLEN; lia).
  assert (OLD1 : bytes_at rsegs m1 A (firstn k oldbs)).
  { eapply rpres_except_bytes_at; [exact PRES1| exact OLDk|]. rewrite LK. cbv beta. intros x Hx. subst k. unfold RERRNO. clear - Hx HK0 AIMG0 HAE FIT HO STR RBC CLOv LO Hoff; lia. }
  assert (OLDmm : bytes_at rsegs mm P' (firstn k oldbs)).
  { apply (rbytes_at_moved m1 mm A P' (firstn k oldbs) OLD1); rewrite ?LK.
    - intros i Hi. rewrite EP', HAE. replace (NB + 16 + 16 * off + i) with (NB + (16 + 16 * off + i)) by (clear; lia).
      replace (Bg + 16 + 16 * off + i) with (Bg + (16 + 16 * off + i)) by (clear; lia). apply COPY. subst k kt. clear - Hi HK0 FIT STR NDR Hoff; lia.
    - rewrite EP'; clear - NB0 Hoff; lia.
    - rewrite EP'; subst k; clear - NCEILv HK0 NDR Hoff; lia.
    - subst k; clear - AIMG0 HK0; lia.
    - rewrite EP'; subst k; clear - DRn HK0 NDR Hoff ND4096; lia. }
  assert (OLD2 : bytes_at rsegs m2 P' (firstn k oldbs)).
  { eapply rpres_except_bytes_at; [exact PE2| exact OLDmm|]. rewrite LK. cbv beta. intros x Hx. subst k. clear - Hx HK0 GF2 EP' NDR Hoff; lia. }
  assert (OLD' : bytes_at rsegs m' P' (firstn k oldbs)).
  { eapply rpres_except_bytes_at; [exact PE3| exact OLD2|]. rewrite LK. cbv beta. intros x Hx. subst k. clear - Hx HK0; lia. }
  assert (WRn : wr_at rsegs m' P' n).
  { eapply rpres_except_wr_at; [exact PE3| |cbv beta; intros x Hx; clear - Hx; lia].
    eapply rpres_except_wr_at; [exact PE2| eapply wr_at_sub; [exact WRN| rewrite EP'; clear - Hoff; lia| rewrite EP'; clear - NDR Hoff; lia]| cbv beta; intros x Hx; clear - Hx GF2 EP' NDR Hoff; lia]. }
  destruct (rwr_at_bytes_exist m' (P' + Z.of_nat k) (n - Z.of_nat k) ltac:(eapply wr_at_sub; [exact WRn| subst k; clear - HK0; lia| subst k; clear - HK0; lia]) ltac:(subst k; clear - HK0; lia) ltac:(rewrite EP'; subst k; clear - DRn HK0 NDR Hoff ND4096; lia)) as (junk & LJ & BJ).
  assert (BLK : rw_cells rsegs m' P' [Cells.CB (Z.to_nat n) (firstn k oldbs ++ junk)]).
  { split; [split|].
    - cbn. split; [| exact I]. rewrite length_app, LK, LJ. subst k. clear - HK0 HN; lia.
    - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split; [exact OLD'|]. rewrite LK. exact BJ.
    - cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (clear - HN; lia). exact WRn. }

  unfold POST, rrealloc_post. do 15 eexists. exists m', errv2. split; [reflexivity|].
  split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|].
  split. { intros x Hx. apply (proj1 (PE x ltac:(unfold RAUXV_CELL, RLIBC in Hx; clear - Hx; lia) ltac:(apply NCimg; unfold RAUXV_CELL, RLIBC, RERRNO in *; clear - Hx; lia))). }
  split. { intros x Hx HCx. apply PE; [exact Hx|]. destruct HCx as [X|[[X NS]|(b' & Hb' & Hab)]]; [apply NCstk; exact X| apply NCimg; unfold ralloc_static, RERRNO in *; clear - X NS; lia| exact (NCblk b' x Hb' Hab)]. }
  split; [reflexivity|]. split; [reflexivity|].
  exists P', junk.
  split; [rewrite EP'; reflexivity|].
  split. { pose_ceil; unfold rblock_range. rewrite EP'. clear - NB0 NBA HN NDR NCEILv Hoff DRn ND4096. Z.div_mod_to_equations. lia. }
  split.
  { exists (remap_full st c off n NB needed), (rLB' LB0 p n P'). split; [exact PERM'|].
    split. { rewrite strip_remap_full by (exists (g, idx); exact SL). rewrite SL. cbn [ps_m set_m]. rewrite Hst. reflexivity. }
    split; [exact RSS|]. split; [| exact ARR].
    unfold brk_link in HBL |- *. cbn [ps_brk set_m].
    change (ctx (remap_full st c off n NB needed)) with (s_ctx (remap_full st c off n NB needed)).
    rewrite <- (s_ctx_strip (remap_full st c off n NB needed)), strip_remap_full, SL, s_ctx_remap_update, s_ctx_strip by (exists (g, idx); exact SL).
    change (s_ctx st) with (ctx st).
    destruct (c_brk (ctx st)) as [| |brid boff]; [exact I| exact I|].
    rewrite HBL. unfold conc, get_region.
    rewrite <- (s_regions_strip (remap_full st c off n NB needed)), strip_remap_full, SL, s_regions_remap_update by (exists (g, idx); exact SL).
    cbn [fst snd]. rewrite lookup_insert_ne by (rewrite FC; clear - PC7; congruence). rewrite s_regions_strip. reflexivity. }
  exact BLK.
Qed.
End TAIL.

Section P.
Hypothesis HMAL : rmalloc_impl_stmt.
Hypothesis HFREE : rfree_impl_stmt.

Theorem remap_arm_proof : remap_arm_stmt.
Proof.
  unfold remap_arm_stmt.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 F fc m m1 s LB LB0 p A old n lo B errv oldbs st g bg idx r off.
  intros _ _ PERM Hst RMR HBL AR Hin0 SL HM Hr Kr FC Ec CB HA Hoff FIT HO S16 SMOD B0 BG16 Hidx LI SPAN RCEIL RB0 SSTR SC63 K3
         FR ST1 MI1 ERR1 AUX1 PRES1 OLDB OLEN SB CLO LO TP HN _ y7 a5v y28 THR SC.
  set (c := fst p) in *. set (mr := get_meta_rec st g) in *. set (stride := get_stride mr) in *. set (Bg := conc st bg) in *.
  set (E := Bg + 16 + stride * (idx + 1) - 4) in *. set (sp1 := bv_unsigned sp - 64) in *.
  set (POST := rrealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p A old n lo B oldbs m).
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof LO as LOr. unfold RREALLOC_STACK, RMALLOC_STACK in LO. pose proof CLO as CLOv. pose_ceil.
  assert (ETP : bv_unsigned tp + -164 = 429036) by (rewrite TP; unfold RATP; rewrite unsigned_lit by lia; reflexivity).

  destruct (realloc_bf ref_reserved st LB0 p A old AR Hin0 g bg idx SL HM) as (L & LS & BL & off' & ai & a & ar & ka & INV & CR & Hk & HA' & BF).
  change (fst p) with c in HA'. assert (off' = off) as -> by (rewrite HA in HA'; unfold UNIT in HA'; clear - HA'; lia). clear HA'.
  pose proof INV as (IR & IA & IM & IL & IG & IS & ISH).
  pose proof (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF) as HgB. fold c in HgB.
  pose proof (ig_ok _ _ _ IG _ _ _ HgB) as GO.
  destruct (g_sc _ _ _ _ _ _ GO) as [[S48 _]|(_ & L0 & ML & _)]; [exfalso; change (MR st g) with mr in S48; clear - S48 SC; lia|].
  change (MR st g) with mr in L0, ML.
  destruct (g_top _ _ _ _ _ _ GO ML) as (SB0 & r0 & Hr0 & Kr0 & EOL & GE). change (MR st g) with mr in EOL, GE.
  rewrite Hr in Hr0. assert (r0 = r) as -> by congruence.
  assert (I0 : idx = 0) by (clear - Hidx L0; lia).
  assert (STR : stride = m_maplen mr * 4096 - 16).
  { subst stride. unfold get_stride. rewrite L0. cbn [Z.eqb andb]. destruct (Z.eqb_spec (m_maplen mr) 0); [exfalso; exact (ML ltac:(eassumption))| reflexivity]. }
  set (OL := m_maplen mr * 4096) in *.
  pose proof (g_maplen _ _ _ _ _ _ GO) as ML0. change (MR st g) with mr in ML0.
  assert (OL4096 : 4096 <= OL) by (subst OL; clear - ML ML0; lia).
  assert (EBg : Bg = r_base r) by (subst Bg; rewrite CB, SB0; clear; lia).
  assert (CC : conc st c = Bg + 16) by (subst c; rewrite (conc_region' st (fst p) r) by (rewrite FC; exact Hr); rewrite Ec; cbn [snd]; rewrite SB0, I0, EBg; unfold UNIT; clear; lia).
  assert (HAE : A = Bg + 16 + 16 * off) by (rewrite HA, CC; unfold UNIT; clear; lia).
  assert (HE : E = Bg + OL - 4) by (subst E; rewrite I0, STR; clear; lia).
  set (needed := remap_needed (UNIT * off) n).
  pose proof (remap_needed_ge (UNIT * off) n ltac:(clear - HN; lia) ltac:(unfold UNIT; clear - Hoff; lia)) as NDR. fold needed in NDR. unfold UNIT, IB in NDR.
  pose proof (remap_needed_pg (UNIT * off) n) as NDA. fold needed in NDA.
  assert (ND62 : needed < 2 ^ 62) by (clear - NDR HN Hoff; lia).
  assert (ND4096 : 4096 <= needed) by (clear - NDR NDA HN Hoff; Z.div_mod_to_equations; lia).
  set (kt := Z.min OL needed).
  pose proof RMR as (WF & CX & GL & ARS & GR & SH). pose proof WF as (Hres & WR & DISJr & WA & WG).
  destruct (WR _ _ Hr) as (RrB0 & RBAL & RL0 & RBC & RF). pose_ceil.
  pose proof (round_up_pg_ge (r_len r)) as RUP. rewrite <- EOL in RUP, RBC, RF.
  pose proof (rreserved_disjoint1 _ _ RF ltac:(clear - OL4096; lia)) as DRr. rewrite <- EBg in DRr, RBC, RrB0, RBAL, RF.
  destruct (SH _ _ Hr Kr) as [WRr RDr]. rewrite <- EBg, <- EOL in WRr.
  set (mword := m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr) in *.
  pose proof (g_freeable _ _ _ _ _ _ GO) as FB1. change (MR st g) with mr in FB1.
  assert (MWR : 0 <= mword < 2^64) by (subst mword OL; rewrite L0, FB1, SC; clear - ML0 RBC RrB0; lia).
  assert (MWP : mword - mword mod 4096 = OL).
  { subst mword OL. rewrite L0, FB1, SC. replace (0 + 32 * 1 + 64 * 63 + 4096 * m_maplen mr) with (4064 + m_maplen mr * 4096) by (clear; lia).
    rewrite Z.mod_add, Z.mod_small by (clear; lia). clear; lia. }
  assert (NDE : needed = (n + 4095 + 16 * off + 20) - (n + 4095 + 16 * off + 20) mod 4096).
  { subst needed. unfold remap_needed, UNIT, IB. clear - HN Hoff. Z.div_mod_to_equations. lia. }

  assert (RC : realloc_case (strip st) c A n = RcRemap (fst c) g Bg OL needed).
  { unfold realloc_case, realloc_geom. change (s_slots (strip st)) with (s_slots st). rewrite SL.
    change (get_meta_rec (strip st) g) with mr. change (conc (strip st) c) with (conc st c). fold stride. cbn [rg_g rg_start rg_end rg_idx rg_stride].
    unfold inplace_ok. cbn [rg_end rg_g]. change (get_meta_rec (strip st) g) with mr.
    replace (n <? MMAP_THRESHOLD) with false by (symmetry; apply Z.ltb_ge; clear - THR; lia). rewrite andb_false_r. cbn [andb].
    replace (MMAP_THRESHOLD <=? n) with true by (symmetry; apply Z.leb_le; exact THR).
    replace (48 <=? m_sizeclass mr) with true by (symmetry; apply Z.leb_le; clear - SC; lia). cbn [andb].
    rewrite HM. change (conc (strip st) bg) with Bg. subst needed. rewrite CC, HAE. f_equal. unfold UNIT. f_equal. clear; lia. }

  assert (DISJo : forall rid2 r2, s_regions st !! rid2 = Some r2 -> rid2 <> fst bg ->
                  let '(b2, l2) := region_live_range r2 in Bg + OL <= b2 \/ b2 + l2 <= Bg).
  { intros rid2 r2 H2 NE2. pose proof (DISJr _ _ _ _ H2 Hr NE2) as D. rewrite (lr_lo_group r Kr), <- EBg, <- EOL in D.
    unfold region_live_range. unfold lr_lo in D. destruct (r_kind r2); unfold PGSZ; clear - D; lia. }
  assert (SP1 : bv_unsigned (Z_to_bv 64 sp1) = sp1) by (apply unsigned_lit; subst sp1; clear - SPR LO CLOv; lia).
  unfold realloc_body. rewrite <- Hst, RC. unfold realloc_remap.
  destruct (Z.eqb_spec OL needed) as [EQ|NEQ].
  -
    eapply (implM_bind rsegs _ _ _ (fun _ s' ms' => POST (Some p) s' ms')); [| intros [] s' ms' H'; apply implM_ret; apply evt_done; exact H'].
    apply implM_upd. rewrite Hst.

    step. step. rewrite (unsigned_lit (Bg + stride * idx + 16)) by (clear - RrB0 RBC OL4096 STR I0; subst stride; lia).
    replace (A + - (Bg + stride * idx + 16)) with (16 * off) by (rewrite I0, HAE; clear; lia).
    step. step. step. step. rewrite ?(unsigned_lit (16 * off)) by (clear - Hoff; lia). step.
    step. rewrite ?(unsigned_lit (n + 4095 + 16 * off + 20)) by (clear - Hoff HN; lia). rewrite land_pgmask by (clear - Hoff HN; lia). rewrite <- NDE.
    step. rewrite (wz_unsigned mword) by exact MWR. rewrite land_pgmask by exact MWR. rewrite MWP.
    step. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by (clear - OL4096 RBC RrB0 ND62 ND4096; lia). 2:{ exfalso. clear - K0 EQ. lia. } clear K0.
    change (wz Bg) with (Z_to_bv 64 Bg).
    apply (remap_tail ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 m1 s LB LB0 p A old n lo B errv oldbs st g bg idx r off Bg
             PERM Hst RMR HBL AR Hin0 SL HM Hr Kr FC Ec CB HA Hoff FIT HO B0 BG16 Hidx SPAN RB0 K3 FR ST1 MI1 ERR1 AUX1 PRES1 OLDB OLEN SB CLO LOr TP HN SC RC).
    + exact RrB0.
    + exact RBAL.
    + pose_ceil. fold needed. clear - RBC EQ. lia.
    + fold needed. rewrite <- EQ. exact RF.
    + fold needed. rewrite <- EQ. exact DISJo.
    + intros; reflexivity.
    + fold needed. intros i Hi. exfalso. clear - Hi EQ. subst OL mr. lia.
    + fold needed. rewrite <- EQ. exact WRr.
    + intros; reflexivity.
    + intros x _ _ _ W; exact W.
  -
    assert (AVX : forall x k, ranges_free (live_ranges_except (strip st) (fst c)) x k = true -> 0 < k -> x + k <= 0x10000 \/ 0x8a000 <= x).
    { intros x k H Hk0. apply (rreserved_disjoint1 x k); [| exact Hk0]. unfold live_ranges_except in H. apply ranges_free_app_l in H.
      change (s_reserved (strip st)) with (s_reserved st) in H. rewrite Hres in H. exact H. }
    assert (AV : forall x k, ranges_free (live_ranges (strip st)) x k = true -> 0 < k -> x + k <= 0x10000 \/ 0x8a000 <= x).
    { intros x k H Hk0. apply (rreserved_disjoint1 x k); [| exact Hk0]. unfold live_ranges in H. apply ranges_free_app_l in H.
      change (s_reserved (strip st)) with (s_reserved st) in H. rewrite Hres in H. exact H. }
    pose proof GL as (GL1 & GL2 & GL3 & GL4 & GL5).
    eapply (implM_bind rsegs _ _ _ (fun a' s' ms' => s' = s /\
              rmremap_post (Z_to_bv 64 0x4b4f8) (Z_to_bv 64 sp1) gp tp (Z_to_bv 64 needed) (wz (conc st g)) (Z_to_bv 64 (A + old)) (Z_to_bv 64 (16 * off)) (Z_to_bv 64 4095)
                           (Z_to_bv 64 A) (Z_to_bv 64 n) s7 s8 s9 s10 s11 F fc Bg OL needed
                           (live_ranges_except (strip st) (fst c)) (live_ranges (strip st)) errv (wz ssp_canary) lo m1 a' ms')).
    { eapply implM_evt.
      { step. step. rewrite (unsigned_lit (Bg + stride * idx + 16)) by (clear - RrB0 RBC OL4096 STR I0; subst stride; lia).
        replace (A + - (Bg + stride * idx + 16)) with (16 * off) by (rewrite I0, HAE; clear; lia).
        step. step. step. step. rewrite ?(unsigned_lit (16 * off)) by (clear - Hoff; lia). step.
        step. rewrite ?(unsigned_lit (n + 4095 + 16 * off + 20)) by (clear - Hoff HN; lia). rewrite land_pgmask by (clear - Hoff HN; lia). rewrite <- NDE.
        step. rewrite (wz_unsigned mword) by exact MWR. rewrite land_pgmask by exact MWR. rewrite MWP.
        step. if_cases K0; zify_cond K0; rewrite ?unsigned_lit in K0 by (clear - OL4096 RBC RrB0 ND62 ND4096; lia). { exfalso. clear - K0 NEQ. lia. } clear K0.

        step. step. step. step. step. step. step.
        lazymatch goal with |- evt _ ?P ?ms => unify P (fun ms1 : machine_state => ms1 = ms) end. apply evt_done. reflexivity. }
      cbv beta. intros ms' ->.
      apply implM_of_enode. eapply impl_epost_mono; [| cbv beta; intros a' ms1 H1; split; [reflexivity| exact H1]].
      change (wz Bg) with (Z_to_bv 64 Bg).
      eapply rmremap_spec; [rewrite SP1; exact ST1| exact ERR1| exact GL4| exact GL5| exact MI1| reflexivity| reflexivity| reflexivity| reflexivity
        | clear - OL4096; lia| clear - ND62 ND4096; lia| exact NEQ| clear - RrB0; lia| pose_ceil; clear - RBC; lia| exact DRr| exact AVX| exact AV
        | rewrite SP1; subst sp1; clear - LO; lia| exact CLO| exact TP]. }
    cbv beta. intros a' s' ms' [-> PO].
    destruct a' as [e| |nb].
    +
      destruct PO as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m' & -> & MU & WM & MI' & ST' & ERR' & He).
      rewrite SP1 in MU, ST'. rewrite ETP in MU.
      replace (ret_pc (Z_to_bv 64 0x4b4f8)) with (Z_to_bv 64 0x4b4f8) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      assert (PEe : rpres_except (fun x => (sp1 - 112 <= x < sp1) \/ (429036 <= x < 429040)) m1 m').
      { eapply rpres_except_of_munch; [exact MU| exact WM|]. intros x Hx NC. cbn [outside]. clear - NC. repeat split; lia. }
      assert (RMR' : rmrep st m').
      { eapply (rmrep_transport_unowned st m1 m' _ RMR MU WM). intros lo' hi' x Hin Hx RFx.
        destruct (rrepfoot_where st m1 x RMR RFx) as [AC AW].
        destruct Hin as [E1|[E1|[]]]; injection E1 as <- <-; pose_ceil; unfold RCTX, RMLOCK, RLIBC, RGOT_SSP, RSSP_GUARD in *; subst sp1; clear - Hx AC AW CLOv LO; lia. }
      assert (FR' : rw_cells rsegs m' sp1 [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply rpres_except_rw_cells; [exact PEe| exact FR|]. cbn [cells_size csize Nat.add Z.of_nat]. cbv beta. intros x Hx. subst sp1. clear - Hx CLOv LO. lia. }
      assert (AUX' : rauxv_ok m' B).
      { eapply rauxv_ok_pres_B; [exact AUX1| exact PEe| cbv beta; intros x Hx; subst sp1; clear - Hx SB CLOv LO; lia| cbv beta; unfold RAUXV_CELL; intros x Hx; clear - Hx CLOv LO; lia]. }
      assert (PRES' : rpres_except (fun x => (lo <= x < bv_unsigned sp) \/ (RERRNO <= x < RERRNO + 4)) m m').
      { eapply rpres_except_trans; [exact PRES1|]. eapply rpres_except_mono; [exact PEe|]. cbv beta. unfold RERRNO. intros x Hx. subst sp1. clear - Hx LO. lia. }

      eapply implM_evt.
      { step. step. step. step. step. if_true.
        lazymatch goal with |- evt _ ?P ?ms => unify P (fun ms1 : machine_state => ms1 = ms) end. apply evt_done. reflexivity. }
      cbv beta. intros ms'' ->.
      exact (move_arm HMAL HFREE ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m' s LB LB0 p A old n lo B (Z_to_bv 64 e) oldbs st g bg idx r off
               PERM Hst RMR' HBL AR Hin0 SL FC Ec HA HO S16 B0 Hidx SPAN K3 FR' ST' MI' ERR' AUX' PRES' OLDB OLEN SB CLO LOr TP HN
               _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    +
      destruct PO as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m2' & -> & MU & WM & MI2 & MI' & ST' & ERR2 & GROW).
      rewrite SP1 in MU, ST'.
      replace (ret_pc (Z_to_bv 64 0x4b4f8)) with (Z_to_bv 64 0x4b4f8) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      assert (PE12 : rpres_except (fun x => sp1 - 112 <= x < sp1) m1 m2').
      { eapply rpres_except_of_munch; [exact MU| exact WM|]. intros x Hx NC. cbn [outside]. clear - NC. repeat split; lia. }
      assert (FR2' : rw_cells rsegs m2' sp1 [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply rpres_except_rw_cells; [exact PE12| exact FR|]. cbn [cells_size csize Nat.add Z.of_nat]. cbv beta. intros x Hx. clear - Hx. lia. }
      assert (W2 : wr_at rsegs m2' Bg OL).
      { eapply rpres_except_wr_at; [exact PE12| exact WRr|]. cbv beta. intros x Hx. subst sp1. clear - Hx RBC CLOv LO. lia. }
      assert (WV : forall x : word, m2' x = m1 x \/ wview rsegs m2' x <> None -> forall mx : mem, mx x = m2' x -> wview rsegs m1 x <> None -> wview rsegs mx x <> None).
      { intros x Hx mx Ex W. unfold wview in *. rewrite Ex. destruct Hx as [E1|W1]; [rewrite E1; exact W| exact W1]. }
      unfold rmremap_same_mem in MI', ST' |- *. destruct (needed <? OL) eqn:CMP; [apply Z.ltb_lt in CMP| apply Z.ltb_ge in CMP].
      *
        set (mm := apply_unmaps m2' [(wa (Bg + needed), Z_to_bv 64 (OL - needed))]) in *.
        assert (Ha : 0 <= Bg + needed < 2^64) by (clear - RrB0 RBC ND4096 CMP; lia).
        assert (Hn : 0 <= OL - needed < 2^64) by (clear - RrB0 RBC ND4096 CMP; lia).
        assert (Han : Bg + needed + (OL - needed) <= 2^64) by (clear - RrB0 RBC; lia).
        assert (OUT : forall x : word, (bv_unsigned x < Bg + needed \/ Bg + OL <= bv_unsigned x) -> mm x = m2' x).
        { intros x Hx. subst mm. apply (unmaps_outside m2' _ _ Ha Hn Han). clear - Hx. lia. }
        assert (FRmm : rw_cells rsegs mm sp1 [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
        { subst mm. apply (rw_cells_unmaps_other rsegs m2' _ _ Ha Hn Han _ _ FR2'). cbn [cells_size csize Nat.add Z.of_nat]. subst sp1. clear - RBC CLOv LO. lia. }
        assert (ERRmm : rw_cells rsegs mm (errno_addr tp) [C4 errv]).
        { subst mm. apply (rw_cells_unmaps_other rsegs m2' _ _ Ha Hn Han _ _ ERR2). rewrite ETP. cbn [cells_size csize Nat.add Z.of_nat]. clear - DRr ND4096; lia. }
        assert (PEM0 : rpres_except (fun x => (Bg + needed <= x < Bg + OL) \/ (sp1 - 112 <= x < sp1)) m1 mm).
        { intros x Hx NC. assert (E1 : mm (wa x) = m2' (wa x)) by (apply OUT; rewrite wa_unsigned by exact Hx; clear - NC ND4096; lia).
          destruct (PE12 x Hx ltac:(cbv beta; clear - NC; tauto)) as [E2 W2']. split; [rewrite E1; exact E2|]. intros W. apply (WV (wa x) (or_introl E2) mm E1 W). }
        assert (AUXmm : rauxv_ok mm B).
        { eapply rauxv_ok_pres_B; [exact AUX1| exact PEM0| cbv beta; intros x Hx; subst sp1; clear - Hx SB RBC CLOv LO; lia| cbv beta; unfold RAUXV_CELL; intros x Hx; subst sp1; clear - Hx DRr OL4096 ND4096 CLOv LO; lia]. }
        assert (NCEILx : Bg + needed <= alloc_ceiling) by (pose_ceil; clear - RBC CMP; lia).
        assert (RFRx : ranges_free ref_reserved Bg needed = true) by (eapply ranges_free_sub; [exact RF| clear; lia| clear - CMP; lia| clear - ND4096; lia]).
        assert (DISJx : forall rid2 r2, s_regions st !! rid2 = Some r2 -> rid2 <> fst bg -> let '(b2, l2) := region_live_range r2 in Bg + needed <= b2 \/ b2 + l2 <= Bg).
        { intros rid2 r2 H2 NE2. specialize (DISJo rid2 r2 H2 NE2). destruct (region_live_range r2) as [b2 l2]. clear - DISJo CMP. lia. }
        assert (COPYx : forall i, 0 <= i < kt -> mm (wa (Bg + i)) = m1 (wa (Bg + i))).
        { intros i Hi. subst kt. rewrite OUT by (rewrite wa_unsigned by (clear - Hi RrB0 RBC ND4096; lia); clear - Hi ND4096; lia).
          apply (proj1 (PE12 (Bg + i) ltac:(clear - Hi RrB0 RBC; lia) ltac:(cbv beta; subst sp1; clear - Hi RBC CLOv LO; lia))). }
        assert (ZEROx : forall i, kt <= i < needed -> mm (wa (Bg + i)) = Some (b8 0)) by (intros i Hi; exfalso; subst kt; clear - Hi CMP; lia).
        assert (WRNx : wr_at rsegs mm Bg needed).
        { subst mm. apply (wr_at_unmaps_other rsegs m2' _ _ Ha Hn Han); [| clear; lia]. eapply wr_at_sub; [exact W2| clear; lia| clear - CMP; lia]. }
        assert (AGMx : forall x, 0 <= x < 2^64 -> ~ (Bg <= x < Bg + OL) -> ~ (Bg <= x < Bg + needed) -> ~ (lo <= x < sp1) -> mm (wa x) = m1 (wa x)).
        { intros x Hx N1 N2 N3. apply (proj1 (PEM0 x Hx ltac:(cbv beta; subst sp1; clear - N1 N3 LO CLOv ND4096; lia))). }
        assert (WMMx : forall x, 0 <= x < 2^64 -> ~ (Bg <= x < Bg + OL) -> ~ (Bg <= x < Bg + needed) -> wview rsegs m1 (wa x) <> None -> wview rsegs mm (wa x) <> None).
        { intros x Hx N1 N2 W. apply (WV (wa x) (or_intror (WM _ W)) mm); [apply OUT; rewrite wa_unsigned by exact Hx; clear - N1 ND4096; lia| exact W]. }

        eapply implM_evt.
        { step. step. step. lazymatch goal with |- evt _ ?P ?ms => unify P (fun ms1 : machine_state => ms1 = ms) end. apply evt_done. reflexivity. }
        cbv beta. intros ms'' ->.
        eapply (implM_bind rsegs _ _ _ (fun _ s'' ms'' => POST (Some p) s'' ms'')); [| intros [] s'' ms'' H'; apply implM_ret; apply evt_done; exact H'].
        apply implM_upd. rewrite Hst.
        exact (remap_tail ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 mm s LB LB0 p A old n lo B errv oldbs st g bg idx r off Bg
                 PERM Hst RMR HBL AR Hin0 SL HM Hr Kr FC Ec CB HA Hoff FIT HO B0 BG16 Hidx SPAN RB0 K3 FRmm ST' MI' ERRmm AUXmm PRES1 OLDB OLEN SB CLO LOr TP HN SC RC
                 RrB0 RBAL NCEILx RFRx DISJx COPYx ZEROx WRNx AGMx WMMx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
      *
        assert (OLT : OL < needed) by (clear - CMP NEQ; lia).
        destruct (GROW CMP) as [NCEIL' RFA]. pose proof NCEIL' as NCEILv. pose_ceil.
        set (mm := apply_zeros m2' [(wa (Bg + OL), Z_to_bv 64 (needed - OL))]) in *.
        assert (Ha : 0 <= Bg + OL < 2^64) by (clear - RrB0 RBC OL4096; lia).
        assert (Hn : 0 <= needed - OL < 2^64) by (clear - OLT ND62 OL4096; lia).
        assert (Han : Bg + OL + (needed - OL) <= 2^64) by (clear - RrB0 NCEILv; lia).
        assert (IMGx : Bg + needed <= 0x10000 \/ 0x8a000 <= Bg).
        { pose proof (AVX _ _ RFA ltac:(clear - OLT; lia)) as X. clear - X DRr OL4096 OLT. lia. }
        assert (OUT : forall x : word, (bv_unsigned x < Bg + OL \/ Bg + needed <= bv_unsigned x) -> mm x = m2' x).
        { intros x Hx. subst mm. apply (zeros_outside m2' _ _ Ha Hn Han). clear - Hx. lia. }
        assert (FRmm : rw_cells rsegs mm sp1 [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
        { subst mm. apply (rw_cells_zeros_other rsegs m2' _ _ Ha Hn Han _ _ FR2'). cbn [cells_size csize Nat.add Z.of_nat]. subst sp1. clear - NCEILv CLOv LO. lia. }
        assert (ERRmm : rw_cells rsegs mm (errno_addr tp) [C4 errv]).
        { subst mm. apply (rw_cells_zeros_other rsegs m2' _ _ Ha Hn Han _ _ ERR2). rewrite ETP. cbn [cells_size csize Nat.add Z.of_nat]. clear - IMGx OL4096; lia. }
        assert (PEM0 : rpres_except (fun x => (Bg + OL <= x < Bg + needed) \/ (sp1 - 112 <= x < sp1)) m1 mm).
        { intros x Hx NC. assert (E1 : mm (wa x) = m2' (wa x)) by (apply OUT; rewrite wa_unsigned by exact Hx; clear - NC ND4096; lia).
          destruct (PE12 x Hx ltac:(cbv beta; clear - NC; tauto)) as [E2 W2']. split; [rewrite E1; exact E2|]. intros W. apply (WV (wa x) (or_introl E2) mm E1 W). }
        assert (AUXmm : rauxv_ok mm B).
        { eapply rauxv_ok_pres_B; [exact AUX1| exact PEM0| cbv beta; intros x Hx; subst sp1; clear - Hx SB NCEILv CLOv LO; lia| cbv beta; unfold RAUXV_CELL; intros x Hx; subst sp1; clear - Hx IMGx OL4096 ND4096 CLOv LO; lia]. }
        assert (RFRx : ranges_free ref_reserved Bg needed = true) by (apply rreserved_free_intro; [clear - RrB0; lia| exact IMGx]).
        assert (LRPOS : forall q rq, s_regions st !! q = Some rq -> let '(b2, l2) := region_live_range rq in 0 < l2).
        { intros q rq Hq. destruct (ir_shape _ _ _ IR _ _ Hq) as (_ & _ & LEN & _ & _ & MK). pose proof (round_up_pg_ge (r_len rq)) as UP.
          unfold region_live_range, is_metakind in *. destruct (r_kind rq); unfold PGSZ in *;
            first [specialize (MK (or_introl eq_refl)); clear - LEN MK UP; lia| specialize (MK (or_intror eq_refl)); clear - LEN MK UP; lia| clear - LEN UP; lia]. }
        assert (DISJx : forall rid2 r2, s_regions st !! rid2 = Some r2 -> rid2 <> fst bg -> let '(b2, l2) := region_live_range r2 in Bg + needed <= b2 \/ b2 + l2 <= Bg).
        { intros rid2 r2 H2 NE2. specialize (DISJo rid2 r2 H2 NE2). specialize (LRPOS rid2 r2 H2).
          pose proof (In_live_ranges_except (strip st) (fst c) rid2 r2 H2 ltac:(rewrite FC; exact NE2)) as IN2.
          destruct (region_live_range r2) as [b2 l2]. pose proof (ranges_free_In _ _ _ _ _ RFA IN2) as D2. clear - DISJo LRPOS D2 OLT. lia. }
        assert (COPYx : forall i, 0 <= i < kt -> mm (wa (Bg + i)) = m1 (wa (Bg + i))).
        { intros i Hi. subst kt. rewrite OUT by (rewrite wa_unsigned by (clear - Hi RrB0 RBC ND4096; lia); clear - Hi ND4096; lia).
          apply (proj1 (PE12 (Bg + i) ltac:(clear - Hi RrB0 RBC; lia) ltac:(cbv beta; subst sp1; clear - Hi RBC CLOv LO; lia))). }
        assert (ZEROx : forall i, kt <= i < needed -> mm (wa (Bg + i)) = Some (b8 0)).
        { intros i Hi. subst kt mm. unfold b8. apply (zeros_inside m2' _ _ Ha Hn Han). rewrite wa_unsigned by (clear - Hi RrB0 NCEILv OL4096; lia). clear - Hi OLT; lia. }
        assert (WRNx : wr_at rsegs mm Bg needed).
        { replace needed with (OL + (needed - OL)) by (clear; lia). subst mm. apply wr_at_app; [| apply (wr_at_zeros_new rsegs m2' _ _ Ha Hn Han)| clear - OL4096; lia| clear - OLT; lia].
          apply (wr_at_zeros rsegs m2' _ _ Ha Hn Han). exact W2. }
        assert (AGMx : forall x, 0 <= x < 2^64 -> ~ (Bg <= x < Bg + OL) -> ~ (Bg <= x < Bg + needed) -> ~ (lo <= x < sp1) -> mm (wa x) = m1 (wa x)).
        { intros x Hx N1 N2 N3. apply (proj1 (PEM0 x Hx ltac:(cbv beta; subst sp1; clear - N2 N3 LO CLOv OL4096; lia))). }
        assert (WMMx : forall x, 0 <= x < 2^64 -> ~ (Bg <= x < Bg + OL) -> ~ (Bg <= x < Bg + needed) -> wview rsegs m1 (wa x) <> None -> wview rsegs mm (wa x) <> None).
        { intros x Hx N1 N2 W. apply (WV (wa x) (or_intror (WM _ W)) mm); [apply OUT; rewrite wa_unsigned by exact Hx; clear - N2 OL4096 ND4096; lia| exact W]. }

        eapply implM_evt.
        { step. step. step. lazymatch goal with |- evt _ ?P ?ms => unify P (fun ms1 : machine_state => ms1 = ms) end. apply evt_done. reflexivity. }
        cbv beta. intros ms'' ->.
        eapply (implM_bind rsegs _ _ _ (fun _ s'' ms'' => POST (Some p) s'' ms'')); [| intros [] s'' ms'' H'; apply implM_ret; apply evt_done; exact H'].
        apply implM_upd. rewrite Hst.
        exact (remap_tail ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 mm s LB LB0 p A old n lo B errv oldbs st g bg idx r off Bg
                 PERM Hst RMR HBL AR Hin0 SL HM Hr Kr FC Ec CB HA Hoff FIT HO B0 BG16 Hidx SPAN RB0 K3 FRmm ST' MI' ERRmm AUXmm PRES1 OLDB OLEN SB CLO LOr TP HN SC RC
                 RrB0 RBAL NCEIL' RFRx DISJx COPYx ZEROx WRNx AGMx WMMx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    +
      destruct PO as (x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & m2' & -> & MU & WM & MI2 & MI' & ST' & ERR2 & (NBne & NBA' & NB0' & NCEIL' & RFA & OLT)).
      rewrite SP1 in MU, ST'. pose proof NCEIL' as NCEILv. pose_ceil.
      replace (ret_pc (Z_to_bv 64 0x4b4f8)) with (Z_to_bv 64 0x4b4f8) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
      assert (PE12 : rpres_except (fun x => sp1 - 112 <= x < sp1) m1 m2').
      { eapply rpres_except_of_munch; [exact MU| exact WM|]. intros x Hx NC. cbn [outside]. clear - NC. repeat split; lia. }
      assert (FR2' : rw_cells rsegs m2' sp1 [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply rpres_except_rw_cells; [exact PE12| exact FR|]. cbn [cells_size csize Nat.add Z.of_nat]. cbv beta. intros x Hx. clear - Hx. lia. }
      assert (W2 : wr_at rsegs m2' Bg OL).
      { eapply rpres_except_wr_at; [exact PE12| exact WRr|]. cbv beta. intros x Hx. subst sp1. clear - Hx RBC CLOv LO. lia. }
      assert (WV : forall x : word, m2' x = m1 x \/ wview rsegs m2' x <> None -> forall mx : mem, mx x = m2' x -> wview rsegs m1 x <> None -> wview rsegs mx x <> None).
      { intros x Hx mx Ex W. unfold wview in *. rewrite Ex. destruct Hx as [E1|W1]; [rewrite E1; exact W| exact W1]. }
      assert (RFRx : ranges_free ref_reserved nb needed = true).
      { unfold live_ranges in RFA. pose proof (ranges_free_app_l _ _ _ _ RFA) as X. change (s_reserved (strip st)) with (s_reserved st) in X. rewrite Hres in X. exact X. }
      pose proof (rreserved_disjoint1 _ _ RFRx ltac:(clear - ND4096; lia)) as DRn.
      unfold rmremap_move_mem in MI', ST' |- *.
      set (mz := apply_zeros (apply_unmaps m2' [(wa Bg, Z_to_bv 64 OL)]) [(wa (nb + OL), Z_to_bv 64 (needed - OL))]) in *.
      set (mm := apply_copies m2' mz [ {| copy_src := wa Bg; copy_dst := Z_to_bv 64 nb; copy_len := Z_to_bv 64 OL |} ]) in *.
      assert (Hua : 0 <= Bg < 2^64) by (clear - RrB0 RBC OL4096; lia). assert (Hun : 0 <= OL < 2^64) by (clear - OL4096 RBC RrB0; lia). assert (Huan : Bg + OL <= 2^64) by (clear - RBC; lia).
      assert (Hza : 0 <= nb + OL < 2^64) by (clear - NB0' NCEILv OL4096 OLT; lia). assert (Hzn : 0 <= needed - OL < 2^64) by (clear - OLT ND62 OL4096; lia).
      assert (Hzan : nb + OL + (needed - OL) <= 2^64) by (clear - NCEILv; lia).
      assert (Hcs : 0 <= Bg /\ Bg + OL <= 2^64) by (clear - RrB0 RBC; lia). assert (Hcd : 0 <= nb /\ nb + OL <= 2^64) by (clear - NB0' NCEILv OLT; lia).
      assert (Hcl : 0 < OL < 2^64) by (clear - OL4096 RBC RrB0; lia).
      assert (OUTz : forall x : word, (bv_unsigned x < Bg \/ Bg + OL <= bv_unsigned x) -> (bv_unsigned x < nb + OL \/ nb + needed <= bv_unsigned x) -> mz x = m2' x).
      { intros x H1 H2. subst mz. rewrite (zeros_outside _ _ _ Hza Hzn Hzan) by (clear - H2; lia). apply (unmaps_outside m2' _ _ Hua Hun Huan). exact H1. }
      assert (OUT : forall x : word, (bv_unsigned x < Bg \/ Bg + OL <= bv_unsigned x) -> (bv_unsigned x < nb \/ nb + needed <= bv_unsigned x) -> mm x = m2' x).
      { intros x H1 H2. subst mm. rewrite (copies_outside m2' mz Bg nb OL Hcs Hcd Hcl) by (clear - H2 OLT; lia). apply OUTz; [exact H1| clear - H2 OL4096; lia]. }
      assert (FRmm : rw_cells rsegs mm sp1 [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { subst mm mz. apply (rw_cells_copies_other rsegs m2' _ Bg nb OL Hcs Hcd Hcl); [| cbn [cells_size csize Nat.add Z.of_nat]; subst sp1; clear - NCEILv OLT CLOv LO; lia].
        apply (rw_cells_zeros_other rsegs _ _ _ Hza Hzn Hzan); [| cbn [cells_size csize Nat.add Z.of_nat]; subst sp1; clear - NCEILv CLOv LO; lia].
        apply (rw_cells_unmaps_other rsegs m2' _ _ Hua Hun Huan _ _ FR2'). cbn [cells_size csize Nat.add Z.of_nat]. subst sp1. clear - RBC CLOv LO. lia. }
      assert (ERRmm : rw_cells rsegs mm (errno_addr tp) [C4 errv]).
      { subst mm mz. rewrite ETP. apply (rw_cells_copies_other rsegs m2' _ Bg nb OL Hcs Hcd Hcl); [| cbn [cells_size csize Nat.add Z.of_nat]; clear - DRn OL4096 OLT; lia].
        apply (rw_cells_zeros_other rsegs _ _ _ Hza Hzn Hzan); [| cbn [cells_size csize Nat.add Z.of_nat]; clear - DRn OL4096 OLT; lia].
        rewrite <- ETP. apply (rw_cells_unmaps_other rsegs m2' _ _ Hua Hun Huan _ _ ERR2). rewrite ETP. cbn [cells_size csize Nat.add Z.of_nat]. clear - DRr OL4096; lia. }
      assert (PEM0 : rpres_except (fun x => (Bg <= x < Bg + OL) \/ (nb <= x < nb + needed) \/ (sp1 - 112 <= x < sp1)) m1 mm).
      { intros x Hx NC. assert (E1 : mm (wa x) = m2' (wa x)) by (apply OUT; rewrite wa_unsigned by exact Hx; clear - NC ND4096; lia).
        destruct (PE12 x Hx ltac:(cbv beta; clear - NC; tauto)) as [E2 W2']. split; [rewrite E1; exact E2|]. intros W. apply (WV (wa x) (or_introl E2) mm E1 W). }
      assert (AUXmm : rauxv_ok mm B).
      { eapply rauxv_ok_pres_B; [exact AUX1| exact PEM0| cbv beta; intros x Hx; subst sp1; clear - Hx SB NCEILv RBC CLOv LO; lia| cbv beta; unfold RAUXV_CELL; intros x Hx; subst sp1; clear - Hx DRr DRn OL4096 ND4096 CLOv LO; lia]. }
      assert (DISJx : forall rid2 r2, s_regions st !! rid2 = Some r2 -> rid2 <> fst bg -> let '(b2, l2) := region_live_range r2 in nb + needed <= b2 \/ b2 + l2 <= nb).
      { intros rid2 r2 H2 NE2. pose proof (In_live_ranges (strip st) rid2 r2 H2) as IN2.
        destruct (region_live_range r2) as [b2 l2]. exact (ranges_free_In _ _ _ _ _ RFA IN2). }
      assert (COPYx : forall i, 0 <= i < kt -> mm (wa (nb + i)) = m1 (wa (Bg + i))).
      { intros i Hi. subst kt mm. rewrite (copies_inside m2' mz Bg nb OL Hcs Hcd Hcl) by (clear - Hi; lia).
        apply (proj1 (PE12 (Bg + i) ltac:(clear - Hi RrB0 RBC; lia) ltac:(cbv beta; subst sp1; clear - Hi RBC CLOv LO; lia))). }
      assert (ZEROx : forall i, kt <= i < needed -> mm (wa (nb + i)) = Some (b8 0)).
      { intros i Hi. subst kt mm. unfold b8. rewrite (copies_outside m2' mz Bg nb OL Hcs Hcd Hcl) by (rewrite wa_unsigned by (clear - Hi NB0' NCEILv OL4096; lia); clear - Hi; lia).
        subst mz. apply (zeros_inside _ _ _ Hza Hzn Hzan). rewrite wa_unsigned by (clear - Hi NB0' NCEILv OL4096; lia). clear - Hi OLT; lia. }
      assert (WRNx : wr_at rsegs mm nb needed).
      { replace needed with (OL + (needed - OL)) by (clear; lia). apply wr_at_app; [| | clear - OL4096; lia| clear - OLT; lia].
        - split; [clear - NB0'; lia|]. split; [clear - NCEILv OLT; lia|]. intros i Hi. subst mm.
          rewrite ref_wview_overlay by (rewrite wa_unsigned by (clear - Hi NB0' NCEILv OLT; lia); clear - Hi DRn OLT; lia).
          rewrite (copies_inside m2' mz Bg nb OL Hcs Hcd Hcl i Hi).
          destruct W2 as (_ & _ & W2i). specialize (W2i i Hi). rewrite ref_wview_overlay in W2i by (rewrite wa_unsigned by (clear - Hi RrB0 RBC; lia); clear - Hi DRr; lia). exact W2i.
        - subst mm. apply (wr_at_copies_other rsegs m2' mz Bg nb OL Hcs Hcd Hcl); [| clear; lia]. subst mz. apply (wr_at_zeros_new rsegs _ _ _ Hza Hzn Hzan). }
      assert (AGMx : forall x, 0 <= x < 2^64 -> ~ (Bg <= x < Bg + OL) -> ~ (nb <= x < nb + needed) -> ~ (lo <= x < sp1) -> mm (wa x) = m1 (wa x)).
      { intros x Hx N1 N2 N3. apply (proj1 (PEM0 x Hx ltac:(cbv beta; subst sp1; clear - N1 N2 N3 LO CLOv; lia))). }
      assert (WMMx : forall x, 0 <= x < 2^64 -> ~ (Bg <= x < Bg + OL) -> ~ (nb <= x < nb + needed) -> wview rsegs m1 (wa x) <> None -> wview rsegs mm (wa x) <> None).
      { intros x Hx N1 N2 W. apply (WV (wa x) (or_intror (WM _ W)) mm); [apply OUT; rewrite wa_unsigned by exact Hx; [clear - N1; lia| clear - N2; lia]| exact W]. }

      eapply implM_evt.
      { step. step. step. lazymatch goal with |- evt _ ?P ?ms => unify P (fun ms1 : machine_state => ms1 = ms) end. apply evt_done. reflexivity. }
      cbv beta. intros ms'' ->.
      eapply (implM_bind rsegs _ _ _ (fun _ s'' ms'' => POST (Some p) s'' ms'')); [| intros [] s'' ms'' H'; apply implM_ret; apply evt_done; exact H'].
      apply implM_upd. rewrite Hst.
      exact (remap_tail ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 mm s LB LB0 p A old n lo B errv oldbs st g bg idx r off nb
               PERM Hst RMR HBL AR Hin0 SL HM Hr Kr FC Ec CB HA Hoff FIT HO B0 BG16 Hidx SPAN RB0 K3 FRmm ST' MI' ERRmm AUXmm PRES1 OLDB OLEN SB CLO LOr TP HN SC RC
               NB0' NBA' NCEIL' RFRx DISJx COPYx ZEROx WRNx AGMx WMMx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
Qed.
End P.

End CEIL.
End TwinB.
