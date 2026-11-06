(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocKit_A Malloc_iface Malloc_ifaceP.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocFacts_A MallocBlocks MallocHINV MallocFacts_B MallocFacts_R.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree Malloc MallocCtrl Monad RawAlloc Realloc ReallocKeep MI_Inv MI_Read.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import Malloc_fp MallocKit_B MallocKit_B2 F_ntf F_free_K F_free F_free_spec F_malloc_join F_malloc_entry.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.U Require Import UMallocRep UMallocTree UMallocTreeX UMallocKit_B UMallocKit_B2 UMalloc_fp UMalloc_iface UMalloc_ifaceP UF_malloc_implT UF_realloc_hdr UF_realloc_ip UF_realloc_A UF_realloc_mv.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require MallocFacts_inv MallocFacts_inv2 MallocFacts_inv3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation RAREACH := (AREACH_from ref_reserved).
Notation RMFACTS := (@MFACTS_g ref_reserved).

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition RREALLOC_STACK_MIN : Z := 8256.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rbig_tree (st : mstate) (pf g : aptr) (idx n : Z) : MX (mstate * optr) :=
  let mr := get_meta_rec st g in
  let stride := get_stride mr in
  let start := slot_start' mr idx in
  let base := snd pf - snd start in
  let needed := round_up_pg (n + base + UNIT + IB) in
  let maplen4096 := m_maplen mr * 4096 in
  let gmem := default (0%N, 0) (m_mem mr) in
  if maplen4096 =? needed then
    SRet (realloc_big_tail st gmem base idx needed n)
  else if PTRDIFF_MAX <=? needed then
    realloc_move st pf n
  else
    SVis (XMremap (conc st gmem) maplen4096 needed MREMAP_MAYMOVE) (fun r =>
      if negb (mremap_answer_ok (live_ranges st) (conc st gmem) maplen4096 needed r)
      then xbad_answer (SRet (st, None))
      else if is_err r then realloc_move st pf n
      else SRet (realloc_big_tail (remap_region (fst gmem) g r needed st) gmem base idx needed n)).

Section SIG.
Variables (gp tp : word) (s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo B : Z).

(* [comment removed for export] *)
Definition rbig_stmt : Prop :=
  forall (ra sp s0 s1 s2 s3 s4 s5 s6 : word) (a0 a1 t2 t3 t4 t5 t6 : word)
         (o m0 m1 : mem) (s : PState) (st0 : mstate) (LB : list block) (b : block) (pf g bm : aptr) (i : Z)
         (n : Z) (old : list byte) (errv : word) (off rsv : Z),
  let st := set_tick (N.succ (s_tick st0)) st0 in
  let mr := get_meta_rec st g in
  let stride := get_stride mr in
  let S := conc st (blk_slot b) in
  let P := blk_addr b in
  alloc_ceiling <= lo -> tp = Z_to_bv 64 RATP ->
  RAREACH st0 LB -> rmrep st m1 -> brk_link_ps st0 s -> unk_agree st o m1 ->
  In b LB -> fst pf = fst (blk_slot b) -> conc st0 pf = blk_addr b -> s_slots st0 !! blk_slot b = Some (g, i) ->
  m_mem mr = Some bm -> fst bm = fst pf -> 0 <= off -> 0 <= rsv ->
  snd (blk_slot b) = snd bm + UNIT + stride * i -> snd pf = snd (blk_slot b) + UNIT * off ->
  rsv = stride - IB - UNIT * off - blk_size b -> m_sizeclass mr = 63 -> MMAP_THRESHOLD <= n ->
  realloc_hdr st pf = ret (Some (g, i, blk_size b)) ->
  bytes_at usegs m1 (blk_addr b) old -> Z.of_nat (length old) = blk_size b ->
  rauxv_ok m1 B -> bv_unsigned sp <= B ->
  stk usegs m1 lo (bv_unsigned sp - 64) -> lo <= bv_unsigned sp - RREALLOC_STACK_MIN ->
  rw_cells usegs m1 (bv_unsigned sp + -64) (rre_frame s6 s5 s4 s3 s2 s1 s0 ra) ->
  rw_cells usegs m1 (errno_addr tp) [C4 errv] -> mem_inv usegs m1 ->
  rheap_pres LB (bv_unsigned sp) m0 m1 ->
  a0 = Z_to_bv 64 (blk_addr b) -> a1 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  rimplTX o (rbig_tree st pf g i n) s
    (rreallocT_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB b n lo B old m0)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 (S + stride - 4)) (Z_to_bv 64 S) t2
             s0 (wz (conc st g)) a0 a1 (wz (conc st bm)) (Z_to_bv 64 63) (wz (meta_word mr)) (Z_to_bv 64 63)
             (Z_to_bv 64 (S + stride)) (Z_to_bv 64 (S + stride - 4 - P)) (Z_to_bv 64 (S + stride - 4 - rsv))
             s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x19d7c) fc None m1 (seg_rom usegs)).
End SIG.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma set_size_b3 p e n b b' st : Z.land b 31 = Z.land b' 31 -> set_size p e n b st = set_size p e n b' st.
Proof. intros H. unfold set_size. rewrite H. reflexivity. Qed.

Lemma ctx_havoc p n st : ctx (havoc p n st) = ctx st.
Proof. unfold havoc. destruct (n <=? 0); reflexivity. Qed.
Lemma ctx_set_size p e n b st : ctx (set_size p e n b st) = ctx st.
Proof. unfold set_size. destruct (negb _); destruct (5 <=? _); reflexivity. Qed.

(* [comment removed for export] *)
End RC__1.
Ltac rss_mw := first [apply munch_refl | apply munch_write; [rss_mw| lia| cbn; rewrite ?length_le4; cbn; lia| cbn; rewrite ?length_le4; cbn; lia]].
Ltac rss_ww := first [apply wmono_refl | apply wmono_write; rss_ww].
Ltac rss_fw H := first [exact H | apply rw_cells_frame; [rss_fw H| lia| cbn; rewrite ?length_le4; cbn; lia| cbn; rewrite ?length_le4; cbn; lia]].

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma rset_size_mem_fp m P E n k :
  3 <= P -> 0 <= n -> P + n <= E -> E <= 2^64 -> 0 <= E - P - n < 2^32 ->
  munch [(P - 3, E)] m (rset_size_mem m P E n k) /\ wmono usegs m (rset_size_mem m P E n k)
  /\ (forall A cs, rw_cells usegs m A cs -> P <= A -> A + Z.of_nat (cells_size cs) <= P + n -> rw_cells usegs (rset_size_mem m P E n k) A cs).
Proof.
  intros P3 N0 PNE E64 R32. unfold rset_size_mem. cbv zeta.
  destruct (Z.eqb_spec (E - P - n) 0) as [R0|R0]; destruct (Z.leb_spec 5 (E - P - n)) as [L5|L5]; cbv beta iota; try lia.
  all: split; [rss_mw|]; split; [rss_ww|]; intros A cs H HA HB; rss_fw H.
Qed.

Section REALLOC.
Variables (gp tp : word) (s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (lo B : Z).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis TP : tp = Z_to_bv 64 RATP.
Hypothesis RBIG : rbig_stmt gp tp s7 s8 s9 s10 s11 F fc lo B.
Theorem rrealloc_walk_gen :
  forall (ra sp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 t3 t4 t5 t6 : word)
         (m : mem) (s : PState) (st0 : mstate) (LB : list block) (b : block) (pf : aptr) (n : Z) (old : list byte) (errv : word),
  RAREACH st0 LB -> rmrep st0 m -> brk_link_ps st0 s ->
  In b LB -> fst pf = fst (blk_slot b) -> conc st0 pf = blk_addr b ->
  bytes_at usegs m (blk_addr b) old -> Z.of_nat (length old) = blk_size b ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - RREALLOC_STACK_MIN ->
  rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m ->
  a0 = Z_to_bv 64 (blk_addr b) -> a1 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  rimplTX m (realloc st0 (Some pf) n) s
    (rreallocT_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB b n lo B old m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 rrealloc_entry) fc None m (seg_rom usegs)).
Proof.
  intros until errv. intros AR MR0 BL Hb Hfst Hconc OLD LEN AUXB SB ST SLO ERR MI A0 A1 N.
  unfold RREALLOC_STACK_MIN in SLO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof LO as CLO. unfold alloc_ceiling in CLO.
  set (t := N.succ (s_tick st0)). set (st := set_tick t st0).
  assert (AR1 : RAREACH st LB) by (apply areach_tick; [exact AR| subst t; lia]).
  pose proof (MallocFacts_inv3.areach_cinv_proof _ _ AR1) as C1.
  pose proof (MallocFacts_inv3.areach_cinv_proof _ _ AR) as C0.
  pose proof (ci_ticks _ _ C1) as TK.
  assert (MR : rmrep st m) by (apply rmrep_set_tick; exact MR0).
  pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C0) b Hb) as [(g & i & bb0 & SL & _) _ _].
  (* [comment removed for export] *)
  unfold realloc. replace (size_overflows n) with false by (symmetry; unfold size_overflows; apply Z.leb_gt; lia).
  change (set_tick (N.succ (s_tick st0)) st0) with st.
  eapply (rrealloc_hdr_phase gp tp F fc lo LO ra sp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
            m m s st0 LB b pf n t g i); first [exact AR| exact MR| exact MI| exact Hb| exact Hfst| exact Hconc| exact SL| exact ST| exact A0| exact A1| exact N| idtac].
  { subst t; lia. }
  { lia. }
  intros ms1 bm off rsv Hmem Fbm OFF0 RSV0 Eslot Epf Ersv Ii S16 SCR SCF HDREQ HQ.
  destruct HQ as (xt2 & xt3 & xt4 & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & MR1).
  cbv beta iota. fold st. fold st in Hmem, Eslot, Ersv, Ii, S16, SCR, SCF, HDREQ, MR1.
  (* [comment removed for export] *)
  lazymatch goal with |- rimplTX _ (if _ then _ else if _ then xguard 70 ?c ?BODY ?bail else _) _ _ _ =>
    change BODY with (rbig_tree st pf g i n) end.
  set (BT := rbig_tree st pf g i n).
  set (mr := get_meta_rec st g) in *. set (stride := get_stride mr) in *.
  (* [comment removed for export] *)
  pose proof (ci_gmetas _ _ C1 bm g ltac:(destruct (areach_blk_hdr st LB b pf AR1 Hb Hfst Hconc g i SL) as (bm' & o' & r' & q' & Hm' & _ & HO & _);
                                         change (get_meta_rec st g) with mr in Hm'; rewrite Hmem in Hm'; inversion Hm'; subst; exact HO)) as GO.
  destruct (go_region _ _ _ GO) as (r & Hr & Kr & B0 & B16 & SPAN & TOP). change (get_meta_rec st g) with mr in SPAN, TOP.
  pose proof (go_li _ _ _ GO) as LI. change (get_meta_rec st g) with mr in LI.
  unfold sstart_of in SPAN. rewrite Hmem in SPAN. cbn [default id snd] in SPAN. fold stride in SPAN.
  pose proof MR1 as (WF & _ & _ & _ & _ & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
  destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF).
  assert (Hrp : s_regions st !! fst pf = Some r) by (rewrite <- Fbm; exact Hr).
  assert (HP : blk_addr b = r_base r + snd pf) by (rewrite <- Hconc; apply (conc_region' st pf r Hrp)).
  assert (HS : conc st (blk_slot b) = r_base r + snd (blk_slot b)) by (apply conc_region'; rewrite <- Hfst; exact Hrp).
  assert (HBm : conc st bm = r_base r + snd bm) by (apply conc_region'; exact Hr).
  assert (SI0 : 0 <= stride * i) by (apply Z.mul_nonneg_nonneg; lia).
  assert (SIL : stride * (i + 1) <= stride * (m_last_idx mr + 1)) by (apply Z.mul_le_mono_nonneg_l; lia).
  rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL.
  assert (ETOP : snd (blk_slot b) + stride <= round_up_pg (r_len r)) by (rewrite Eslot; unfold UNIT in *; lia).
  pose proof (rreserved_disjoint1 _ _ RF ltac:(clear -ETOP Eslot B0 SI0 S16; unfold UNIT in *; lia)) as DR.
  set (S := conc st (blk_slot b)) in *. set (P := blk_addr b) in *.
  set (AV := stride - IB - UNIT * off).
  assert (EAV : S + stride - 4 - P = AV) by (subst AV; rewrite HS, HP, Epf; unfold UNIT, IB; lia).
  rewrite EAV.
  assert (ESS : slot_start' mr i = aadd bm (UNIT + stride * i)) by (unfold slot_start'; rewrite Hmem; reflexivity).
  rewrite ESS. unfold aadd. cbn [fst snd].
  replace (snd bm + (UNIT + stride * i) + (stride - IB) - snd pf) with AV by (subst AV; rewrite Epf, Eslot; lia).
  replace (snd pf - (snd bm + (UNIT + stride * i))) with (UNIT * off) by (rewrite Epf, Eslot; lia).
  (* [comment removed for export] *)
  assert (RB : forall rid r1, s_regions st !! rid = Some r1 -> 4096 <= r_base r1 /\ r_base r1 + round_up_pg (r_len r1) <= alloc_ceiling).
  { intros rid r1 H1. pose proof (rregion_facts st m1 rid r1 MR1 H1) as (X1 & _ & X2 & _). split; [exact X1| exact X2]. }
  assert (UA1 : unk_agree st m m1).
  { eapply unk_agree_munch; [apply unk_agree_refl| exact MU1| |].
    - intros rid r1 H1 K1. destruct (RB rid r1 H1). cbn. unfold alloc_ceiling in *. lia.
    - intros rid r1 H1. destruct (RB rid r1 H1). unfold alloc_ceiling in *. pose proof (round_up_pg_ge (r_len r1)). lia. }
  pose proof (bytes_at_bound _ _ _ _ OLD) as OB. rewrite LEN in OB.
  pose proof (MallocFacts_inv2.areach_facts_proof _ _ AR1) as MF1.
  destruct (rblock_inside st LB m1 b MF1 MR1 Hb) as (rb' & gb' & ib' & Hrb' & _ & _ & LOB & HIB & BZ & R4 & RC & RI1). fold P in LOB, HIB, RC, RI1.
  unfold alloc_ceiling in RC.
  assert (PR : 4096 <= P /\ P + blk_size b <= (Z.max 0x7fff80000000 (Z.min 0x800000000000 rc_sp) - 8388608)) by (clear -LOB HIB RC R4 BZ; lia).
  assert (OLD1 : bytes_at usegs m1 P old).
  { eapply bytes_at_transport; [exact OLD| exact MU1|]. cbn. rewrite LEN. lia. }
  assert (ERR1 : rw_cells usegs m1 (errno_addr tp) [C4 errv]).
  { eapply rw_cells_transport; [exact ERR| exact MU1| exact WM1|]. rewrite TP. unfold RATP. rewrite unsigned_lit by lia. cbn. lia. }
  assert (AUX1 : rauxv_ok m1 B).
  { eapply rauxv_ok_frame; [exact AUXB| exact MU1| exact WM1|]. constructor; [|constructor]. cbn. unfold RAUXV_CELL. lia. }
  assert (HP01 : rheap_pres LB (bv_unsigned sp) m m1).
  { intros a Ha CA. split; [| intros W; apply WM1; exact W]. apply MU1. rewrite wa_unsigned by lia. cbn. split; [| exact I].
    destruct CA as [CA|[[CA _]|(blk' & Hb' & Hab)]]; [lia| lia|].
    destruct (rblock_inside st LB m1 blk' MF1 MR1 Hb') as (r2 & _ & _ & _ & _ & _ & LO2 & HI2 & _ & _ & RC2 & _). unfold alloc_ceiling in RC2. lia. }
  assert (ST1' : stk usegs m1 lo (bv_unsigned sp - 64)) by (replace (bv_unsigned sp - 64) with (bv_unsigned sp + -64) by lia; exact ST1).
  assert (EOSE : S + stride - 4 - rsv - P = blk_size b) by (rewrite HS, HP, Ersv, Epf; unfold UNIT, IB; lia).
  (* [comment removed for export] *)
  assert (MOVE : forall (rax s0x s1x s3x s4x s5x s6x q0 q1 q2 w2 w3 w4 w5 w6 w7 q3 q4 : word),
    rimplTX m (realloc_move st pf n) s
      (rreallocT_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB b n lo B old m)
      (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp q0 q1 q2 s0x s1x a0 a1 w2 w3 w4 w5 w6 w7
               (Z_to_bv 64 (S + stride - 4 - rsv)) s3x s4x s5x s6x s7 s8 s9 s10 s11 q3 q4 t5 t6)
          F (Z_to_bv 64 0x19e64) fc None m1 (seg_rom usegs))).
  { intros. unfold st, t.
    eapply (rrealloc_move_walk gp tp s7 s8 s9 s10 s11 F fc lo B LO TP ra sp s0 s1 s2 s3 s4 s5 s6 _ _ _ _ _ _ _ _ _ _ a0 a1 _ _ _ _ _ _ _ _ t5 t6
              m m m1 s st0 LB b pf n old errv (N.succ (s_tick st0)) (S + stride - 4 - rsv));
      first [exact AR| exact MR1| exact BL| exact UA1| exact Hb| exact Hfst| exact Hconc| exact OLD1| exact LEN| exact AUX1| exact SB
            | exact ST1'| exact FR1| exact ERR1| exact MI1| exact HP01| exact A1| exact N| exact EOSE| idtac].
    - lia.
    - lia.
    - rewrite A0. apply unsigned_lit. lia. }
  (* [comment removed for export] *)
  assert (BIG : forall (t2v t3v t4v : word), m_sizeclass mr = 63 -> MMAP_THRESHOLD <= n ->
    rimplTX m (rbig_tree st pf g i n) s
      (rreallocT_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB b n lo B old m)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 (S + stride - 4)) (Z_to_bv 64 S) t2v
               s0 (wz (conc st g)) a0 a1 (wz (conc st bm)) (Z_to_bv 64 63) (wz (meta_word mr)) (Z_to_bv 64 63)
               (Z_to_bv 64 (S + stride)) (Z_to_bv 64 (S + stride - 4 - P)) (Z_to_bv 64 (S + stride - 4 - rsv))
               s3 s4 s5 s6 s7 s8 s9 s10 s11 t3v t4v t5 t6)
          F (Z_to_bv 64 0x19d7c) fc None m1 (seg_rom usegs))).
  { intros t2v t3v t4v SC63 NTH. unfold st, t, S, P, mr, stride.
    eapply (RBIG ra sp s0 s1 s2 s3 s4 s5 s6 a0 a1 t2v t3v t4v t5 t6 m m m1 s st0 LB b pf g bm i n old errv off rsv LO TP);
      first [exact AR| exact MR1| exact BL| exact UA1| exact Hb| exact Hfst| exact Hconc| exact SL| exact Hmem| exact Fbm| exact OFF0| exact RSV0
            | exact Eslot| exact Epf| exact Ersv| exact SC63| exact NTH| exact HDREQ| exact OLD1| exact LEN| exact AUX1| exact SB| exact ST1'| exact FR1| exact ERR1| exact MI1| exact HP01| exact A0| exact A1| exact N| idtac].
    unfold RREALLOC_STACK_MIN. lia. }
  (* [comment removed for export] *)
  unfold rre_frame in FR1. unfold mkR in MOVE, BIG.
  riprefixTX.
  (* [comment removed for export] *)
  step. step. step. if_cases Kn; zify_cond Kn; rewrite A1, ?unsigned_lit in Kn by lia.
  - (* [comment removed for export] *)
    replace (n <? MMAP_THRESHOLD) with false by (symmetry; apply Z.ltb_ge; unfold MMAP_THRESHOLD; lia). rewrite andb_false_r. cbn [andb].
    step. step. if_cases K2; zify_cond K2; rewrite A1, ?unsigned_lit in K2 by lia. { exfalso. cbn in K2. lia. }
    (* [comment removed for export] *)
    step. step. if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia.
    + (* [comment removed for export] *)
      replace (48 <=? m_sizeclass mr) with false by (symmetry; apply Z.leb_gt; lia). cbn [andb].
      apply evt_done. apply MOVE.
    + (* [comment removed for export] *)
      assert (SC63 : m_sizeclass mr = 63) by (destruct SCF as [[X _]|[X _]]; [lia| exact X]).
      rewrite SC63. replace (MMAP_THRESHOLD <=? n) with true by (symmetry; apply Z.leb_le; unfold MMAP_THRESHOLD; lia). cbn [andb Z.leb].
      step. step. if_cases K4; zify_cond K4. 2:{ exfalso. rewrite ?unsigned_lit in K4 by lia. lia. }
      apply evt_done. apply rimplTX_xguard. intros _. subst BT. rewrite <- EAV. apply BIG; [exact SC63| unfold MMAP_THRESHOLD; lia].
  - (* [comment removed for export] *)
    replace (n <? MMAP_THRESHOLD) with true by (symmetry; apply Z.ltb_lt; unfold MMAP_THRESHOLD; lia).
    replace (MMAP_THRESHOLD <=? n) with false by (symmetry; apply Z.leb_gt; unfold MMAP_THRESHOLD; lia). rewrite andb_false_r, andb_true_r.
    assert (AVR : 0 <= AV < 2^64).
    { subst AV. clear -S16 OFF0 RSV0 Ersv BZ ETOP Eslot B0 SI0 RBC RB0. unfold UNIT, IB, alloc_ceiling in *. lia. }
    (* [comment removed for export] *)
    step. if_cases Ka; zify_cond Ka; rewrite A1, ?unsigned_lit in Ka by lia.
    + (* [comment removed for export] *)
      replace (n <=? AV) with false by (symmetry; apply Z.leb_gt; lia). cbn [andb].
      step. step. if_cases K2; zify_cond K2; rewrite A1, ?unsigned_lit in K2 by lia. 2:{ exfalso. cbn in K2. lia. }
      apply evt_done. apply MOVE.
    + (* [comment removed for export] *)
      replace (n <=? AV) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
      pose proof (size_to_class_props n ltac:(unfold MMAP_THRESHOLD; lia)) as (STR & _ & _).
      eapply evt_cut. { eapply (rrealloc_stc_walk _ _ gp tp); [exact A1| unfold MMAP_THRESHOLD; lia| exact MI1]. }
      cbv beta. intros ms' (t1' & a4' & a5' & a7' & ->).
      (* [comment removed for export] *)
      step. rewrite (unsigned_lit (size_to_class n)), swrap32_small by lia.
      step. if_cases Kc; zify_cond Kc; rewrite ?signed_wz_small in Kc by lia.
      * (* [comment removed for export] *)
        replace (m_sizeclass mr <=? size_to_class n + 1) with true by (symmetry; apply Z.leb_le; lia).
        apply evt_done. apply rimplTX_ret.
        assert (SC48 : m_sizeclass mr < 48) by (destruct SCF as [[X _]|[X _]]; lia).
        assert (STB : stride < 2^21).
        { pose proof (size_class_range (m_sizeclass mr) ltac:(lia)) as SZR.
          assert (MLB : m_maplen mr <= 256) by (destruct SCF as [[_ MLB]|[X _]]; [exact MLB| lia]).
          unfold stride, get_stride. destruct ((m_last_idx mr =? 0) && negb (m_maplen mr =? 0)); unfold UNIT; clear -SZR MLB; lia. }
        (* [comment removed for export] *)
        destruct (areach_blk_hdr st LB b pf AR1 Hb Hfst Hconc g i SL) as (bm' & off' & rsv' & q' & Hm' & _ & _ & _ & Eslot' & _ & Epf' & _ & Ersv' & _ & _ & _ & _ &
                  _ & C3 & _ & _ & _ & _ & _ & UNK & _).
        change (get_meta_rec st g) with mr in Hm', Eslot', Ersv'. fold stride in Eslot', Ersv'. rewrite Hmem in Hm'. inversion Hm'; subst bm'.
        assert (off' = off) as -> by (clear -Epf Epf' Eslot Eslot'; unfold UNIT in *; lia).
        assert (rsv' = rsv) as -> by (clear -Ersv Ersv'; lia). clear Eslot' Epf' Ersv' Hm'.
        destruct (SH (fst bm) r Hr Kr) as (HW & HBY & _).
        assert (BK : bytes_at usegs m1 (P - 3) [b8 (i + 32 * Z.min rsv 5)]).
        { rewrite HP. replace (r_base r + snd pf - 3) with (r_base r + (snd pf - 3)) by lia. rewrite <- Hfst, <- Fbm in C3.
          refine (proj1 (HBY _ _ _ C3)). clear -Epf Eslot ETOP B0 SI0 OFF0 S16 RSV0 Ersv BZ; unfold UNIT, IB in *. lia. }
        assert (WR3 : wr_at usegs m1 (P - 3) (S + stride - 4 - P + 3)).
        { eapply wr_at_sub; [exact HW| rewrite HP; clear -Epf Eslot B0 SI0 OFF0; unfold UNIT in *; lia| rewrite HS, HP; clear -Epf Eslot ETOP B0 SI0 OFF0 S16 RSV0 Ersv BZ; unfold UNIT, IB in *; lia]. }
        rewrite A1.
        set (E := S + stride - 4) in *. replace (S + stride) with (E + 4) by lia.
        eapply evt_cut.
        { eapply (rrealloc_ss_walk _ _ gp tp); first [exact MI1| exact FR1| exact ST1| exact WR3| exact BK| idtac].
          - rewrite A0. apply unsigned_lit. clear -PR BZ. lia.
          - clear -SLO; lia.
          - unfold E. rewrite HS. clear -ETOP RBC CLO; unfold alloc_ceiling in *. lia.
          - clear -PR BZ; lia.
          - clear -N; lia.
          - unfold E. subst AV. rewrite HS, HP, Epf. clear -Ka Eslot; unfold UNIT, IB in *; lia.
          - unfold E. subst AV. rewrite HS, HP, Epf. clear -Ka STB Eslot OFF0 N; unfold UNIT, IB in *. lia.
          - unfold E. rewrite HS. clear -ETOP RBC; unfold alloc_ceiling in *. lia.
          - clear -Ii RSV0 LI. lia. }
        cbv beta. intros msf PS. unfold rss_post in PS.
        destruct PS as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & -> & MI2 & ST2).
        set (b3 := i + 32 * Z.min rsv 5) in *.
        set (m2 := rset_size_mem m1 P E n b3) in *.
        (* [comment removed for export] *)
        set (e := (fst bm, snd bm + (UNIT + stride * i) + (stride - IB))).
        set (st' := havoc pf n (set_size pf e n i st)).
        assert (NOGRP : forall b' gh, s_groups st !! b' = Some gh -> fst b' = fst bm ->
                  snd b' + 9 <= snd bm + 16 + stride * i - 4 \/ snd bm + 16 + stride * i + stride - 4 <= snd b').
        { intros b' gh Hb' Hf'. pose proof (areach_blk_slot_nogrp st LB b pf AR1 Hb Hfst Hconc g i SL b' gh Hb' ltac:(rewrite Hf', Fbm, Hfst; reflexivity)) as X.
          change (get_meta_rec st g) with mr in X. fold stride in X. rewrite Eslot in X. clear -X. unfold UNIT, IB in *. lia. }
        destruct (rset_size_rep st m1 g bm r i n off b3 MR1 TK Hr Kr B0 ltac:(clear -Ii LI; lia)
                    ltac:(change (get_meta_rec st g) with mr; fold stride; rewrite Eslot in ETOP; clear -ETOP; unfold UNIT in *; lia)
                    ltac:(change (get_meta_rec st g) with mr; fold stride; exact S16)
                    ltac:(change (get_meta_rec st g) with mr; fold stride; exact NOGRP)
                    OFF0 ltac:(clear -N; lia)
                    ltac:(change (get_meta_rec st g) with mr; fold stride; subst AV; clear -Ka; unfold IB, UNIT in *; lia)
                    ltac:(change (get_meta_rec st g) with mr; fold stride; clear -STB N OFF0; lia)
                    ltac:(subst b3; clear -Ii RSV0; lia)) as [MRS TKS].
        cbv zeta in MRS, TKS. change (get_meta_rec st g) with mr in MRS, TKS. fold stride in MRS, TKS.
        assert (Epfp : (fst bm, snd bm + 16 + stride * i + 16 * off) = pf).
        { rewrite (surjective_pairing pf). f_equal; [rewrite Fbm; reflexivity| rewrite Epf, Eslot; unfold UNIT; lia]. }
        rewrite Epfp in MRS, TKS.
        assert (Ee : (fst bm, snd bm + 16 + stride * i + stride - 4) = e) by (unfold e; f_equal; unfold UNIT, IB; lia).
        rewrite Ee in MRS, TKS.
        rewrite (set_size_b3 pf e n b3 i st) in MRS, TKS by (subst b3; rewrite hdr_b3_idx by (clear -Ii LI RSV0; lia); symmetry; change 31 with (Z.ones 5); rewrite Z.land_ones by lia; apply Z.mod_small; clear -Ii LI; lia).
        replace (conc st bm + 16 + stride * i + 16 * off) with P in MRS by (rewrite HBm, HP, Epf, Eslot; unfold UNIT; lia).
        replace (conc st bm + 16 + stride * i + stride - 4) with E in MRS by (unfold E; rewrite HBm, HS, Eslot; unfold UNIT; lia).
        fold m2 in MRS.
        destruct (rmrep_havoc _ m2 pf n MRS TKS) as [MR2 TK2]. fold st' in MR2, TK2.
        (* [comment removed for export] *)
        destruct (rset_size_mem_fp m1 P E n b3 ltac:(clear -PR; lia) ltac:(clear -N; lia)
                    ltac:(unfold E; subst AV; rewrite HS, HP, Epf; clear -Ka Eslot; unfold UNIT, IB in *; lia)
                    ltac:(unfold E; rewrite HS; clear -ETOP RBC; unfold alloc_ceiling in *; lia)
                    ltac:(unfold E; subst AV; rewrite HS, HP, Epf; clear -Ka Eslot STB N OFF0; unfold UNIT, IB in *; lia)) as (MU2 & WM2 & MID2).
        fold m2 in MU2, WM2, MID2.
        pose proof (go_stride _ _ _ GO) as [_ SM]. change (get_meta_rec st g) with mr in SM. fold stride in SM.
        assert (EIMG : E <= 0x10000 \/ 0x57000 <= P - 3).
        { unfold E. rewrite HS, HP. clear -DR ETOP Epf Eslot OFF0 B0 SI0 RB0. unfold UNIT in *. lia. }
        assert (CONC' : conc st' pf = P) by (unfold st'; rewrite conc_havoc, conc_set_size; unfold st; rewrite conc_set_tick; exact Hconc).
        apply evt_done. unfold rreallocT_post. cbn [fst snd]. do 15 eexists. exists m2, errv.
        split; [reflexivity|]. split; [exact MR2|]. split; [exact MI2|]. split; [exact ST2|].
        split. { eapply rw_cells_transport; [exact ERR1| exact MU2| exact WM2|]. rewrite TP. unfold RATP. rewrite unsigned_lit by lia. cbn. clear -EIMG PR. lia. }
        split. { eapply rauxv_ok_frame; [exact AUX1| exact MU2| exact WM2|]. constructor; [|constructor]. cbn. unfold RAUXV_CELL, E. rewrite HS. clear -ETOP RBC SB CLO SLO EIMG PR HS. unfold alloc_ceiling in *. lia. }
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split. { unfold brk_link_ps in *. unfold st'. rewrite ctx_havoc, ctx_set_size. change (ctx st) with (ctx st0).
                 destruct (c_brk (ctx st0)) as [| |brid boff]; [exact BL| exact BL|]. rewrite conc_havoc, conc_set_size. exact BL. }
        (* [comment removed for export] *)
        set (kk := Z.min n (blk_size b)).
        assert (KK : 0 <= kk <= n /\ kk <= blk_size b) by (subst kk; clear -N BZ; lia).
        destruct (rwr_at_bytes_exist m1 (P + kk) (n - kk)) as (bs & LBS & BS).
        { eapply wr_at_sub; [exact HW| rewrite HP; clear -Epf Eslot B0 SI0 OFF0 KK; unfold UNIT in *; lia|].
          rewrite HP. subst AV. rewrite Epf, Eslot. rewrite Eslot in ETOP. clear -Ka ETOP KK OFF0 B0 SI0. unfold UNIT, IB in *. lia. }
        { clear -KK N; lia. }
        { rewrite HP. rewrite Eslot in ETOP. subst AV. clear -DR ETOP Epf Eslot OFF0 B0 SI0 RB0 KK N Ka. unfold UNIT, IB in *. lia. }
        assert (UCH1 : rw_cells usegs m1 P [CB (Z.to_nat kk) (firstn (Z.to_nat kk) old); CB (Z.to_nat (n - kk)) bs]).
        { apply rw_cells_of_bytes.
          - cbn. rewrite length_firstn. repeat split; lia.
          - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split.
            + rewrite <- (firstn_skipn (Z.to_nat kk) old) in OLD1. apply (proj1 (bytes_at_app _ _ _ _ _)) in OLD1. destruct OLD1 as [X _]. exact X.
            + rewrite length_firstn. replace (Z.of_nat (Z.to_nat kk `min` length old)) with kk by (rewrite <- (Nat2Z.id (length old)), LEN in |- *; clear -KK; lia). exact BS.
          - cbn [cells_size csize]. rewrite Nat.add_0_r. replace (Z.of_nat (Z.to_nat kk + Z.to_nat (n - kk))) with n by (clear -KK N; lia).
            eapply wr_at_sub; [exact HW| rewrite HP; clear -Epf Eslot B0 SI0 OFF0; unfold UNIT in *; lia|].
            rewrite HP. subst AV. rewrite Epf, Eslot. rewrite Eslot in ETOP. clear -Ka ETOP OFF0 B0 SI0 N. unfold UNIT, IB in *. lia. }
        pose proof (MID2 _ _ UCH1 ltac:(lia) ltac:(cbn [cells_size csize]; clear -KK N; lia)) as UCH2.
        exists (blk_id b), bs. cbv zeta. rewrite CONC'. fold kk.
        split; [exact A0|].
        split. { unfold rblock_range, alloc_ceiling. split; [clear -PR; lia|]. split.
                 { rewrite HP, Epf, Eslot. apply mod16_of_region; [exact RBAL| apply mod16_slot; [exact B16| exact SM]]. }
                 split; [clear -N; lia|]. unfold E in *. rewrite HS in *. clear -Ka EIMG PR ETOP RBC Epf Eslot HP OFF0 AV B0 SI0 N. subst AV. unfold UNIT, IB, alloc_ceiling in *. lia. }
        split. { pose proof (areach_realloc_keep st0 LB b pf n st' AR Hb ltac:(clear -N; lia) Hfst Hconc) as X. rewrite CONC' in X. apply X. clear X.
                 split; [unfold size_overflows; apply Z.leb_gt; clear -N; lia|].
                 exists g, i, (blk_size b). split; [exact HDREQ|]. cbv zeta. left.
                 cbn [rk_of rk_st0 rk_e rk_avail rk_g rk_idx]. fold st. change (get_meta_rec st g) with mr. fold stride.
                 unfold slot_start'. rewrite Hmem. cbn [default id fst snd aadd]. unfold aadd. cbn [fst snd].
                 replace (snd bm + (UNIT + stride * i) + (stride - IB) - snd pf) with AV by (subst AV; rewrite Epf, Eslot; lia).
                 split; [| reflexivity].
                 rewrite (proj2 (Z.leb_le _ _) Ka), (proj2 (Z.leb_le _ _) Kc). replace (n <? MMAP_THRESHOLD) with true by (symmetry; apply Z.ltb_lt; unfold MMAP_THRESHOLD; clear -Kn; lia). reflexivity. }
        split.
        { eapply rheap_pres_trans; [eapply rheap_pres_weaken; [exact HP01| lia| intros bb' Hbb'; unfold lbrm in Hbb'; apply In_filter_iff in Hbb'; destruct Hbb' as [X _]; exact X]|].
          intros a Ha CA. split; [| intros W; apply WM2; exact W]. apply MU2. rewrite wa_unsigned by lia. cbn. split; [| exact Logic.I].
          destruct CA as [CA|[[CA _]|(blk' & Hb' & Hab)]].
          - unfold E. rewrite HS. clear -CA ETOP RBC CLO SLO. unfold alloc_ceiling in *. lia.
          - clear -CA EIMG PR. lia.
          - unfold lbrm in Hb'. apply In_filter_iff in Hb'. destruct Hb' as [Hin' Hne'].
            assert (NS' : blk_slot blk' <> blk_slot b) by (intros EE; rewrite EE, aptr_eqb_refl in Hne'; exact Hne').
            destruct (N.eq_dec (fst (blk_slot blk')) (fst (blk_slot b))) as [EF|NF].
            + pose proof (areach_blk_slot_clear st LB b pf AR1 Hb Hfst Hconc g i SL blk' Hin' NS' EF) as X.
              change (get_meta_rec st g) with mr in X. fold stride in X. fold S in X. unfold E. rewrite HP, Epf, Eslot. rewrite HS in X |- *.
              clear -X Hab Eslot OFF0 B0 SI0. unfold UNIT, IB in *. lia.
            + destruct (rblock_inside st LB m1 blk' MF1 MR1 Hin') as (r2 & _ & _ & Hr2 & Kr2 & _ & LO2 & HI2 & _).
              assert (NE2 : fst (blk_slot blk') <> fst bm) by (rewrite Fbm, Hfst; exact NF).
              pose proof (lr_lo_group r2 Kr2). pose proof (lr_lo_group r Kr).
              destruct (DISJ _ _ _ _ Hr2 Hr NE2); unfold E; rewrite ?HS, ?HP, ?Epf, ?Eslot in *; clear -H H0 H1 Hab LO2 HI2 ETOP Epf Eslot OFF0 B0 SI0 HP HS; unfold UNIT, IB in *; lia. }
        exact UCH2.
      * (* [comment removed for export] *)
        replace (m_sizeclass mr <=? size_to_class n + 1) with false by (symmetry; apply Z.leb_gt; lia).
        apply evt_done. apply MOVE.
Qed.
End REALLOC.
End RC__2.
