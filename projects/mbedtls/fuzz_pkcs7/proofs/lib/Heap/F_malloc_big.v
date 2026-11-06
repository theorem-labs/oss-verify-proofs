(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast MallocTree MallocFacts_A MallocKit_A F_mm_syscalls.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp AllocSlot_iface F_malloc_join F_malloc_core MallocHINV.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocKit_AB.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocKit_A2 F_malloc_bigw.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_F_malloc_big () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.Heap.Malloc.IB"; "OSSVerify.KrLib.Heap.Malloc.UNIT"; "OSSVerify.KrLib.Heap.Malloc.mstate"; "OSSVerify.KrLib.Heap.Malloc.upd_meta"; "OSSVerify.KrLib.Heap.Malloc.meta"; "OSSVerify.KrLib.Heap.Malloc.m_set_freed"; "OSSVerify.KrLib.Heap.Malloc.m_set_avail"; "OSSVerify.KrLib.Heap.Malloc.m_set_maplen"; "Stdlib.ZArith.BinInt.Z.div"; "OSSVerify.KrLib.Heap.Malloc.m_set_sizeclass"; "OSSVerify.KrLib.Heap.Malloc.m_set_freeable"; "OSSVerify.KrLib.Heap.Malloc.m_set_last_idx"; "OSSVerify.KrLib.Heap.Malloc.m_set_mem"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.N"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.Heap.Malloc.put_group"; "OSSVerify.KrLib.Heap.Malloc.aptr"; "OSSVerify.KrLib.Heap.Malloc.group_active_idx"; "OSSVerify.KrLib.Heap.Malloc.lh_hdr"; "OSSVerify.KrLib.Heap.Malloc.full_lay"; "OSSVerify.KrLib.Heap.Malloc.add_slots"; "OSSVerify.KrLib.Heap.Malloc.get_stride"; "OSSVerify.KrLib.Heap.Malloc.get_meta_rec"; "OSSVerify.KrLib.Heap.Malloc.upd_ctx"; "OSSVerify.KrLib.Heap.Malloc.mctx"; "OSSVerify.KrLib.Heap.Malloc.set_mmap_counter"; "OSSVerify.KrLib.Heap.Malloc.u32"; "OSSVerify.KrLib.Heap.Malloc.c_mmap_counter"; "OSSVerify.KrLib.Heap.Malloc_fp.unk_agree"; "OSSVerify.KrLib.Heap.Malloc.region"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "stdpp.gmap.gmap_lookup"; "OSSVerify.KrLib.Heap.Malloc.s_regions"; "OSSVerify.KrLib.Heap.Malloc.rkind"; "OSSVerify.KrLib.Heap.Malloc.r_kind"; "OSSVerify.KrLib.Heap.Malloc.RKGroup"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.and"; "OSSVerify.KrLib.Heap.Malloc.shadow"; "OSSVerify.KrLib.Heap.Malloc.get_shadow"; "OSSVerify.KrLib.Heap.Malloc_fp.grp_hdr_cov"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.Heap.Malloc.round_up_pg"; "OSSVerify.KrLib.Heap.Malloc.r_len"; "OSSVerify.KrLib.Heap.Malloc.cellval"; "OSSVerify.KrLib.Heap.Malloc.cell_read"; "OSSVerify.KrLib.Heap.Malloc.Unknown"; "Corelib.Init.Logic.not"; "stdpp.bitvector.definitions.bv"; "OSSVerify.KrLib.Lib.Mem.wa"; "OSSVerify.KrLib.Heap.Malloc.r_base"; "Corelib.Init.Datatypes.bool"; "OSSVerify.KrLib.Lib.Decode.mmap_addr_ok"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.true"; "OSSVerify.KrLib.Heap.Malloc.mmap_answer_ok"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.Heap.Malloc.ranges_free"; "OSSVerify.KrLib.Heap.Malloc.is_err"; "Corelib.Init.Datatypes.false"; "OSSVerify.KrLib.Heap.Malloc.brkstate"; "OSSVerify.KrLib.Heap.Malloc.c_brk"; "OSSVerify.KrLib.Heap.Malloc.ctx"; "OSSVerify.KrLib.Heap.Malloc.BrkLive"; "OSSVerify.KrLib.Heap.Malloc.conc"; "OSSVerify.KrLib.Heap.MallocTree.brk_link_ps"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Heap.MallocBlocks.block"; "OSSVerify.KrLib.Heap.MallocBlocks.AREACH_from"; "OSSVerify.KrLib.Heap.MallocRep.agent_reserved"; "OSSVerify.KrLib.Heap.Malloc.MMAP_THRESHOLD"; "OSSVerify.KrLib.Heap.Malloc.s_ceil"; "OSSVerify.KrLib.Heap.Malloc.set_tick"; "OSSVerify.KrLib.Heap.Malloc.live_ranges"; "OSSVerify.KrLib.Heap.Malloc.step_seq"; "Corelib.Init.Datatypes.fst"; "OSSVerify.KrLib.Heap.Malloc.new_region"].


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition big_final (st3 : mstate) (g : aptr) (rid : N) (n : Z) : mstate := ltac2:(CDefT.buildp (gd_tbl_F_malloc_big ()) "Zneeded,$0.(1.(1.O1.$2.)$3.)Zst4,$4.(5.O3.Lmr,$6.(7.=(8.=(9.(:.(1.R2.+???.)+1000.)(;.+3?.(<.+1.(=.=(>.(?.(10.$11.$0.)(12.$11.$0.O2.=))R1.)))))))O4.)Zst5,$4.(13.(12.$11.$0.O2.=)(?.$14.O3.)(15.R1.(12.$11.$0.O2.=))(16.$17.R1.(12.$11.$0.O2.=)))Zst6,$4.(18.O3.(12.$11.$0.O2.=)(19.(1:.R1.O3.))+1.R1.)(1;.Lc,$1<.(1=.(1>.(1.(1?.R1.)+1.))R1.)R1.)")
(* [comment removed for export] *).


Section FINAL.
Variables (st3 : mstate) (g : aptr) (rid : N) (xa n c : Z).
Hypothesis G0 : get_meta_rec st3 g = meta0.
Hypothesis GN : (s_groups st3) !! (rid, 0) = None.
Hypothesis HC : c_mmap_counter (ctx st3) = c.
Hypothesis NR : 0 <= n < 2^32.
Hypothesis RR : (s_regions st3) !! rid = Some (mkRegion RKGroup xa (n + IB + UNIT)).

Let stF := big_final st3 g rid n.
Let stM := big_st st3 g rid n (u32 (c + 1)).


End FINAL.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma malloc_core_big_eq st1 n : MMAP_THRESHOLD <= n < 2^32 ->
  malloc_core full_lay st1 n =
    SVis (EMmap 0 (n + IB + UNIT) PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
      if negb (mmap_answer_ok (s_ceil st1) (live_ranges st1) (n + IB + UNIT) r) then bad_answer (ret (st1, @None (aptr * Z))) else
      if is_err r then ret (st1, None) else
      let '(st2, rid) := new_region RKGroup r (n + IB + UNIT) st1 in
      alloc_meta (step_seq st2) (fun st3 go =>
        match go with
        | None => SVis (EMunmap r (n + IB + UNIT)) (fun ru => if munmap_answer_ok ru then ret (drop_region rid st3, @None (aptr * Z)) else bad_answer (ret (st1, None)))
        | Some g => ret (big_final st3 g rid n, Some (g, 0))
        end) (ret (st1, None))).
Proof.
  intros Hn. unfold malloc_core.
  replace (size_overflows n) with false by (symmetry; unfold size_overflows; apply Z.leb_gt; lia).
  replace (MMAP_THRESHOLD <=? n) with true by (symmetry; apply Z.leb_le; lia).
  reflexivity.
Qed.

Lemma unk_agree_transfer st st' o m m' : ltac2:(CDefT.buildp (gd_tbl_F_malloc_big ()) "P,(20.O5.O3.O2.)P,Prid,$11.Pr,$21.P,(22.(23.$21.)(24.$11.$21.(25.$11.$26.$27.$21.)(28.$11.$26.$27.$21.)R2.(29.O4.))(?.$21.R1.))P,(22.$2:.(2;.R2.)$2<.)(2=.(2>.(22.(23.$21.)(24.$11.$21.(25.$11.$26.$27.$21.)(28.$11.$26.$27.$21.)R4.(29.O5.))(?.$21.R3.))(2>.(22.$2?.(30.O4.R4.)(30.O5.R4.))(2>.Poff,$0.P,(31.O5.R5.R1.)(31.O4.R6.R2.)Poff,$0.Ph,$0.P,(2>.(32.=R2.)(33.R2.(34.(35.R5.))))P,(22.$36.(37.(30.O5.R7.)R3.)(38.R2.))P,(39.(31.O4.R8.R4.))(22.(23.(3:.&8.))A1.O1.(3;.(1.(3<.R8.)R5.))A1.O2.(3;.(1.(3<.R8.)R5.))))))Poff,$0.Ph,$0.P,(2>.(32.=R2.)(33.R2.(34.(35.R5.))))P,(22.$36.(37.(30.O4.R7.)R3.)(38.R2.))(31.O4.R8.R4.))(20.O4.O3.O1.)")
(* [comment removed for export] *).
Proof.
  intros UA H rid r off h Hr Hk Ho Hc NG.
  destruct (H rid r Hr Hk) as [(Hr0 & ES & GM & AG)|NEW].
  - rewrite ES in Hc. rewrite (AG off h Ho Hc NG). apply (UA rid r off h Hr0 Hk Ho Hc). intros X. apply NG, GM, X.
  - exfalso. apply NG. eapply NEW; eauto.
Qed.

Lemma grp_hdr_cov_same st st' rid off : s_groups st' = s_groups st -> grp_hdr_cov st rid off -> grp_hdr_cov st' rid off.
Proof. (intros EG dd_H; ddestruct dd_H as (b & gh & Hb & E & R)). dexists b, gh. rewrite EG. auto. Qed.

(* [comment removed for export] *)
Lemma munmap_answer_ok_range a : match a with RgErr e => 1 <= e <= 4095 | RgDone _ => True end -> munmap_answer_ok (range_val a) = true.
Proof.
  destruct a as [e|b]; cbn [range_val]; intros He.
  - unfold munmap_answer_ok, is_errno_form, neg_errno, TWO64.
    replace (2 ^ 64 - 4095 <=? 2 ^ 64 - e) with true by (symmetry; apply Z.leb_le; lia).
    replace (2 ^ 64 - e <? 2 ^ 64) with true by (symmetry; apply Z.ltb_lt; lia).
    destruct (2 ^ 64 - e =? 0); reflexivity.
  - reflexivity.
Qed.

Lemma mmap_answer_ok_err ceil live len e : 1 <= e <= 4095 -> mmap_answer_ok ceil live len (neg_errno e) = true /\ is_err (neg_errno e) = true.
Proof.
  intros He. unfold mmap_answer_ok, is_errno_form, is_err, neg_errno, TWO64. split.
  - replace (2 ^ 64 - 4095 <=? 2 ^ 64 - e) with true by (symmetry; apply Z.leb_le; lia).
    replace (2 ^ 64 - e <? 2 ^ 64) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - apply Z.ltb_lt. lia.
Qed.

(* [comment removed for export] *)
Lemma mmap_answer_ok_addr ceil live len xa : ltac2:(CDefT.buildp (gd_tbl_F_malloc_big ()) "P,(32.=O2.)P,(22.$3=.(3>.O2.(3?.(10.$0.$0.))O1.)$40.)P,(22.$3=.(41.O4.O3.O2.O1.)$40.)(2>.(33.=O1.)(2>.(22.$0.(42.O1.+1000.)=)(2>.(32.(1.O1.(34.O2.))O4.)(2>.(22.$3=.(43.O3.O1.(34.O2.))$40.)(22.$3=.(44.O1.)$45.)))))")
(* [comment removed for export] *).
Proof.
  intros L0 A B. pose proof (round_up_pg_ge len) as RG. unfold mmap_addr_ok in A. rewrite !Bool.andb_true_iff in A. ddestruct A as [[[A1 A2] A3] _].
  apply Z.eqb_eq in A1. apply Z.ltb_lt in A2. apply Z.leb_le in A3. rewrite mmap_len_round_up in A3.
  rewrite grant_top_max_val in A3. change page_size with 4096 in A1.
  unfold mmap_answer_ok in B. apply Bool.orb_prop in B.
  assert (NE : is_errno_form xa = false).
  { unfold is_errno_form, TWO64. replace (2 ^ 64 - 4095 <=? xa) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
  destruct B as [B|B]; [rewrite NE in B; discriminate|].
  rewrite !Bool.andb_true_iff in B. ddestruct B as [[[_ _] B3] B4]. apply Z.leb_le in B3.
  repeat split; auto. unfold is_err, TWO64. apply Z.ltb_ge. lia.
Qed.


Lemma brk_link_ps_ext st st' s : ltac2:(CDefT.buildp (gd_tbl_F_malloc_big ()) "P,(22.$46.(47.(48.O2.))(47.(48.O3.)))P,Prid,$11.Poff,$0.P,(22.$46.(47.(48.O3.))(49.R2.R1.))(22.$0.(4:.O2.(12.$11.$0.R3.R2.))(4:.O3.(12.$11.$0.R3.R2.)))P,(4;.O3.O1.)(4;.O2.O1.)")
(* [comment removed for export] *).
Proof.
  intros EB EC BL. unfold brk_link_ps in *. rewrite EB. destruct (c_brk (ctx st)) as [| |rid off] eqn:E; auto.
  rewrite (EC rid off eq_refl). exact BL.
Qed.

Lemma munch_of_pointwise (lo hi : Z) (m m' : mem) : ltac2:(CDefT.buildp (gd_tbl_F_malloc_big ()) "P,(32.=O4.)P,(32.O3.(4<.+2.+40.))P,Pa,$0.P,(2>.(32.=R1.)(33.R1.(4<.+2.+40.)))P,(2=.(33.R2.O4.)(32.O3.R2.))(22.(23.(3:.&8.))A1.O1.(3;.R3.)A1.O2.(3;.R3.))(4=.(4>.(10.$0.$0.)(12.$0.$0.O4.O3.)(3?.(10.$0.$0.)))O2.O1.)")
(* [comment removed for export] *).
Proof.
  intros H0 H1 AG x Hx. cbn in Hx. pose proof (bv_unsigned_in_range 64 x) as R. change (bv_modulus 64) with (2^64) in R.
  rewrite <- (wa_unsigned_id x). apply AG; lia.
Qed.


(* [comment removed for export] *)
Lemma cell_read_hh0 st rid off : (s_shadow st) !! rid = None -> 0 <= off ->
  cell_read (get_shadow (hdr_havoc (rid, 0) st) rid) off = if off <? 12 then Unknown 0 else Known 0.
Proof.
  intros SH Ho. unfold hdr_havoc, get_shadow, upd_shadow. cbn [s_shadow set_shadow fst snd].
  rewrite lookup_insert_eq. cbn [default from_option id]. unfold get_shadow. rewrite SH. cbn [default from_option id r_cells r_hav r_havp shadow0].
  unfold cell_read. cbn [r_cells r_hav r_havp]. rewrite !lookup_empty. change (0 / 16) with 0.
  destruct (Z.eq_dec (off / 16) 0) as [E|NE].
  - rewrite E, lookup_insert_eq. cbn [default from_option id]. unfold hav_add. cbn.
    replace (off mod 16) with off by (Z.div_mod_to_equations; lia). destruct (off <? 12); reflexivity.
  - rewrite lookup_insert_ne by congruence. rewrite lookup_empty. cbn.
    replace (off <? 12) with false by (symmetry; apply Z.ltb_ge; Z.div_mod_to_equations; lia). reflexivity.
Qed.

Lemma round_up_pg_4115 n : 0 <= n -> round_up_pg (n + IB + UNIT) = (n + 4115) / 4096 * 4096.
Proof. intros Hn. unfold IB, UNIT. rewrite round_up_pg_eq. Z.div_mod_to_equations. lia. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AMP_BIG (am_pre : mstate -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_F_malloc_big ()) "Pst,$4.PLB,(4?.$50.)Pt,$11.Pxa,$0.Pn,$0.P,(51.$52.R5.R4.)P,(2>.(32.$53.R2.)(33.R2.(4<.+2.+20.)))P,(22.$3=.(41.(54.(55.R5.R7.))(56.(55.R5.R7.))(1.(1.R3.$2.)$3.)R4.)$40.)P,(22.$3=.(44.R5.)$45.)A1.O1.(57.(58.$4.$11.(59.$2<.R6.(1.(1.R5.$2.)$3.)(55.R7.R9.))))")
(* [comment removed for export] *).

Section BIG.
Variable am_pre : mstate -> Prop.
Hypothesis AM : alloc_meta_stmt am_pre.
Hypothesis AMP : AMP_BIG am_pre.

End BIG.
