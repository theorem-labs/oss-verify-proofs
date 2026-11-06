(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep .
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_syscalls.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_MallocRep () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "pw"; "OSSVerify.KrLib.Heap.Malloc.m_prev"; "OSSVerify.KrLib.Heap.Malloc.m_next"; "OSSVerify.KrLib.Heap.Malloc.m_mem"; "OSSVerify.KrLib.Lib.Cells.C4"; "wz"; "OSSVerify.KrLib.Heap.Malloc.m_avail"; "OSSVerify.KrLib.Heap.Malloc.m_freed"; "meta_word"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Heap.Malloc.mctx"; "OSSVerify.KrLib.Heap.Malloc.ctx"; "OSSVerify.KrLib.Heap.Malloc.c_secret"; "OSSVerify.KrLib.Heap.Malloc.c_init_done"; "OSSVerify.KrLib.Heap.Malloc.c_mmap_counter"; "OSSVerify.KrLib.Heap.Malloc.c_free_meta_head"; "OSSVerify.KrLib.Heap.Malloc.c_avail_meta"; "OSSVerify.KrLib.Heap.Malloc.c_avail_meta_count"; "OSSVerify.KrLib.Heap.Malloc.c_avail_meta_area_count"; "OSSVerify.KrLib.Heap.Malloc.c_meta_alloc_shift"; "OSSVerify.KrLib.Heap.Malloc.c_meta_area_head"; "OSSVerify.KrLib.Heap.Malloc.c_meta_area_tail"; "OSSVerify.KrLib.Heap.Malloc.c_avail_meta_areas"; "Corelib.Init.Logic.and"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Heap.F_syscalls.asegs"; "CTX"; "ctx_head_cells"; "OSSVerify.KrLib.Lib.Arr.u64arr"; "Stdlib.ZArith.BinInt.Z.add"; "actives"; "usages"; "OSSVerify.KrLib.Lib.Arr.u8arr"; "unmap_seqs"; "bouncess"; "ctx_tail_cells"; "MLOCK"; "NEED_LOCKS"; "OSSVerify.KrLib.Lib.Cells.C1"; "b8"; "PAGE_SIZE_A"; "OSSVerify.KrLib.Heap.Malloc.conc"; "OSSVerify.KrLib.Heap.Malloc.a_check"; "OSSVerify.KrLib.Heap.Malloc.a_next"; "OSSVerify.KrLib.Heap.Malloc.a_nslots"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.Heap.Malloc.NSLOTS"; "OSSVerify.KrLib.Heap.Malloc.AREA_HDR"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Heap.Malloc.META_SIZE"; "meta_cells"; "OSSVerify.KrLib.Heap.Malloc.get_meta_rec"; "OSSVerify.KrLib.Heap.Malloc.aadd"; "OSSVerify.KrLib.Lib.Cells.CB"; "zeros"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "OSSVerify.KrLib.Heap.Malloc.g_meta"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.land"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.Heap.Malloc.g_active_idx"; "OSSVerify.KrLib.Lib.Mem.wr_at"; "OSSVerify.KrLib.Heap.Malloc.r_base"; "OSSVerify.KrLib.Heap.Malloc.round_up_pg"; "OSSVerify.KrLib.Heap.Malloc.r_len"; "OSSVerify.KrLib.Heap.Malloc.cellval"; "OSSVerify.KrLib.Heap.Malloc.cell_read"; "OSSVerify.KrLib.Heap.Malloc.get_shadow"; "OSSVerify.KrLib.Heap.Malloc.Known"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "OSSVerify.KrLib.Heap.Malloc.s_reserved"; "agent_reserved"; "Corelib.Numbers.BinNums.N"; "OSSVerify.KrLib.Heap.Malloc.region"; "Corelib.Init.Datatypes.option"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "stdpp.gmap.gmap_lookup"; "OSSVerify.KrLib.Heap.Malloc.s_regions"; "Corelib.Init.Datatypes.Some"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.Heap.Malloc.s_ceil"; "Corelib.Init.Datatypes.bool"; "OSSVerify.KrLib.Heap.Malloc.ranges_free"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.or"; "lr_lo"; "OSSVerify.KrLib.Heap.Malloc.area"; "OSSVerify.KrLib.Heap.Malloc.aptr"; "stdpp.decidable.prod_eq_dec"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.prod_countable"; "stdpp.countable.Z_countable"; "OSSVerify.KrLib.Heap.Malloc.s_areas"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "OSSVerify.KrLib.Heap.Malloc.rkind"; "OSSVerify.KrLib.Heap.Malloc.r_kind"; "OSSVerify.KrLib.Heap.Malloc.RKGroup"; "OSSVerify.KrLib.Heap.Malloc.ghdr"; "OSSVerify.KrLib.Heap.Malloc.s_groups"; "OSSVerify.KrLib.Heap.Malloc.mstate"; "mrep"; "meta_slot"; "OSSVerify.KrLib.Heap.Malloc.shadow"; "OSSVerify.KrLib.Heap.Malloc.s_shadow"; "OSSVerify.KrLib.Heap.Malloc.r_hav"; "Stdlib.Lists.List.In"; "Stdlib.NArith.BinNat.N.le"; "OSSVerify.KrLib.Heap.Malloc.s_tick"; "OSSVerify.KrLib.Heap.Malloc.r_havp"; "regions_wf"; "mrep_ctx"; "OSSVerify.KrLib.Heap.Malloc.meta"; "area_rep"; "group_rep"; "shadow_rep"; "OSSVerify.KrLib.Heap.Malloc.wr8"; "stdpp.base.insert"; "stdpp.fin_maps.map_insert"; "stdpp.gmap.gmap_partial_alter"; "OSSVerify.KrLib.Heap.Malloc.mkShadow"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.Heap.Malloc.r_cells"; "ticks_ok"; "OSSVerify.KrLib.Heap.Malloc.optr"; "OSSVerify.KrLib.Heap.Malloc.set_active"; "OSSVerify.KrLib.Lib.Arr.upd"; "Stdlib.ZArith.BinInt.Z.to_nat"; "OSSVerify.KrLib.Heap.Malloc.stale"; "OSSVerify.KrLib.Heap.Malloc.hav_add"; "Corelib.Init.Datatypes.false"; "sh_ticks"; "shadow_le"; "stdpp.option.from_option"; "Corelib.Init.Datatypes.id"; "OSSVerify.KrLib.Heap.Malloc.havoc_units"; "OSSVerify.KrLib.Heap.Malloc.havoc_pages"].


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition CTX : Z := 0x1a188.
Definition MLOCK : Z := 0x1a0d0.
Definition LIBC : Z := 0x1a120.
Definition NEED_LOCKS : Z := 0x1a123.     (* [comment removed for export] *)
Definition PAGE_SIZE_A : Z := 0x1a150.    (* [comment removed for export] *)
Definition SIZE_CLASSES : Z := 0x18170.


        (* [comment removed for export] *)
Definition alloc_meta_entry : Z := 0x15fd4.
Definition alloc_slot_entry : Z := 0x162e0.


(* [comment removed for export] *)
Definition agent_reserved : list (Z * Z) := [(0x10000, 0x9000); (0x19000, 0x2000)].

Definition wz (z : Z) : word := Z_to_bv 64 z.
Definition b8 (z : Z) : byte := Z_to_bv 8 z.
(* [comment removed for export] *)
Definition pw (st : mstate) (p : optr) : word := wz (oconc st p).

(* [comment removed for export] *)
Definition meta_word (mr : meta) : Z :=
  m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + 4096 * m_maplen mr.

Definition meta_cells (st : mstate) (mr : meta) : list cell := ltac2:(CDefT.buildp (gd_tbl_MallocRep ()) "(0.$1.(2.(3.O2.(4.O1.)))(0.$1.(2.(3.O2.(5.O1.)))(0.$1.(2.(3.O2.(6.O1.)))(0.$1.(7.(8.(9.O1.)))(0.$1.(7.(8.(:.O1.)))(0.$1.(2.(8.(;.O1.)))(<.$1.)))))))")
(* [comment removed for export] *).

Definition brk_word (st : mstate) : Z :=
  match c_brk (ctx st) with
  | BrkUntried => 0
  | BrkDead => 2^64 - 1
  | BrkLive rid off => conc st (rid, off)
  end.

Definition ctx_head_cells (st : mstate) : list cell := ltac2:(CDefT.buildp (gd_tbl_MallocRep ()) "Zc,$=.(>.O1.)(0.$1.(2.(8.(?.R1.)))(0.$1.(7.(8.(10.R1.)))(0.$1.(7.(8.(11.R1.)))(0.$1.(2.(3.O1.(12.R1.)))(0.$1.(2.(3.O1.(13.R1.)))(0.$1.(2.(8.(14.R1.)))(0.$1.(2.(8.(15.R1.)))(0.$1.(2.(8.(16.R1.)))(0.$1.(2.(3.O1.(17.R1.)))(0.$1.(2.(3.O1.(18.R1.)))(0.$1.(2.(3.O1.(19.R1.)))(<.$1.))))))))))))")
(* [comment removed for export] *).

Definition actives (st : mstate) : list word := map (fun i => pw st (active st (Z.of_nat i))) (seq 0 48).
Definition usages (st : mstate) : list word := map (fun i => wz (usage st (Z.of_nat i))) (seq 0 48).
Definition unmap_seqs (st : mstate) : list byte := map (fun i => b8 (unmap_seq st (Z.of_nat i))) (seq 0 32).
Definition bouncess (st : mstate) : list byte := map (fun i => b8 (bounces st (Z.of_nat i))) (seq 0 32).
Definition zeros (n : nat) : list byte := repeat (b8 0) n.
Definition ctx_tail_cells (st : mstate) : list cell :=
  [C1 (b8 (c_seq (ctx st))); CB 7 (zeros 7); C8 (wz (brk_word st))].

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition lr_lo (r : region) : Z :=
  match r_kind r with RKBrk => r_base r + 4096 | _ => r_base r end.

Lemma lr_lo_ge r : r_base r <= lr_lo r.
Proof. unfold lr_lo. destruct (r_kind r); lia. Qed.
Lemma lr_lo_group r : r_kind r = RKGroup -> lr_lo r = r_base r.
Proof. unfold lr_lo. intros ->. reflexivity. Qed.
Lemma lr_lo_nbrk r : r_kind r <> RKBrk -> lr_lo r = r_base r.
Proof. unfold lr_lo. destruct (r_kind r); congruence. Qed.

Section MREP.
Variable st : mstate.
Variable m : word -> option byte.

Definition mrep_ctx : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocRep ()) "(1:.(1;.$1<.Vm,$1=.(1>.Vst,))(1:.(1?.$1<.Vm,(20.$1=.+50.)(21.Vst,))(1:.(1?.$1<.Vm,(20.$1=.+1=0.)(22.Vst,))(1:.(23.$1<.Vm,(20.$1=.+350.)(24.Vst,))(1:.(23.$1<.Vm,(20.$1=.+370.)(25.Vst,))(1;.$1<.Vm,(20.$1=.+390.)(26.Vst,)))))))")
(* [comment removed for export] *).

Definition mrep_globals : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocRep ()) "(1:.(1;.$1<.Vm,$27.(0.$1.(7.(8.=))(<.$1.)))(1:.(1;.$1<.Vm,$28.(0.$1.(29.(2:.=))(<.$1.)))(1;.$1<.Vm,$2;.(0.$1.(2.(8.+1000.))(<.$1.)))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition area_rep (a : aptr) (ar : area) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocRep ()) "(1:.(1;.$1<.Vm,(2<.Vst,O2.)(0.$1.(2.(8.(2=.O1.)))(0.$1.(2.(3.Vst,(2>.O1.)))(0.$1.(7.(8.(2?.O1.)))(0.$1.(7.(8.=))(<.$1.))))))(1:.Pk,$30.P,(1:.(31.=R1.)(32.R1.$33.))(1;.$1<.Vm,(20.(20.(2<.Vst,O2.)$34.)(35.$36.R2.))(37.Vst,(38.Vst,(39.O2.(20.$34.(35.$36.R2.))))))(1;.$1<.Vm,(20.(2<.Vst,O2.)+?>0.)(0.$1.(3:.#20.(3;.#20.))(<.$1.)))))")
(* [comment removed for export] *).
Definition mrep_areas : Prop :=
  forall a ar, (s_areas st) !! a = Some ar -> area_rep a ar.

(* [comment removed for export] *)
Definition group_rep (b : aptr) (gh : ghdr) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocRep ()) "(3<.(3=.&8.)Lw8,(3=.&8.)(1:.(1;.$1<.Vm,(2<.Vst,O2.)(0.$1.(2.(3.Vst,(3>.O1.)))(0.$1.(29.R1.)(<.$1.))))(3?.$30.(40.(41.&8.R1.)+1?.)(42.O1.))))")
(* [comment removed for export] *).
Definition mrep_groups : Prop :=
  forall b gh, (s_groups st) !! b = Some gh -> group_rep b gh.

(* [comment removed for export] *)
Definition shadow_rep (rid : N) (r : region) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocRep ()) "(1:.(43.$1<.Vm,(44.O1.)(45.(46.O1.)))Po,$30.Pv,$30.P,(1:.(31.=R2.)(32.R2.(45.(46.O1.))))P,(3?.$47.(48.(49.Vst,O2.)R3.)(4:.R2.))(1:.(4;.$1<.Vm,(20.(44.O1.)R4.)(0.(3=.&8.)(2:.R3.)(<.(3=.&8.))))(1:.(31.=R3.)(32.R3.+100.))))")
(* [comment removed for export] *).
Definition mrep_shadow : Prop :=
  forall rid r, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> shadow_rep rid r.

(* [comment removed for export] *)
Definition regions_wf : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocRep ()) "(1:.(3?.(4<.(4=.$30.$30.))(4>.Vst,)$4?.)(1:.Prid,$50.Pr,$51.P,(3?.(52.$51.)(53.$50.$51.(54.$50.$55.$56.$51.)(57.$50.$55.$56.$51.)R2.(58.Vst,))(59.$51.R1.))(1:.(32.=(44.R2.))(1:.(3?.$30.(5:.(44.R2.)+1000.)=)(1:.(31.=(46.R2.))(1:.(31.(20.(44.R2.)(45.(46.R2.)))(5;.Vst,))(3?.$5<.(5=.$4?.(44.R2.)(45.(46.R2.)))$5>.)))))(1:.Prid1,$50.Pr1,$51.Prid2,$50.Pr2,$51.P,(3?.(52.$51.)(53.$50.$51.(54.$50.$55.$56.$51.)(57.$50.$55.$56.$51.)R4.(58.Vst,))(59.$51.R3.))P,(3?.(52.$51.)(53.$50.$51.(54.$50.$55.$56.$51.)(57.$50.$55.$56.$51.)R3.(58.Vst,))(59.$51.R2.))P,(5?.(3?.$50.R6.R4.))(60.(31.(20.(44.R6.)(45.(46.R6.)))(61.R4.))(31.(20.(44.R4.)(45.(46.R4.)))(61.R6.)))(1:.Pa,(4=.$50.$30.)Par,$62.P,(3?.(52.$62.)(53.(4=.$50.$30.)$62.(54.$63.(64.$50.$55.$30.$65.)(66.$50.$55.$56.$30.$65.$67.)$62.)(57.$63.(64.$50.$55.$30.$65.)(66.$50.$55.$56.$30.$65.$67.)$62.)R2.(68.Vst,))(59.$62.R1.))(3<.$51.Lr,$51.(1:.(3?.(52.$51.)(53.$50.$51.(54.$50.$55.$56.$51.)(57.$50.$55.$56.$51.)(69.$50.$30.R4.)(58.Vst,))(59.$51.R1.))(1:.(31.=(6:.$50.$30.R4.))(1:.(31.(20.(6:.$50.$30.R4.)+1000.)(45.(46.R1.)))(1:.(3?.$30.(5:.(6:.$50.$30.R4.)+1000.)=)(1:.(5?.(3?.$6;.(6<.R1.)$6=.))(31.(61.R1.)(20.(44.R1.)(6:.$50.$30.R4.)))))))))Pb,(4=.$50.$30.)Pgh,$6>.P,(3?.(52.$6>.)(53.(4=.$50.$30.)$6>.(54.$63.(64.$50.$55.$30.$65.)(66.$50.$55.$56.$30.$65.$67.)$6>.)(57.$63.(64.$50.$55.$30.$65.)(66.$50.$55.$56.$30.$65.$67.)$6>.)R2.(6?.Vst,))(59.$6>.R1.))(3<.$51.Lr,$51.(1:.(3?.(52.$51.)(53.$50.$51.(54.$50.$55.$56.$51.)(57.$50.$55.$56.$51.)(69.$50.$30.R4.)(58.Vst,))(59.$51.R1.))(1:.(3?.$6;.(6<.R1.)$6=.)(1:.(31.=(6:.$50.$30.R4.))(1:.(31.(20.(6:.$50.$30.R4.)+10.)(45.(46.R1.)))(3?.$30.(5:.(6:.$50.$30.R4.)+10.)=))))))))))")
(* [comment removed for export] *).

Definition mrep : Prop :=
  regions_wf /\ mrep_ctx /\ mrep_globals /\ mrep_areas /\ mrep_groups /\ mrep_shadow.

End MREP.


(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma conc_aadd : forall st p d,
  is_Some ((s_regions st) !! (fst p)) -> conc st (aadd p d) = conc st p + d.
Proof.
  intros st [rid off] d [r Hr]. unfold conc, aadd, get_region. cbn. rewrite Hr. lia.
Qed.

Lemma conc_region : forall st rid off r,
  (s_regions st) !! rid = Some r -> conc st (rid, off) = r_base r + off.
Proof. intros. unfold conc, get_region. cbn. rewrite H. reflexivity. Qed.

Lemma round_up_pg_ge : forall x, x <= round_up_pg x.
Proof. intros. unfold round_up_pg, PGSZ. assert (0 <= Z.land (-x) (4096 - 1)) by (apply Z.land_nonneg; right; lia). lia. Qed.


(* [comment removed for export] *)
Lemma wz_unsigned x : 0 <= x < 2^64 -> bv_unsigned (wz x) = x.
Proof. intros. unfold wz. apply unsigned_lit. lia. Qed.
Lemma b8_unsigned x : 0 <= x < 256 -> bv_unsigned (b8 x) = x.
Proof. intros. unfold b8. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn. apply Z.mod_small. lia. Qed.
Lemma zxb_b8 x : 0 <= x < 256 -> zxb (b8 x) = wz x.
Proof. intros. unfold zxb, wz. rewrite b8_unsigned by lia. reflexivity. Qed.
Lemma zx16_wz x : 0 <= x < 65536 -> zx16 (wz x) = wz x.
Proof. intros. unfold zx16, wz. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
Lemma sx32_wz x : 0 <= x < 2^31 -> sx32 (wz x) = wz x.
Proof. intros. unfold sx32, wz. rewrite unsigned_lit by lia. rewrite swrap32_small by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma land_ldiff_distr x a b : Z.land x (Z.ldiff a b) = Z.ldiff (Z.land x a) b.
Proof. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec. destruct (Z.testbit x n), (Z.testbit a n), (Z.testbit b n); reflexivity. Qed.

Lemma land_pgmask x : 0 <= x < 2^64 -> Z.land x 18446744073709547520 = x - x mod 4096.
Proof.
  intros Hx.
  assert (E : 18446744073709547520 = Z.ldiff (Z.ones 64) (Z.ones 12)) by reflexivity. rewrite E.
  rewrite land_ldiff_distr. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^12) with 4096. pose proof (Z.div_mod x 4096). lia.
Qed.

(* [comment removed for export] *)
Lemma mod_mod_pow2 z a b : 0 <= a <= b -> (z mod 2^b) mod 2^a = z mod 2^a.
Proof. intros. apply Z.mod_mod_divide. exists (2^(b-a)). rewrite <- Z.pow_add_r by lia. f_equal. lia. Qed.

Lemma swrap32_mod32 z : (bv_swrap 32 z) mod 2^32 = z mod 2^32.
Proof.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2^32). change (2^32 `div` 2) with (2^31).
  rewrite Zminus_mod, Z.mod_mod by lia. rewrite <- Zminus_mod.
  replace (z + 2^31 - 2^31) with z by lia. reflexivity.
Qed.


Lemma signed_wz_small x : 0 <= x < 2^63 -> bv_signed (Z_to_bv 64 x) = x.
Proof.
  intros. rewrite Z_to_bv_signed. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64 / 2)%Z with (2^63)%Z. lia.
Qed.

Ltac nrm := rewrite ?zxb_b8, ?zx16_wz, ?b8_unsigned, ?wz_unsigned by lia.
Ltac st1 := step; try nrm.
Ltac showpc := match goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "PC" pc end.


(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma size_class_range sc : 0 <= sc < 48 -> 1 <= size_class sc <= 8191.
Proof.
  intros H. unfold size_class.
  assert (F : Forall (fun x => 1 <= x <= 8191) size_classes).
  { unfold size_classes. repeat (constructor; [lia|]). constructor. }
  apply (Forall_nth (fun x => 1 <= x <= 8191) size_classes); [exact F|]. cbn. lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma conc_region' : forall st (q : aptr) r,
  (s_regions st) !! (fst q) = Some r -> conc st q = r_base r + snd q.
Proof. intros st [rid off] r H. apply conc_region. exact H. Qed.

(* [comment removed for export] *)
Definition meta_slot (st : mstate) (g : aptr) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocRep ()) "(3<.$63.La,$63.(3<.$62.Lar,$62.(3<.$30.Lk,$30.(1:.(3?.(52.$62.)(53.$63.$62.(54.$63.(64.$50.$55.$30.$65.)(66.$50.$55.$56.$30.$65.$67.)$62.)(57.$63.(64.$50.$55.$30.$65.)(66.$50.$55.$56.$30.$65.$67.)$62.)R3.(68.O2.))(59.$62.R2.))(1:.(1:.(31.=R1.)(32.R1.$33.))(3?.$63.O1.(39.R3.(20.$34.(35.$36.R1.)))))))))")
(* [comment removed for export] *).

Lemma mrep_meta_chunk : ltac2:(CDefT.buildp (gd_tbl_MallocRep ()) "Pst,$70.Pm,P,(3=.&40.)(52.(3=.&8.))Pg,$63.P,(71.R3.R2.)P,(72.R4.R2.)(1;.$1<.R4.(2<.R5.R3.)(37.R5.(38.R5.R3.)))")
(* [comment removed for export] *).
Proof.
  (intros st m g MR dd_H; ddestruct dd_H as (a & ar & k & Ha & Hk & ->)).
  dpose MR as (WF & _ & _ & AR & _ & _).
  ddestruct (AR a ar Ha) as (_ & SL & _).
  ddestruct WF as (_ & _ & _ & WA & _). ddestruct (WA a ar Ha) as (r & Hr & _).
  rewrite conc_aadd by (rewrite Hr; eauto).
  replace (conc st a + (AREA_HDR + META_SIZE * k)) with (conc st a + AREA_HDR + META_SIZE * k) by lia. apply SL. exact Hk.
Qed.


Lemma le2_lohi : forall lo hi, 0 <= lo < 256 -> 0 <= hi < 256 -> le2 (wz (lo + 256 * hi)) = [b8 lo; b8 hi].
Proof.
  intros lo hi Hl Hh. unfold le2, wz, b8. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
  f_equal; [apply Z_to_bv8_mod; rewrite <- Zplus_mod_idemp_r; replace (256 * hi) with (hi * 2^8) by lia; rewrite Z_mod_mult; rewrite Z.add_0_r; reflexivity|].
  f_equal. apply Z_to_bv8_mod. rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
  replace (lo + 256 * hi) with (lo + hi * 256) by lia. rewrite Z.div_add, Z.div_small by lia. reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ticks_ok (st : mstate) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocRep ()) "(1:.Prid,$50.Psh,$73.Pu,$30.Phl,(4<.(4=.$30.$50.))Pch,(4=.$30.$50.)P,(3?.(52.$73.)(53.$50.$73.(54.$50.$55.$56.$73.)(57.$50.$55.$56.$73.)R5.(74.O1.))(59.$73.R4.))P,(3?.(52.(4<.(4=.$30.$50.)))(53.$30.(4<.(4=.$30.$50.))(54.$30.$65.$67.(4<.(4=.$30.$50.)))(57.$30.$65.$67.(4<.(4=.$30.$50.)))R4.(75.R5.))(59.(4<.(4=.$30.$50.))R3.))P,(76.(4=.$30.$50.)R3.R4.)(77.(6:.$30.$50.R4.)(78.O1.))Prid,$50.Psh,$73.Ppg,$30.Pt,$50.P,(3?.(52.$73.)(53.$50.$73.(54.$50.$55.$56.$73.)(57.$50.$55.$56.$73.)R4.(74.O1.))(59.$73.R3.))P,(3?.(52.$50.)(53.$30.$50.(54.$30.$65.$67.$50.)(57.$30.$65.$67.$50.)R3.(79.R4.))(59.$50.R2.))(77.R3.(78.O1.)))")
(* [comment removed for export] *).


(* [comment removed for export] *)
Lemma reserved_disjoint : ltac2:(CDefT.buildp (gd_tbl_MallocRep ()) "Pb,$30.Pn,$30.P,(3?.$5<.(5=.$4?.R2.R1.)$5>.)(1:.(60.(31.(20.R3.R2.)+10000.)(31.+19000.R3.))(60.(31.(20.R3.R2.)+19000.)(31.+1;000.R3.)))")
(* [comment removed for export] *).
Proof.
  intros b n H. unfold ranges_free, agent_reserved in H. cbn [forallb fst snd] in H.
  unfold iv_disjoint in H. rewrite !Bool.andb_true_iff, !Bool.orb_true_iff, !Z.leb_le in H. lia.
Qed.

(* [comment removed for export] *)
Definition wr_in (st : mstate) (rid : N) (a len : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocRep ()) "(3<.$51.Lr,$51.(1:.(3?.(52.$51.)(53.$50.$51.(54.$50.$55.$56.$51.)(57.$50.$55.$56.$51.)O3.(58.O4.))(59.$51.R1.))(1:.(31.(61.R1.)O2.)(1:.(31.(20.O2.O1.)(20.(44.R1.)(45.(46.R1.))))(31.=O1.)))))")
(* [comment removed for export] *).


(* [comment removed for export] *)
Lemma area_lr_lo : ltac2:(CDefT.buildp (gd_tbl_MallocRep ()) "Pst,$70.Pa,(4=.$50.$30.)Par,$62.Pr,$51.P,(7:.R4.)P,(3?.(52.$62.)(53.(4=.$50.$30.)$62.(54.$63.(64.$50.$55.$30.$65.)(66.$50.$55.$56.$30.$65.$67.)$62.)(57.$63.(64.$50.$55.$30.$65.)(66.$50.$55.$56.$30.$65.$67.)$62.)R4.(68.R5.))(59.$62.R3.))P,(3?.(52.$51.)(53.$50.$51.(54.$50.$55.$56.$51.)(57.$50.$55.$56.$51.)(69.$50.$30.R5.)(58.R6.))(59.$51.R3.))(31.(61.R4.)(20.(44.R4.)(6:.$50.$30.R6.)))")
(* [comment removed for export] *).
Proof.
  (intros st a ar r dd_H; ddestruct dd_H as (_ & _ & _ & WA & _); intros Ha Hr). ddestruct (WA a ar Ha) as (r0 & Hr0 & _ & _ & _ & _ & LO).
  rewrite Hr in Hr0. inversion Hr0; subst. exact LO.
Qed.


(* [comment removed for export] *)
Lemma mrep_ctx_ext : ltac2:(CDefT.buildp (gd_tbl_MallocRep ()) "Pst,$70.Pst',$70.Pm,P,(3=.&40.)(52.(3=.&8.))P,(3?.$=.(>.R2.)(>.R3.))P,Pp,$63.(3?.$30.(2<.R4.R1.)(2<.R5.R1.))P,(7;.R5.R3.)(7;.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros st st' m Hc Hconc H.
  assert (Hpw : forall p, pw st' p = pw st p). { intros [p|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity. }
  assert (E1 : ctx_head_cells st' = ctx_head_cells st) by (unfold ctx_head_cells; rewrite Hc, !Hpw; reflexivity).
  assert (E2 : actives st' = actives st). { unfold actives. apply map_ext. intros. unfold active. rewrite Hc. apply Hpw. }
  assert (E3 : usages st' = usages st). { unfold usages. apply map_ext. intros. unfold usage. rewrite Hc. reflexivity. }
  assert (E4 : unmap_seqs st' = unmap_seqs st). { unfold unmap_seqs. apply map_ext. intros. unfold unmap_seq. rewrite Hc. reflexivity. }
  assert (E5 : bouncess st' = bouncess st). { unfold bouncess. apply map_ext. intros. unfold bounces. rewrite Hc. reflexivity. }
  assert (E6 : ctx_tail_cells st' = ctx_tail_cells st). { unfold ctx_tail_cells, brk_word. rewrite Hc. destruct (c_brk (ctx st)); rewrite ?Hconc; reflexivity. }
  unfold mrep_ctx in *. rewrite E1, E2, E3, E4, E5, E6. exact H.
Qed.

Lemma area_rep_ext : ltac2:(CDefT.buildp (gd_tbl_MallocRep ()) "Pst,$70.Pst',$70.Pm,P,(3=.&40.)(52.(3=.&8.))Pa,$63.Par,$62.P,Pp,$63.(3?.$30.(2<.R5.R1.)(2<.R6.R1.))P,Pk,$30.P,(1:.(31.=R1.)(32.R1.$33.))(3?.$7<.(38.R7.(39.R5.(20.$34.(35.$36.R2.))))(38.R8.(39.R5.(20.$34.(35.$36.R2.)))))P,(7=.R7.R5.R4.R3.)(7=.R7.R6.R5.R4.)")
(* [comment removed for export] *).
Proof.
  (intros st st' m a ar Hconc Hm dd_H; ddestruct dd_H as (H1 & H2 & H3)).
  assert (Hpw : forall p, pw st' p = pw st p). { intros [p|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity. }
  assert (Hmc : forall mr, meta_cells st' mr = meta_cells st mr) by (intros; unfold meta_cells; rewrite !Hpw; reflexivity).
  unfold area_rep. rewrite !Hconc, Hpw. split; [exact H1|]. split; [|exact H3].
  intros k Hk. rewrite Hmc, Hm by exact Hk. apply H2. exact Hk.
Qed.

Lemma group_rep_ext : ltac2:(CDefT.buildp (gd_tbl_MallocRep ()) "Pst,$70.Pst',$70.Pm,P,(3=.&40.)(52.(3=.&8.))Pb,$63.Pgh,$6>.P,Pp,$63.(3?.$30.(2<.R5.R1.)(2<.R6.R1.))P,(7>.R6.R4.R3.R2.)(7>.R6.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  (intros st st' m b gh Hconc dd_H; ddestruct dd_H as (w8 & H1 & H2)).
  assert (Hpw : forall p, pw st' p = pw st p). { intros [p|]; unfold pw, oconc; [rewrite Hconc|]; reflexivity. }
  exists w8. rewrite Hconc, Hpw. auto.
Qed.

Lemma shadow_rep_ext : ltac2:(CDefT.buildp (gd_tbl_MallocRep ()) "Pst,$70.Pst',$70.Pm,P,(3=.&40.)(52.(3=.&8.))Prid,$50.Pr,$51.P,(3?.$73.(49.R4.R2.)(49.R5.R2.))P,(7?.R6.R4.R3.R2.)(7?.R6.R5.R4.R3.)")
(* [comment removed for export] *).
Proof. intros st st' m rid r Hs [H1 H2]. split; [exact H1|]. intros o v Ho Hc. rewrite Hs in Hc. eauto. Qed.


(* [comment removed for export] *)
Lemma area_conc : ltac2:(CDefT.buildp (gd_tbl_MallocRep ()) "Pst,$70.Pa,(4=.$50.$30.)Par,$62.P,(7:.R3.)P,(3?.(52.$62.)(53.(4=.$50.$30.)$62.(54.$63.(64.$50.$55.$30.$65.)(66.$50.$55.$56.$30.$65.$67.)$62.)(57.$63.(64.$50.$55.$30.$65.)(66.$50.$55.$56.$30.$65.$67.)$62.)R3.(68.R4.))(59.$62.R2.))(3<.$51.Lr,$51.(1:.(3?.(52.$51.)(53.$50.$51.(54.$50.$55.$56.$51.)(57.$50.$55.$56.$51.)(69.$50.$30.R5.)(58.R6.))(59.$51.R1.))(1:.(3?.$30.(2<.R6.R5.)(20.(44.R1.)(6:.$50.$30.R5.)))(1:.(31.=(6:.$50.$30.R5.))(1:.(31.(20.(6:.$50.$30.R5.)+1000.)(45.(46.R1.)))(1:.(3?.$30.(5:.(6:.$50.$30.R5.)+1000.)=)(1:.(5?.(3?.$6;.(6<.R1.)$6=.))(1:.(32.=(44.R1.))(1:.(3?.$30.(5:.(44.R1.)+1000.)=)(31.(20.(44.R1.)(45.(46.R1.)))(5;.R6.)))))))))))")
(* [comment removed for export] *).
Proof.
  (intros st a ar dd_H; ddestruct dd_H as (_ & WR & _ & WA & _); intros Ha). ddestruct (WA a ar Ha) as (r & Hr & A0 & A1 & AL & NK & _).
  destruct (WR _ r Hr) as (B0 & BAL & _ & BC & _).
  exists r. rewrite (conc_region' st a r Hr). repeat split; auto.
Qed.

Lemma group_conc : ltac2:(CDefT.buildp (gd_tbl_MallocRep ()) "Pst,$70.Pb,(4=.$50.$30.)Pgh,$6>.P,(7:.R3.)P,(3?.(52.$6>.)(53.(4=.$50.$30.)$6>.(54.$63.(64.$50.$55.$30.$65.)(66.$50.$55.$56.$30.$65.$67.)$6>.)(57.$63.(64.$50.$55.$30.$65.)(66.$50.$55.$56.$30.$65.$67.)$6>.)R3.(6?.R4.))(59.$6>.R2.))(3<.$51.Lr,$51.(1:.(3?.(52.$51.)(53.$50.$51.(54.$50.$55.$56.$51.)(57.$50.$55.$56.$51.)(69.$50.$30.R5.)(58.R6.))(59.$51.R1.))(1:.(3?.$30.(2<.R6.R5.)(20.(44.R1.)(6:.$50.$30.R5.)))(1:.(3?.$6;.(6<.R1.)$6=.)(1:.(31.=(6:.$50.$30.R5.))(1:.(31.(20.(6:.$50.$30.R5.)+10.)(45.(46.R1.)))(1:.(3?.$30.(5:.(6:.$50.$30.R5.)+10.)=)(1:.(32.=(44.R1.))(31.(20.(44.R1.)(45.(46.R1.)))(5;.R6.))))))))))")
(* [comment removed for export] *).
Proof.
  (intros st b gh dd_H; ddestruct dd_H as (_ & WR & _ & _ & WG); intros Hb). ddestruct (WG b gh Hb) as (r & Hr & K & B0 & B1 & AL).
  destruct (WR _ r Hr) as (R0 & _ & _ & RC & _).
  exists r. rewrite (conc_region' st b r Hr). repeat split; auto.
Qed.

(* [comment removed for export] *)
Lemma s_shadow_wr8 : ltac2:(CDefT.buildp (gd_tbl_MallocRep ()) "Pst,$70.Pp,$63.Pv,$30.(3?.(54.$50.$55.$56.$73.)(74.(80.R2.R1.R3.))(81.$50.$73.(54.$50.$55.$56.$73.)(82.$50.$73.(54.$50.$55.$56.$73.)(83.$50.$55.$56.$73.))(69.$50.$30.R2.)(84.(81.$30.(4=.$30.$50.)(54.$30.$65.$67.(4=.$30.$50.))(82.$30.(4=.$30.$50.)(54.$30.$65.$67.(4=.$30.$50.))(83.$30.$65.$67.(4=.$30.$50.)))(6:.$50.$30.R2.)(85.$30.$50.(40.R1.+??.)(78.R3.))(86.(49.R3.(69.$50.$30.R2.))))(75.(49.R3.(69.$50.$30.R2.)))(79.(49.R3.(69.$50.$30.R2.))))(74.R3.)))")
(* [comment removed for export] *).
Proof. intros. reflexivity. Qed.

Lemma get_shadow_unfold : forall st rid, get_shadow st rid = default shadow0 ((s_shadow st) !! rid).
Proof. reflexivity. Qed.

Lemma get_shadow_wr8_same : ltac2:(CDefT.buildp (gd_tbl_MallocRep ()) "Pst,$70.Pp,$63.Pv,$30.(3?.$73.(49.(80.R2.R1.R3.)(69.$50.$30.R2.))(84.(81.$30.(4=.$30.$50.)(54.$30.$65.$67.(4=.$30.$50.))(82.$30.(4=.$30.$50.)(54.$30.$65.$67.(4=.$30.$50.))(83.$30.$65.$67.(4=.$30.$50.)))(6:.$50.$30.R2.)(85.$30.$50.(40.R1.+??.)(78.R3.))(86.(49.R3.(69.$50.$30.R2.))))(75.(49.R3.(69.$50.$30.R2.)))(79.(49.R3.(69.$50.$30.R2.)))))")
(* [comment removed for export] *).
Proof. intros. rewrite (get_shadow_unfold (wr8 p v st)), s_shadow_wr8, lookup_insert_eq. reflexivity. Qed.

Lemma get_shadow_wr8_other : forall st p v rid, rid <> fst p ->
  get_shadow (wr8 p v st) rid = get_shadow st rid.
Proof. intros. rewrite (get_shadow_unfold (wr8 p v st)), s_shadow_wr8, lookup_insert_ne by congruence. reflexivity. Qed.

Lemma cell_read_wr8_other : ltac2:(CDefT.buildp (gd_tbl_MallocRep ()) "Pst,$70.Pp,(4=.$50.$30.)Pv,$30.Po,$30.P,(5?.(3?.$30.R1.(6:.$50.$30.R3.)))(3?.$47.(48.(49.(80.R4.R3.R5.)(69.$50.$30.R4.))R2.)(48.(49.R5.(69.$50.$30.R4.))R2.))")
(* [comment removed for export] *).
Proof. intros. rewrite get_shadow_wr8_same. unfold cell_read. cbn [r_cells r_hav r_havp]. rewrite lookup_insert_ne by congruence. reflexivity. Qed.

Lemma cell_read_wr8_same : ltac2:(CDefT.buildp (gd_tbl_MallocRep ()) "Pst,$70.Pp,$63.Pv,$30.P,(87.R3.)P,(1:.(31.=R2.)(32.R2.+100.))(3?.$47.(48.(49.(80.R4.R3.R5.)(69.$50.$30.R4.))(6:.$50.$30.R4.))(4:.R3.))")
(* [comment removed for export] *).
Proof.
  intros st p v [T1 T2] Hv. rewrite get_shadow_wr8_same. unfold cell_read. cbn [r_cells r_hav r_havp]. rewrite lookup_insert_eq.
  replace (Z.land v 255) with v by (change 255 with (Z.ones 8); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
  unfold get_shadow. destruct (s_shadow st !! fst p) as [sh|] eqn:E; cbn.
  - assert (SP : stale_pg (r_havp sh !! (snd p `div` 4096)) (Some (s_tick st)) = false).
    { unfold stale_pg. destruct (r_havp sh !! (snd p `div` 4096)) eqn:E2; [|reflexivity].
      apply N.ltb_ge. eapply T2; eauto. }
    assert (SU : stale (default [] (r_hav sh !! (snd p `div` 16))) (snd p `mod` 16) (Some (s_tick st)) = false).
    { unfold stale. apply Bool.not_true_iff_false. rewrite existsb_exists. (intros dd_H; ddestruct dd_H as ([cov t] & Hin & Hb)).
      destruct (r_hav sh !! (snd p `div` 16)) eqn:E3; cbn in Hin; [|contradiction].
      apply Bool.andb_true_iff in Hb. destruct Hb as [_ Hb]. apply N.ltb_lt in Hb.
      pose proof (T1 _ _ _ _ _ E E3 Hin) as HT. cbn [snd] in HT. exfalso. apply (N.lt_irrefl t). eapply N.le_lt_trans; [exact HT | exact Hb]. }
    rewrite SP, SU. reflexivity.
  - rewrite lookup_empty. cbn. reflexivity.
Qed.


(* [comment removed for export] *)
Lemma ticks_ok_wr8 : forall st p v, ticks_ok st -> ticks_ok (wr8 p v st).
Proof.
  intros st p v [T1 T2]. split.
  - intros rid sh u hl ch Hs Hu Hin. cbn [s_tick wr8 upd_shadow set_shadow] in *.
    rewrite s_shadow_wr8 in Hs. destruct (N.eq_dec rid (fst p)) as [->|NE].
    + rewrite lookup_insert_eq in Hs. inversion Hs; subst sh. cbn in Hu.
      unfold get_shadow in Hu. destruct (s_shadow st !! fst p) as [sh0|] eqn:E; cbn in Hu.
      * eapply T1; eauto.
      * rewrite lookup_empty in Hu. discriminate.
    + rewrite lookup_insert_ne in Hs by congruence. eapply T1; eauto.
  - intros rid sh pg t Hs Hp. cbn [s_tick wr8 upd_shadow set_shadow] in *.
    rewrite s_shadow_wr8 in Hs. destruct (N.eq_dec rid (fst p)) as [->|NE].
    + rewrite lookup_insert_eq in Hs. inversion Hs; subst sh. cbn in Hp.
      unfold get_shadow in Hp. destruct (s_shadow st !! fst p) as [sh0|] eqn:E; cbn in Hp.
      * eapply T2; eauto.
      * rewrite lookup_empty in Hp. discriminate.
    + rewrite lookup_insert_ne in Hs by congruence. eapply T2; eauto.
Qed.

Lemma wr8_mod : forall st p v, wr8 p v st = wr8 p (v mod 256) st.
Proof.
  intros. unfold wr8, upd_shadow. cbn beta.
  replace (Z.land (v mod 256) 255) with (Z.land v 255); [reflexivity|].
  change 255 with (Z.ones 8). rewrite !Z.land_ones by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma le2_split : forall v, 0 <= v < 65536 -> le2 (wz v) = [b8 (v mod 256); b8 (v / 256)].
Proof.
  intros v Hv. replace v with (v mod 256 + 256 * (v / 256)) at 1 by (pose proof (Z.div_mod v 256); lia).
  rewrite le2_lohi; [reflexivity| |]; [pose proof (Z.mod_pos_bound v 256); lia | split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]].
Qed.


(* [comment removed for export] *)
Lemma get_meta_rec_upd : forall st g f g',
  get_meta_rec (upd_meta g f st) g' = if aptr_eqb g' g then f (get_meta_rec st g) else get_meta_rec st g'.
Proof.
  intros. unfold get_meta_rec at 1. unfold upd_meta, put_meta. cbn [s_metas set_metas].
  unfold aptr_eqb. destruct g as [gr go], g' as [gr' go']. cbn [fst snd].
  destruct (N.eqb_spec gr' gr); destruct (Z.eqb_spec go' go); cbn [andb]; subst;
    first [rewrite lookup_insert_eq; reflexivity | rewrite lookup_insert_ne by congruence; reflexivity].
Qed.

Lemma aptr_eqb_refl : forall g, aptr_eqb g g = true.
Proof. intros [a b]. unfold aptr_eqb. cbn. rewrite N.eqb_refl, Z.eqb_refl. reflexivity. Qed.


(* [comment removed for export] *)
Lemma map_seq_upd : forall {X} (f g : nat -> X) (j : nat) (x : X) n s,
  (forall i, (s <= i < s + n)%nat -> g i = if Nat.eqb i j then x else f i) ->
  (s <= j)%nat ->
  map g (seq s n) = upd (map f (seq s n)) (j - s) x.
Proof.
  intros X f g j x n. induction n as [|n IH]; intros s Hg Hj; [reflexivity|].
  cbn [seq map]. destruct (Nat.eq_dec j s) as [->|NE].
  - rewrite Nat.sub_diag. cbn [upd]. rewrite Hg by lia. rewrite Nat.eqb_refl. f_equal.
    apply map_ext_in. intros i Hi. apply in_seq in Hi. rewrite Hg by lia.
    destruct (Nat.eqb_spec i s); [lia|reflexivity].
  - replace (j - s)%nat with (S (j - S s)) by lia. cbn [upd]. f_equal.
    + rewrite Hg by lia. destruct (Nat.eqb_spec s j); [lia|reflexivity].
    + apply IH; [intros; apply Hg; lia|lia].
Qed.

Lemma active_set_active : forall st sc v i,
  active (set_active sc v st) i = if Z.eqb i sc then v else active st i.
Proof.
  intros. unfold active, set_active, upd_ctx. cbn [ctx s_ctx c_active set_active_map].
  destruct v as [p|]; destruct (Z.eqb_spec i sc); subst.
  - rewrite lookup_insert_eq. reflexivity.
  - rewrite lookup_insert_ne by congruence. reflexivity.
  - rewrite lookup_delete_eq. reflexivity.
  - rewrite lookup_delete_ne by congruence. reflexivity.
Qed.

Lemma actives_set_active : ltac2:(CDefT.buildp (gd_tbl_MallocRep ()) "Pst,$70.Psc,$30.Pv,$88.P,(1:.(31.=R2.)(32.R2.+30.))(3?.(4<.(3=.&40.))(21.(89.R3.R2.R4.))(8:.(3=.&40.)(21.R4.)(8;.R3.)(3.R4.R2.)))")
(* [comment removed for export] *).
Proof.
  intros st sc v Hsc. unfold actives.
  replace (Z.to_nat sc) with (Z.to_nat sc - 0)%nat by lia.
  apply (map_seq_upd (fun i => pw st (active st (Z.of_nat i))) (fun i => pw (set_active sc v st) (active (set_active sc v st) (Z.of_nat i)))); [|lia].
  intros i Hi. rewrite active_set_active.
  assert (Hpw : forall q, pw (set_active sc v st) q = pw st q) by (intros [q|]; reflexivity).
  rewrite Hpw. destruct (Z.eqb_spec (Z.of_nat i) sc); destruct (Nat.eqb_spec i (Z.to_nat sc)); try reflexivity; lia.
Qed.


(* [comment removed for export] *)
Definition sh_ticks (sh : shadow) (t : N) : Prop := ltac2:(CDefT.buildp (gd_tbl_MallocRep ()) "(1:.Pu,$30.Phl,(4<.(4=.$30.$50.))Pch,(4=.$30.$50.)P,(3?.(52.(4<.(4=.$30.$50.)))(53.$30.(4<.(4=.$30.$50.))(54.$30.$65.$67.(4<.(4=.$30.$50.)))(57.$30.$65.$67.(4<.(4=.$30.$50.)))R3.(75.O2.))(59.(4<.(4=.$30.$50.))R2.))P,(76.(4=.$30.$50.)R2.R3.)(77.(6:.$30.$50.R3.)O1.)Ppg,$30.Pt',$50.P,(3?.(52.$50.)(53.$30.$50.(54.$30.$65.$67.$50.)(57.$30.$65.$67.$50.)R2.(79.O2.))(59.$50.R1.))(77.R2.O1.))")
(* [comment removed for export] *).

Definition shadow_le (sh sh' : shadow) : Prop :=
  r_cells sh' = r_cells sh /\ forall o v, cell_read sh' o = Known v -> cell_read sh o = Known v.

Lemma shadow_le_refl : forall sh, shadow_le sh sh. Proof. intros; split; auto. Qed.
Lemma shadow_le_trans : forall a b c, shadow_le a b -> shadow_le b c -> shadow_le a c.
Proof. intros a b c [E1 H1] [E2 H2]. split; [congruence|]. eauto. Qed.

Lemma In_filter_bool : forall {A} (f : A -> bool) (l : list A) x,
  In x (filter (fun y => f y) l) <-> In x l /\ f x = true.
Proof.
  intros A f l x. rewrite <- !list_elem_of_In. rewrite list_elem_of_filter.
  unfold Is_true. destruct (f x); intuition congruence.
Qed.

Lemma stale_hav_add : ltac2:(CDefT.buildp (gd_tbl_MallocRep ()) "Phl,(4<.(4=.$30.$50.))Pcov,$30.Pt,$50.Pb,$30.Ptc,(52.$50.)P,Pch,(4=.$30.$50.)P,(76.(4=.$30.$50.)R1.R6.)(77.(6:.$30.$50.R2.)R5.)P,(3?.$5<.(8<.(8=.R5.R4.R6.)R3.R2.)$8>.)(3?.$5<.(8<.R7.R4.R3.)$8>.)")
(* [comment removed for export] *).
Proof.
  intros hl cov t b tc Ht Hs. unfold stale in *.
  apply Bool.not_true_iff_false. apply Bool.not_true_iff_false in Hs. rewrite existsb_exists in *.
  (intros dd_H; ddestruct dd_H as ([c' h'] & Hin & Hb)). apply Hs. cbn [fst snd] in Hb.
  apply Bool.andb_true_iff in Hb. destruct Hb as [Hb1 Hb2]. apply Z.ltb_lt in Hb1.
  destruct (Z.ltb_spec cov c').
  - exists (c', h'). split; [|cbn [fst snd]; rewrite (proj2 (Z.ltb_lt _ _) Hb1), Hb2; reflexivity].
    unfold hav_add. right. apply In_filter_bool. split; [exact Hin|]. cbn. apply Z.ltb_lt. assumption.
  - exists (cov, t). split; [unfold hav_add; left; reflexivity|]. cbn [fst snd].
    rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [andb].
    destruct tc as [tc|]; [|reflexivity]. apply N.ltb_lt. apply N.ltb_lt in Hb2.
    pose proof (Ht _ Hin) as Hh. cbn [snd] in Hh. eapply N.lt_le_trans; [exact Hb2|exact Hh].
Qed.

Lemma hav_unit_step : ltac2:(CDefT.buildp (gd_tbl_MallocRep ()) "Pcells,(54.$30.$65.$67.(4=.$30.$50.))Phav,(54.$30.$65.$67.(4<.(4=.$30.$50.)))Phavp,(54.$30.$65.$67.$50.)Pu,$30.Pcov,$30.Pt,$50.P,(8?.(84.R6.R5.R4.)R1.)(1:.(90.(84.R7.R6.R5.)(84.R7.(81.$30.(4<.(4=.$30.$50.))(54.$30.$65.$67.(4<.(4=.$30.$50.)))(82.$30.(4<.(4=.$30.$50.))(54.$30.$65.$67.(4<.(4=.$30.$50.)))(83.$30.$65.$67.(4<.(4=.$30.$50.))))R4.(8=.R3.R2.(91.(4<.(4=.$30.$50.))(4<.(4=.$30.$50.))(92.(4<.(4=.$30.$50.)))(<.(4=.$30.$50.))(53.$30.(4<.(4=.$30.$50.))(54.$30.$65.$67.(4<.(4=.$30.$50.)))(57.$30.$65.$67.(4<.(4=.$30.$50.)))R4.R6.)))R6.)R5.))(8?.(84.R7.(81.$30.(4<.(4=.$30.$50.))(54.$30.$65.$67.(4<.(4=.$30.$50.)))(82.$30.(4<.(4=.$30.$50.))(54.$30.$65.$67.(4<.(4=.$30.$50.)))(83.$30.$65.$67.(4<.(4=.$30.$50.))))R4.(8=.R3.R2.(91.(4<.(4=.$30.$50.))(4<.(4=.$30.$50.))(92.(4<.(4=.$30.$50.)))(<.(4=.$30.$50.))(53.$30.(4<.(4=.$30.$50.))(54.$30.$65.$67.(4<.(4=.$30.$50.)))(57.$30.$65.$67.(4<.(4=.$30.$50.)))R4.R6.)))R6.)R5.)R2.))")
(* [comment removed for export] *).
Proof.
  intros cells hav havp u cov t [T1 T2]. cbn [r_hav r_havp] in T1, T2.
  assert (Hl : forall ch, In ch (default [] (hav !! u)) -> (snd ch <= t)%N).
  { intros ch Hin. destruct (hav !! u) eqn:E2; cbn in Hin; [eapply T1; eauto| contradiction]. }
  split.
  - split; [reflexivity|]. intros o v Hc. unfold cell_read in *. cbn [r_cells r_hav r_havp] in *.
    destruct (Z.eq_dec (o / 16) u) as [E|NE].
    + rewrite E, lookup_insert_eq in Hc. cbn [default from_option id] in Hc. rewrite E.
      destruct (cells !! o) as [[v0 tc]|].
      * destruct (stale_pg (havp !! (o / 4096)) (Some tc)) eqn:SP; [cbn in Hc; discriminate|].
        destruct (stale (hav_add cov t (default [] (hav !! u))) (o mod 16) (Some tc)) eqn:SU; [cbn in Hc; discriminate|].
        rewrite (stale_hav_add _ _ _ _ _ Hl SU). exact Hc.
      * destruct (stale_pg (havp !! (o / 4096)) None) eqn:SP; [cbn in Hc; discriminate|].
        destruct (stale (hav_add cov t (default [] (hav !! u))) (o mod 16) None) eqn:SU; [cbn in Hc; discriminate|].
        rewrite (stale_hav_add _ _ _ _ _ Hl SU). exact Hc.
    + rewrite lookup_insert_ne in Hc by congruence. exact Hc.
  - split; cbn [r_hav r_havp]; [|exact T2].
    intros u' hl ch Hu Hin. destruct (Z.eq_dec u' u) as [->|NE].
    + rewrite lookup_insert_eq in Hu. inversion Hu; subst hl. unfold hav_add in Hin. destruct Hin as [<-|Hin]; [cbn; lia|].
      apply In_filter_bool in Hin. destruct Hin as [Hin _]. apply Hl. exact Hin.
    + rewrite lookup_insert_ne in Hu by congruence. eapply T1; eauto.
Qed.

Lemma hav_page_step : ltac2:(CDefT.buildp (gd_tbl_MallocRep ()) "Pcells,(54.$30.$65.$67.(4=.$30.$50.))Phav,(54.$30.$65.$67.(4<.(4=.$30.$50.)))Phavp,(54.$30.$65.$67.$50.)Ppg,$30.Pt,$50.P,(8?.(84.R5.R4.R3.)R1.)(1:.(90.(84.R6.R5.R4.)(84.R6.R5.(81.$30.$50.(54.$30.$65.$67.$50.)(82.$30.$50.(54.$30.$65.$67.$50.)(83.$30.$65.$67.$50.))R3.R2.R4.)))(8?.(84.R6.R5.(81.$30.$50.(54.$30.$65.$67.$50.)(82.$30.$50.(54.$30.$65.$67.$50.)(83.$30.$65.$67.$50.))R3.R2.R4.))R2.))")
(* [comment removed for export] *).
Proof.
  intros cells hav havp pg t [T1 T2]. cbn [r_hav r_havp] in T1, T2. split.
  - split; [reflexivity|]. intros o v Hc. unfold cell_read in *. cbn [r_cells r_hav r_havp] in *.
    destruct (Z.eq_dec (o / 4096) pg) as [E|NE].
    + rewrite E, lookup_insert_eq in Hc. rewrite E.
      destruct (cells !! o) as [[v0 tc]|]; cbn [stale_pg orb] in Hc.
      * destruct (N.ltb_spec tc t); [discriminate|].
        destruct (havp !! pg) as [h|] eqn:E2; cbn [stale_pg].
        -- pose proof (T2 _ _ E2). replace (tc <? h)%N with false by (symmetry; apply N.ltb_ge; lia). exact Hc.
        -- exact Hc.
      * discriminate.
    + rewrite lookup_insert_ne in Hc by congruence. exact Hc.
  - split; cbn [r_hav r_havp]; [exact T1|].
    intros pg' t' Hp. destruct (Z.eq_dec pg' pg) as [->|NE].
    + rewrite lookup_insert_eq in Hp. inversion Hp; subst. lia.
    + rewrite lookup_insert_ne in Hp by congruence. eapply T2; eauto.
Qed.

Lemma Z_iter_invariant : forall {A} (f : A -> A) (Inv : A -> Prop) n x,
  (forall y, Inv y -> Inv (f y)) -> Inv x -> Inv (Z.iter n f x).
Proof.
  intros A f Inv n x Hf Hx. destruct n; cbn; auto. apply Pos.iter_invariant; auto.
Qed.

Lemma havoc_units_le : ltac2:(CDefT.buildp (gd_tbl_MallocRep ()) "Pcells,(54.$30.$65.$67.(4=.$30.$50.))Phav,(54.$30.$65.$67.(4<.(4=.$30.$50.)))Phavp,(54.$30.$65.$67.$50.)Px,$30.Py,$30.Pt,$50.P,(8?.(84.R6.R5.R4.)R1.)(1:.(90.(84.R7.R6.R5.)(84.R7.(93.R4.R3.R2.R6.)R5.))(8?.(84.R7.(93.R4.R3.R2.R6.)R5.)R2.))")
(* [comment removed for export] *).
Proof.
  intros cells hav havp x y t T. unfold havoc_units.
  set (f := fun acc : Z * gmap Z (list (Z * N)) => _).
  apply (Z_iter_invariant f (fun acc => shadow_le (mkShadow cells hav havp) (mkShadow cells (snd acc) havp)
                                         /\ sh_ticks (mkShadow cells (snd acc) havp) t)).
  - intros [u h] [HL HT]. unfold f. cbn [fst snd].
    destruct (hav_unit_step cells h havp u (if u =? (y - 1) / 16 then (let r := y mod 16 in if r =? 0 then 16 else r) else 16) t HT) as [HL2 HT2].
    split; [eapply shadow_le_trans; eauto| exact HT2].
  - cbn [snd]. split; [apply shadow_le_refl| exact T].
Qed.

Lemma havoc_pages_le : ltac2:(CDefT.buildp (gd_tbl_MallocRep ()) "Pcells,(54.$30.$65.$67.(4=.$30.$50.))Phav,(54.$30.$65.$67.(4<.(4=.$30.$50.)))Phavp,(54.$30.$65.$67.$50.)Pp0,$30.Pp1,$30.Pt,$50.P,(8?.(84.R6.R5.R4.)R1.)(1:.(90.(84.R7.R6.R5.)(84.R7.R6.(94.R4.R3.R2.R5.)))(8?.(84.R7.R6.(94.R4.R3.R2.R5.))R2.))")
(* [comment removed for export] *).
Proof.
  intros cells hav havp p0 p1 t T. unfold havoc_pages.
  set (f := fun acc : Z * gmap Z N => _).
  apply (Z_iter_invariant f (fun acc => shadow_le (mkShadow cells hav havp) (mkShadow cells hav (snd acc))
                                         /\ sh_ticks (mkShadow cells hav (snd acc)) t)).
  - intros [pg h] [HL HT]. unfold f. cbn [fst snd].
    destruct (hav_page_step cells hav h pg t HT) as [HL2 HT2].
    split; [eapply shadow_le_trans; eauto| exact HT2].
  - cbn [snd]. split; [apply shadow_le_refl| exact T].
Qed.

Lemma sh_ticks_of_ticks_ok : forall st rid, ticks_ok st -> sh_ticks (get_shadow st rid) (s_tick st).
Proof.
  intros st rid [T1 T2]. unfold get_shadow. destruct (s_shadow st !! rid) as [sh|] eqn:E; cbn.
  - split; [intros; eapply T1; eauto | intros; eapply T2; eauto].
  - split; cbn; intros; rewrite lookup_empty in *; discriminate.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition W_high (st : mstate) (W : list (Z * Z)) : Prop := forall lo hi, In (lo, hi) W -> s_ceil st <= lo.

Lemma W_high_disjoint : forall st W a n, W_high st W -> a + n <= s_ceil st -> disjoint_from W a n.
Proof.
  intros st. induction W as [|[lo hi] W IH]; intros a n HW Hn; cbn; [exact I|].
  split. { left. pose proof (HW lo hi ltac:(left; reflexivity)). lia. }
  apply IH; [| exact Hn]. intros lo' hi' Hin. apply (HW lo' hi'). right; exact Hin.
Qed.


Lemma ticks_ok_set_tick : forall st t, (s_tick st <= t)%N -> ticks_ok st -> ticks_ok (set_tick t st).
Proof.
  intros st t Ht [T1 T2]. split; cbn.
  - intros rid sh u hl ch H1 H2 H3. pose proof (T1 rid sh u hl ch H1 H2 H3). lia.
  - intros rid sh pg t' H1 H2. pose proof (T2 rid sh pg t' H1 H2). lia.
Qed.



(* [comment removed for export] *)
Ltac ceil_bounds :=
  repeat match goal with
  | |- context [s_ceil ?st] =>
      lazymatch goal with
      | _ : ALLOC_CEIL_LO <= s_ceil st <= ALLOC_CEIL_HI |- _ => fail
      | _ => let CB := fresh "CEILB" in pose proof (s_ceil_bounds st) as CB
      end
  | _ : context [s_ceil ?st] |- _ =>
      lazymatch goal with
      | _ : ALLOC_CEIL_LO <= s_ceil st <= ALLOC_CEIL_HI |- _ => fail
      | _ => let CB := fresh "CEILB" in pose proof (s_ceil_bounds st) as CB
      end
  end;
  unfold ALLOC_CEIL_LO, ALLOC_CEIL_HI in *.
