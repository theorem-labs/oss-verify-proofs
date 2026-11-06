(* fuzz_state image B, realloc thin segment S2b: the copy routine's return -> Reallocate's `jal Deallocate`.
   The RGtop hypothesis is [seg_mid_b K2_fs K3_fs] at fs's image-B instance (lib/B/FSRealloc_inst.v, [FS_seg_mid_b]);
   this file proves it ([fs_seg_mid_b]) over a Theorem Labs lane's c5 RGtop (2bd8ae006ef).
   The B twin of lib/A/FSRealloc_S2b.v (a working branch ab749aeaed7): the same proof, at image B's
   addresses and instance.

   Rule 24 (released-proof lookup): proves function __asan::Allocator::Reallocate chain on fs image B
   (fuzz_state.asan-ubsan: __wrap_realloc 0x530e8 -> __interceptor_realloc 0x534e4 -> asan_realloc 0x328ec ->
   Allocator::Reallocate 0x32998), segment S2b.  proof-index, unpiped, 2026-10-29 ~03:55Z
   (internal path): `proof-index: end; 0x530e8: 0 named, 0 by address, 0 related,
   0 lemma(s), 0 by file name, an earlier delivery 0 named and 0 name(s) holding it`; the same 0 / 0 / 0 for 0x534e4;
   `__asan::Allocator::Reallocate: 0 named, 32 by address` (other units); control preset_base64_encode found.  Named
   cold branches: r24/1029/cold-search.md and b-check.md; second-agent checker a Theorem Labs lane: CONFIRM.  The only other holder
   of these walks is fs's pre-ruling bespoke line, a TEMPLATE ONLY (owner ruling a Theorem Labs lane 04:50Z): S2b lies inside
   ricptC_spec (a working branch, proofs/omx-clap-core/fuzz_state/lib/AZ/AsanW/AReallocP.v:370), which
   runs through the copy without a cut here; it is not bridged.
   TEMPLATES: primary, lib/A/FSRealloc_S2b.v @ ab749aeaed7 (fs image A, proved); its donor is cgif_rgb_fuzzer's
   released realloc family, proofs/cgif/cgif_rgb_fuzzer/lib/YF78.v:553 (tfx_arealloc) with YF67 / YF6p: S2b is the
   donor's step from REAL(memcpy)'s return 0x32584 to `jal Deallocate` 0x3259c, i.e. YF67.v:126 (c1_postM, the register
   list at the Deallocate call), YF6p.v:45 (DCFACTS) and YF78.v:289-358 (the regsD / memD hypotheses D1..DP, AR_D,
   PRE_D).

   fs's B body of Reallocate is A's at +0x70, word for word except 0x32a48 (lib/B/FSRealloc_inst.v header), so the
   seven instructions below are A's (and the donor's); their B addresses come from a Theorem Labs lane's
   realloc-thin/fs-addr-map.tsv (fs_asan_ubsan_hex column: 0x32a7c FS_RA_COPY, 0x32a94 the Deallocate call) and are
   re-checked here by disassembly (python3 capstone, RV64, no compressed instructions) over the pinned B image
   projects/omx-clap-core/bin/fuzz_state/fuzz_state.asan-ubsan
   (sha256 5ac5ce0954f87e2d050c481b7b0599cfd55ef554eadc008e51491f44c053d204):

     0x32a7c  00100793  addi a5, zero, 1      (the copy's return pc, FS_RA_COPY)
     0x32a80  00090513  mv   a0, s2           (a0 = inst)
     0x32a84  00048593  mv   a1, s1           (a1 = the old block p)
     0x32a88  00000613  mv   a2, zero         (delete_size = 0)
     0x32a8c  00000693  mv   a3, zero         (delete_alignment = 0)
     0x32a90  00040713  mv   a4, s0           (a4 = the interceptor's stack object so)
     0x32a94  9bcff0ef  jal  -0xe44           (-> Allocator::Deallocate 0x31c50 `addi sp, sp, -0x40` (fc010113),
                                               ra = 0x32a98 = FS_RA_DEALLOC `mv a0, s4` (000a0513))

   The segment is straight-line: no branch, no load, no store, no call but the final one, so it meets no ASan error
   path (the R2 placement rule is vacuous here) and reads no .bss cell and no image byte other than these seven
   instruction words.  Memory is unchanged: memD = mem3, W4 = W3.

   START-UP CELLS: none is read (no load).  The one start-up value the statement carries is the Definition
   TFIB_INST = 0xa4dd8 (Reallocate's inst, through K2_fs / dealloc_pre), taken from a working branch's lib/B/YF0m.v:16 (as
   lib/B/FSRealloc_inst.v does) and equal there and in B's table of record a Theorem Labs lane's startup/regenB/YF0m.new4.v:14.

   CLOSURE: this file Requires no lib/A file that names an image or holds a per-image address; its only lib/A
   Require is the image-free FSupoison.v (and, through lib/B/FSRealloc_inst.v, the image-free FSRealloc_rmodel.v).
   No file of another unit is relocated or copied by this file.

   TWO PREMISES THE PROOF NEEDS come from c5's statement: [HRAW], the RAW copy frame
   `forall x : word, ~ (q <= bv_unsigned x < q + min(req_size n_old, n)) ->
   mem3 x = memM x`, is seg_mid_b's premise (RGtop.v:289-290; amemcpy_realizes gives it, ReallocG.v:249; the donor had
   it: YF78.v:300 DM), needed because ARU's [ahs] part (YG0n.v:441-449) reads RAW memory at hidden in-band bytes, which
   an aview frame cannot reach; [HBOT], `ly_bot ly + FS_RFRAME < spZ regs`, is rentry's realloc_pre (ReallocG.v:120,
   RSTACK := FS_RFRAME), needed for Deallocate's `ly_bot ly2 < spZ regsD` at spZ regsD = spZ regs - FS_RFRAME.

   No Axiom, no Admitted. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YP09 YP02 YP03.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0q YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05 YN32.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import AllocG DeallocG ReallocG RGtop.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1w YF0m FSRealloc_inst.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI16.sink_head := _.
Fail Definition probe_SH : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI14.sink_syms := _.

Module FSU := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The seven instruction words of the segment, from the pinned B image.                                              *)

Definition s2b_text_start : Z := 0x32a7c.
Definition s2b_text_count : nat := 7.
Definition s2b_tbl : ctable := Eval vm_compute in
(build_table tfibsegs s2b_text_start s2b_text_count TEmpty).
Lemma s2b_tbl_eq : s2b_tbl = build_table tfibsegs s2b_text_start s2b_text_count TEmpty.
Proof. vm_cast_no_check (eq_refl s2b_tbl). Qed.
Lemma s2b_tbl_ok : table_ok tfibsegs s2b_tbl.
Proof. rewrite s2b_tbl_eq. apply build_table_ok0. cbv. discriminate. Qed.

Section fetch. Context {fx : YK11.FPState}.
Lemma s2b_fetch_lit : forall (p : word) (w : bv 32),
clookup s2b_tbl (bv_unsigned p) = Some (bv_unsigned w) -> fetch_word tfibsegs p = Some w.
Proof.
intros p w H. rewrite <- (Z_to_bv_bv_unsigned 64 p), <- (Z_to_bv_bv_unsigned 32 w).
apply s2b_tbl_ok. exact H.
Qed.
End fetch.
Ltac s2b_ftac := apply s2b_fetch_lit; vm_compute; reflexivity.

Section code. Context {fx : YK11.FPState}.
(* 0x32a7c  addi a5, zero, 1 *)
Lemma F_a7c : fetch_word tfibsegs (Z_to_bv 64 0x32a7c) = Some (0x00100793%bv : bv 32).
Proof. s2b_ftac. Qed.
Lemma D_a7c : decode_any (0x00100793%bv : bv 32) = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl_bv. Qed.
(* 0x32a80  mv a0, s2 *)
Lemma F_a80 : fetch_word tfibsegs (Z_to_bv 64 0x32a80) = Some (0x00090513%bv : bv 32).
Proof. s2b_ftac. Qed.
Lemma D_a80 : decode_any (0x00090513%bv : bv 32) = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl_bv. Qed.
(* 0x32a84  mv a1, s1 *)
Lemma F_a84 : fetch_word tfibsegs (Z_to_bv 64 0x32a84) = Some (0x00048593%bv : bv 32).
Proof. s2b_ftac. Qed.
Lemma D_a84 : decode_any (0x00048593%bv : bv 32) = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl_bv. Qed.
(* 0x32a88  mv a2, zero *)
Lemma F_a88 : fetch_word tfibsegs (Z_to_bv 64 0x32a88) = Some (0x00000613%bv : bv 32).
Proof. s2b_ftac. Qed.
Lemma D_a88 : decode_any (0x00000613%bv : bv 32) = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl_bv. Qed.
(* 0x32a8c  mv a3, zero *)
Lemma F_a8c : fetch_word tfibsegs (Z_to_bv 64 0x32a8c) = Some (0x00000693%bv : bv 32).
Proof. s2b_ftac. Qed.
Lemma D_a8c : decode_any (0x00000693%bv : bv 32) = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl_bv. Qed.
(* 0x32a90  mv a4, s0 *)
Lemma F_a90 : fetch_word tfibsegs (Z_to_bv 64 0x32a90) = Some (0x00040713%bv : bv 32).
Proof. s2b_ftac. Qed.
Lemma D_a90 : decode_any (0x00040713%bv : bv 32) = Some (OpImm ALU_ADD 14 8 0, 4%Z).
Proof. vm_refl_bv. Qed.
(* 0x32a94  jal -0xe44 -> 0x31c50 (Allocator::Deallocate), ra = 0x32a98 *)
Lemma F_a94 : fetch_word tfibsegs (Z_to_bv 64 0x32a94) = Some (0x9bcff0ef%bv : bv 32).
Proof. s2b_ftac. Qed.
Lemma D_a94 : decode_any (0x9bcff0ef%bv : bv 32) = Some (Jal 1 2093500, 4%Z).
Proof. vm_refl_bv. Qed.
End code.

Ltac s2b_gr :=
repeat first [ rewrite getr_same by reg_neq_tac | rewrite getr_other by reg_neq_tac ];
rewrite ?getr_zero.
Ltac s2b_stepiv F0 D vv tac := let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_addi_at with (v := vv); [ exact F | reflexivity | exact D | reflexivity | tac ]
| step_simpl ].
Ltac s2b_stepj F0 D := let F := litF F0 in stepj F D.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Small generic lemmas (no image, no ASan state).                                                                   *)

Section gen. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma s2b_wz : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 a) = a.
Proof.
intros a Ha. rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity|].
change (bv_modulus 64) with (2 ^ 64). lia.
Qed.

Lemma s2b_req_ge : forall n, n <= req_size n.
Proof. intros n. unfold req_size. destruct (Z.eqb_spec n 0); lia. Qed.

(* aview reads memory only at [Z_to_bv 64 a]. *)
Lemma s2b_aview_at : forall (H : word -> bool) (m m' : word -> option byte) a,
m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> aview tfibsegs H m' a = aview tfibsegs H m a.
Proof.
intros H m m' a E. unfold aview, mbyte, mrestrict.
destruct (H (Z_to_bv 64 a)); [reflexivity|]. rewrite E. reflexivity.
Qed.

Lemma s2b_aview_cong : forall (H : word -> bool) (m : word -> option byte) a b,
Z_to_bv 64 a = Z_to_bv 64 b -> aview tfibsegs H m a = aview tfibsegs H m b.
Proof. intros H m a b E. unfold aview, mbyte, mrestrict. rewrite E. reflexivity. Qed.

Lemma s2b_val_mem_keep : forall (H : word -> bool) (m m' : word -> option byte) lo hi a (w : nat) v,
(forall x, lo <= x < hi -> m' (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
lo <= a -> a + Z.of_nat w <= hi ->
val_mem tfibsegs (mrestrict H m) a w v -> val_mem tfibsegs (mrestrict H m') a w v.
Proof.
intros H m m' lo hi a w v HK Hlo Hhi HV k Hk.
assert (E : mbyte tfibsegs (mrestrict H m') (a + Z.of_nat k) = mbyte tfibsegs (mrestrict H m) (a + Z.of_nat k)).
{ unfold mbyte, mrestrict. destruct (H (Z_to_bv 64 (a + Z.of_nat k))); [reflexivity|].
  rewrite (HK (a + Z.of_nat k) ltac:(lia)). reflexivity. }
rewrite E. exact (HV k Hk).
Qed.

(* A callee-saved register, at a literal index. *)
Lemma s2b_pres : forall (regs regs' : bvmap 5 word) (r : Z) (rb : bv 5),
aregs_preserved regs regs' -> acallee_saved r -> Z_to_bv 5 r = rb ->
getr regs' rb = getr regs rb.
Proof. intros regs regs' r rb CS Hr <-. exact (CS r Hr). Qed.

Lemma s2b_mv : forall (x : word), v_addi x (bv_signed (0%bv : bv 12)) = x.
Proof.
intros x. replace (bv_signed (0%bv : bv 12)) with 0 by (vm_compute; reflexivity).
apply YK11.v_addi_0.
Qed.

End gen.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* A live block's bytes, read on the RAW memory (ARU's memory is the unpoisoned one).                                *)

Section blk. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable Up : list (Z * Z).
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

Lemma s2b_blk : forall ly S (W : world tfibsegs) mem md r m,
FSU.ARU tfibsegs B ly S Up W mem md -> In (r, m) (blocks S) ->
4096 <= sptr_addr B ly r /\ sptr_addr B ly r + req_size m <= alloc_ceiling /\
(forall x, sptr_addr B ly r <= x < sptr_addr B ly r + req_size m ->
   apresent (w_H W) mem x /\ ~ aowned B ly S x) /\
0 <= m < MALLOC_MAX.
Proof.
intros ly S W mem md r m ARU HIN.
assert (IN : In (sptr_addr B ly r, m) (ablocks B ly S)).
{ unfold ablocks. apply in_map_iff. exists (r, m). split; [reflexivity | exact HIN]. }
pose proof ARU as ARUc. destruct ARU as (HAR & OK & PO).
destruct (AR_blocks_law_ok tfibsegs B ly S W (FSU.unpoison Up mem) md _ _ HAR IN)
  as (_ & P4096 & PC & _ & PP & _ & PN).
pose proof (@alloc_ceiling_lt rc) as ACL.
split; [exact P4096|]. split; [exact PC|]. split; [|exact PN].
intros x Hx. destruct (PP x Hx) as (HP & HO). split; [|exact HO].
destruct HP as (HH & b & Hb). split; [exact HH|]. exists b. rewrite <- Hb. symmetry.
apply FSU.unpoison_out.
destruct (FSU.in_ush Up (bv_unsigned (Z_to_bv 64 x))) eqn:E; [exfalso|reflexivity].
pose proof (FSU.ush_facts tfibsegs B ly S Up W mem md _ ARUc E) as (HOWN & _).
rewrite (s2b_wz x ltac:(lia)) in HOWN. exact (HO HOWN).
Qed.

End blk.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The machine run: 0x32a7c -> 0x31c50 (Allocator::Deallocate), memory untouched.                                    *)

Section run. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma s2b_run : forall (W : world tfibsegs) (regs3 : bvmap 5 word) (mem3 : word -> option byte) (md3 : Model)
(Q : world tfibsegs -> config -> Prop),
(forall (regsD : bvmap 5 word) (mdD : Model),
   same_but_materialized md3 mdD ->
   aregs_preserved regs3 regsD ->
   getr regsD 1 = w64 FS_RA_DEALLOC ->
   getr regsD 10 = getr regs3 18 ->
   getr regsD 11 = getr regs3 9 ->
   getr regsD 12 = w64 0 ->
   getr regsD 13 = w64 0 ->
   getr regsD 14 = getr regs3 8 ->
   getr regsD 15 = w64 1 ->
   Q W (cfg_at tfibsegs tfib_A__ZN6__asan9Allocator10DeallocateEPvmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeE
     regsD mem3 mdD)) ->
SRr tfibsegs W (cfg_at tfibsegs FS_RA_COPY regs3 mem3 md3) Q.
Proof.
intros W regs3 mem3 md3 Q HK.
unfold cfg_at, FS_RA_COPY, w64.
eapply (SRr_msteps tfibsegs YF0x.Hwx_tfa W).
- rewrite restrict_mkst_fx.
  s2b_stepiv F_a7c D_a7c (Z_to_bv 64 1) ltac:(s2b_gr; apply bv_eq; vm_compute; reflexivity).
  s2b_stepiv F_a80 D_a80 (getr regs3 18) ltac:(s2b_gr; apply s2b_mv).
  s2b_stepiv F_a84 D_a84 (getr regs3 9) ltac:(s2b_gr; apply s2b_mv).
  s2b_stepiv F_a88 D_a88 (Z_to_bv 64 0) ltac:(s2b_gr; apply bv_eq; vm_compute; reflexivity).
  s2b_stepiv F_a8c D_a8c (Z_to_bv 64 0) ltac:(s2b_gr; apply bv_eq; vm_compute; reflexivity).
  s2b_stepiv F_a90 D_a90 (getr regs3 8) ltac:(s2b_gr; apply s2b_mv).
  s2b_stepj F_a94 D_a94.
  apply mst_refl.
- intros model' Hsbm _. cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
  match goal with
  | |- SRr _ _ (mkCfg (mkst _ ?P _ _) _) _ =>
      replace P with (w64 tfib_A__ZN6__asan9Allocator10DeallocateEPvmmPN11__sanitizer18BufferedStackTraceENS_9AllocTypeE)
        by (apply bv_eq; vm_compute; reflexivity)
  end.
  apply SRr_ret. unfold cfg_at. apply HK.
  + exact Hsbm.
  + intros r Hr. unfold acallee_saved in Hr.
    assert (RR : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                 r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    clear Hr.
    destruct RR as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[-> | ->]]]]]]]]]]]]]];
    s2b_gr; reflexivity.
  + s2b_gr. unfold FS_RA_DEALLOC, w64. apply bv_eq; vm_compute; reflexivity.
  + s2b_gr. reflexivity.
  + s2b_gr. reflexivity.
  + s2b_gr. reflexivity.
  + s2b_gr. reflexivity.
  + s2b_gr. reflexivity.
  + s2b_gr. reflexivity.
Qed.

End run.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* S2b at fs's image-B instance.                                                                                     *)

Section seg. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable Up : list (Z * Z).
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

Theorem fs_seg_mid_b : FS_seg_mid_b B Up.
Proof.
unfold FS_seg_mid_b, seg_mid_b.
intros ly S W regs mem md p n_old n ch q ly2 S2 W3 regsM memM mdM regs3 mem3 md3
  RENTRY K2 HBLK HRPD HU2 CS SBM HCOPY HRAW HPRES.
(* realloc's entry facts (c5's realloc_pre carries the stack margin HBOT, RSTACK := FS_RFRAME) *)
destruct RENTRY as (RPRE & _ & _ & HFPRE & _ & _ & HN & _ & _).
destruct RPRE as (ARX0 & _ & HSP16 & HSLO & HBOT & HSHI & _ & _ & _ & _).
(* the invariant at the copy's entry *)
destruct K2 as (HQN & HGP3 & HTP3 & HQLIVE & RAM & SPM & G8 & G9 & G18 & G20 & GK & RFR & TRO & RWIN & ARX2 & LLE & PA2).
destruct ARX2 as (_ & ARU2).
destruct ARX0 as (_ & ARU0).
(* the layout *)
assert (LY : layout_ok ly).
{ destruct ARU0 as (AR0 & _ & _). destruct AR0 as (ARm0 & _). exact (am_layout B ly S _ ARm0). }
pose proof (lo_stk_ceil ly LY) as SC0.
assert (SC : alloc_ceiling <= ly_stk_lo ly) by (unfold ASAN_CEIL in SC0; exact SC0).
destruct (lo_top ly LY) as (_ & _ & _ & THI0 & _ & _ & _).
assert (THI : ly_stk_hi ly <= 0x800000000000) by (unfold kHighMemEnd in THI0; exact THI0).
assert (HSLO' : ly_stk_lo ly + 16384 <= spZ regs) by (unfold ASTACK in HSLO; exact HSLO).
assert (HBOT' : ly_top ly - kStackSpan + 2208 < spZ regs)
  by (unfold ly_bot, FS_RFRAME in HBOT; exact HBOT).
pose proof LLE as LLE'.
destruct LLE' as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _ & _ & _ & _ & _ & _).
(* the new block and the old one *)
destruct (s2b_blk B Up ly2 S2 W3 memM mdM q n ARU2 HQLIVE) as (Q4096 & QC & QP & _).
destruct (s2b_blk B Up ly2 S2 W3 memM mdM p n_old ARU2 HBLK) as (_ & _ & PP2 & PN).
pose proof (s2b_req_ge n) as RN.
pose proof (s2b_req_ge n_old) as RNO.
pose proof (Z.le_min_l (req_size n_old) n) as LMIN1.
pose proof (Z.le_min_r (req_size n_old) n) as LMIN2.
assert (LEN : 0 <= Z.min (req_size n_old) n <= req_size n) by lia.
pose proof (@alloc_ceiling_lt rc) as ACL.
(* fold the three addresses *)
set (qa := sptr_addr B ly2 q) in *.
set (pa := sptr_addr B ly p) in *.
set (len := Z.min (req_size n_old) n) in *.
(* realloc's stack window is disjoint from the new block, so the copy keeps it byte for byte *)
assert (KEEP : forall x, spZ regs - ASTACK <= x < spZ regs -> mem3 (Z_to_bv 64 x) = memM (Z_to_bv 64 x)).
{ intros x Hx. unfold ASTACK in Hx. apply HRAW. rewrite s2b_wz by lia. lia. }
(* the rewritten p address under ly2 *)
assert (PA2' : sptr_addr B ly2 p = pa) by exact PA2.
(* the run *)
rewrite RAM.
apply (s2b_run W3 regs3 mem3 md3).
intros regsD mdD SBM2 CSD RAD G10 G11 G12 G13 G14 G15.
(* register transport through the copy and the segment *)
assert (CS2 : getr regs3 2 = getr regsM 2)
  by (apply (s2b_pres regsM regs3 2 2 CS); [unfold acallee_saved; lia | apply bv_eq; vm_compute; reflexivity]).
assert (CS3 : getr regs3 3 = getr regsM 3)
  by (apply (s2b_pres regsM regs3 3 3 CS); [unfold acallee_saved; lia | apply bv_eq; vm_compute; reflexivity]).
assert (CS4 : getr regs3 4 = getr regsM 4)
  by (apply (s2b_pres regsM regs3 4 4 CS); [unfold acallee_saved; lia | apply bv_eq; vm_compute; reflexivity]).
assert (CS8 : getr regs3 8 = getr regsM 8)
  by (apply (s2b_pres regsM regs3 8 8 CS); [unfold acallee_saved; lia | apply bv_eq; vm_compute; reflexivity]).
assert (CS9 : getr regs3 9 = getr regsM 9)
  by (apply (s2b_pres regsM regs3 9 9 CS); [unfold acallee_saved; lia | apply bv_eq; vm_compute; reflexivity]).
assert (CS18 : getr regs3 18 = getr regsM 18)
  by (apply (s2b_pres regsM regs3 18 18 CS); [unfold acallee_saved; lia | apply bv_eq; vm_compute; reflexivity]).
assert (CS20 : getr regs3 20 = getr regsM 20)
  by (apply (s2b_pres regsM regs3 20 20 CS); [unfold acallee_saved; lia | apply bv_eq; vm_compute; reflexivity]).
assert (CD2 : getr regsD 2 = getr regs3 2)
  by (apply (s2b_pres regs3 regsD 2 2 CSD); [unfold acallee_saved; lia | apply bv_eq; vm_compute; reflexivity]).
assert (CD3 : getr regsD 3 = getr regs3 3)
  by (apply (s2b_pres regs3 regsD 3 3 CSD); [unfold acallee_saved; lia | apply bv_eq; vm_compute; reflexivity]).
assert (CD4 : getr regsD 4 = getr regs3 4)
  by (apply (s2b_pres regs3 regsD 4 4 CSD); [unfold acallee_saved; lia | apply bv_eq; vm_compute; reflexivity]).
assert (CD20 : getr regsD 20 = getr regs3 20)
  by (apply (s2b_pres regs3 regsD 20 20 CSD); [unfold acallee_saved; lia | apply bv_eq; vm_compute; reflexivity]).
assert (SPD : spZ regsD = spZ regs - FS_RFRAME)
  by (unfold spZ in *; rewrite CD2, CS2; exact SPM).
assert (RAZD : raZ regsD = FS_RA_DEALLOC)
  by (unfold raZ; rewrite RAD; unfold w64, FS_RA_DEALLOC; rewrite s2b_wz by lia; reflexivity).
(* the allocator relation after the copy *)
assert (SBMD : same_but_materialized mdM mdD)
  by exact (same_but_materialized_trans mdM md3 mdD SBM SBM2).
destruct (same_but_materialized_frame mdM mdD SBMD) as (_ & Evm & Elz & _ & _ & _ & _).
assert (ARU3 : FSU.ARU tfibsegs B ly2 S2 Up W3 mem3 mdD).
{ apply (FSU.ARU_frame tfibsegs B LAWS ly2 S2 Up W3 memM mdM mem3 mdD ARU2).
  - intros a Ha Hown. apply s2b_aview_at. apply HRAW. rewrite s2b_wz by lia. intros HIn.
    destruct (QP a ltac:(lia)) as (_ & HO). exact (HO Hown).
  - intros a Hv.
    destruct (Z_le_dec qa (bv_unsigned (Z_to_bv 64 a))) as [H1|H1];
    [destruct (Z_lt_le_dec (bv_unsigned (Z_to_bv 64 a)) (qa + len)) as [H2|H2]|].
    + assert (EA : aview tfibsegs (w_H W3) mem3 a
                 = aview tfibsegs (w_H W3) mem3 (qa + (bv_unsigned (Z_to_bv 64 a) - qa))).
      { apply s2b_aview_cong.
        replace (qa + (bv_unsigned (Z_to_bv 64 a) - qa)) with (bv_unsigned (Z_to_bv 64 a)) by lia.
        rewrite Z_to_bv_bv_unsigned. reflexivity. }
      rewrite EA, (HCOPY (bv_unsigned (Z_to_bv 64 a) - qa) ltac:(lia)).
      destruct (PP2 (pa + (bv_unsigned (Z_to_bv 64 a) - qa)) ltac:(lia)) as ((HH & b & Hb) & _).
      unfold aview, mbyte, mrestrict. rewrite HH, Hb. cbn. discriminate.
    + rewrite (s2b_aview_at _ _ _ _ (HRAW (Z_to_bv 64 a) ltac:(lia))). exact Hv.
    + rewrite (s2b_aview_at _ _ _ _ (HRAW (Z_to_bv 64 a) ltac:(lia))). exact Hv.
  - exact Evm.
  - exact Elz.
  - unfold eager_used. rewrite Evm, Elz. reflexivity.
  - intros a Hb Hh.
    change (mem3 (Z_to_bv 64 a) = memM (Z_to_bv 64 a)).
    change (w_H W3 (Z_to_bv 64 a) = true) in Hh.
    apply HRAW. intros HIn.
    destruct (QP (bv_unsigned (Z_to_bv 64 a)) ltac:(lia)) as ((HH & _) & _).
    rewrite Z_to_bv_bv_unsigned in HH. rewrite HH in Hh. discriminate Hh. }
(* the stack object and its trace buffer *)
destruct TRO as (TRL & TR0 & TR8 & TRI).
destruct RFR as (RF1 & RF2 & RF3 & RF4 & RF5 & RF6 & RF7 & RF8 & RF9 & RF10).
(* every val_mem of the two frames moves to mem3 *)
assert (VM : forall a (w : nat) v, spZ regs - ASTACK <= a -> a + Z.of_nat w <= spZ regs ->
  val_mem tfibsegs (mrestrict (w_H W3) memM) a w v -> val_mem tfibsegs (mrestrict (w_H W3) mem3) a w v).
{ intros a w v Hlo Hhi HV.
  exact (s2b_val_mem_keep (w_H W3) memM mem3 (spZ regs - ASTACK) (spZ regs) a w v KEEP Hlo Hhi HV). }
assert (RFR3 : fs_rframe regs W3 mem3).
{ unfold fs_rframe.
  repeat split;
  (apply VM; [unfold FS_RFRAME, ASTACK; lia | unfold FS_RFRAME; lia | assumption]). }
assert (TRO3 : fs_trobj regs (call_trace ly FS_AREALLOC_IPC_B regs ch) W3 mem3).
{ unfold fs_trobj. split; [exact TRL|].
  split; [apply VM; [unfold FS_SO, ASTACK; lia | unfold FS_SO; lia | exact TR0]|].
  split; [apply VM; [unfold FS_SO, ASTACK; lia | unfold FS_SO; lia | exact TR8]|].
  intros i Hi. apply VM; [unfold FS_SO, ASTACK; lia | unfold FS_SO; lia | exact (TRI i Hi)]. }
assert (RWIN3 : rwin tfibsegs regs W3 mem3) by (intros a Ha; apply HPRES; exact (RWIN a Ha)).
destruct TRO3 as (_ & TB0 & TB8 & TBI).
(* the result *)
exists (spZ regs - FS_SO), (spZ regs - FS_SO + 16), regsD, mem3, mdD.
split; [reflexivity|].
split.
{ unfold dealloc_pre.
  split; [split; [reflexivity | exact ARU3]|].
  split; [exact HRPD|].
  split. { unfold YK0s.ret_ok. rewrite RAD. unfold w64, FS_RA_DEALLOC. apply bv_eq; vm_compute; reflexivity. }
  split; [rewrite RAZD; unfold FS_RA_DEALLOC; lia|].
  split. { rewrite SPD. unfold FS_RFRAME. rewrite Zminus_mod, HSP16. reflexivity. }
  split; [rewrite Eslo, SPD; unfold FS_RFRAME, DFSTACK_G; lia|].
  split. { unfold ly_bot. rewrite Etop, SPD. unfold FS_RFRAME. lia. }
  split; [rewrite Eshi, SPD; unfold FS_RFRAME; lia|].
  split. { intros a Ha. apply HPRES. apply RWIN. rewrite SPD in Ha.
           unfold FS_RFRAME, DFSTACK_G in Ha. unfold ASTACK. lia. }
  split; [rewrite CD3, CS3; exact HGP3|].
  split; [rewrite CD4, CS4; exact HTP3|].
  split; [rewrite G10, CS18; exact G18|].
  split; [rewrite G11, CS9, PA2'; exact G9|].
  split; [exact G12|].
  split; [exact G13|].
  split; [rewrite G14, CS8; exact G8|].
  split; [exact G15|].
  split; [rewrite SPD; unfold FS_RFRAME, FS_SO; lia|].
  split; [rewrite Eshi; unfold FS_SO; lia|].
  split. { unfold FS_SO.
    destruct (proj1 (Z.mod_divide (spZ regs) 16 ltac:(lia)) HSP16) as [c Hc]. rewrite Hc.
    replace (c * 16 - 2136) with ((2 * c - 267) * 8) by lia. apply Z.mod_mul. lia. }
  split; [rewrite SPD; unfold FS_RFRAME, FS_SO; lia|].
  split; [rewrite Eshi; unfold FS_SO; lia|].
  split. { unfold FS_SO.
    destruct (proj1 (Z.mod_divide (spZ regs) 16 ltac:(lia)) HSP16) as [c Hc]. rewrite Hc.
    replace (c * 16 - 2136 + 16) with ((2 * c - 265) * 8) by lia. apply Z.mod_mul. lia. }
  split; [exact TRL|].
  split; [exact TB0|].
  split; [exact TB8|].
  split; [exact TBI|].
  split; [exact HU2|].
  split; [right; exact HBLK|].
  unfold FS_fpre in HFPRE |- *. rewrite PA2'. exact HFPRE. }
split; [exact (rg_sbm_io md3 mdD SBM2)|].
split. { unfold rin. rewrite SPD. unfold FS_RFRAME, DFSTACK_G, ASTACK. lia. }
split. { split; [intros a _ _; reflexivity | intros x _; reflexivity]. }
split; [exact RWIN3|].
(* K3 *)
unfold K3_fs.
split; [exact HQN|].
split; [exact HQLIVE|].
split; [exact LLE|].
split; [exact RAZD|].
split; [exact SPD|].
split; [rewrite CD20, CS20; exact G20|].
split.
{ intros r Hr.
  rewrite (CSD r ltac:(unfold acallee_saved; lia)), (CS r ltac:(unfold acallee_saved; lia)).
  exact (GK r Hr). }
split; [exact RFR3|].
exact RWIN3.
Qed.

End seg.
