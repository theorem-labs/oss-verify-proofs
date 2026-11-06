(* fuzz_state image A, realloc thin segment S2a: [FSRealloc_inst.FS_seg_mid_a], the run from Allocate's return
   into __asan::Allocator::Reallocate (0x32994) to the indirect call of REAL(memcpy) (`jalr a3` 0x32a08, i.e.
   cfg_at 0x98a20 with ra = 0x32a0c).  It establishes ReallocG's [rmemcpy_pre] (dst = q under ly2, src = p under
   ly, len = min (req_size n_old) n, the old header's UsedSize) and [K2_fs].

   Rule 24 (released-proof lookup): a Theorem Labs lane (internal path; ossv proof
   index v5, 2026-10-28T21:58:24Z, ossv/recipes@566eb6ffa5df) answered CONFIRM for fuzz_state's ASan realloc chain:
   no released ASan-image proof of any fuzz_state function.  The released DONOR of this segment is cgif_rgb's
   lib/YF78.v:179-280 (pa2 / blkP / blkQ / blkDISJ / hdr_facts / mid_regs / c1_at_mid) over YF67.v:156-261
   (c1_copy); fs's Reallocate is byte-identical to cgif_rgb's modulo pc-relative fields, so the machine walk is
   ported in FSRealloc_S2a_walk.v and the allocator-side header / cell facts in FSRealloc_S2a_ar.v.  Owner ruling
   (a Theorem Labs lane, 2026-10-28 23:20-23:23Z): fs walks a Theorem Labs lane's shared thin segments directly on its own
   images, one text.

   THE SEGMENT ON A (capstone over the pinned A image, sha256 64b53ff86172bb07...; RV64, no compressed
   instructions).  Start cfg_at 0x32994 (`mv s4, a0` 00050a13, Allocate's return, FS_RA_ALLOC), end cfg_at
   0x98a20 (tfib_A_memcpy) with ra = 0x32a0c (FS_RA_COPY):
     0x32994 00050a13 mv s4, a0            0x329d4 0006d517 auipc a0, 0x6d   ) GOT 0x9f718 -> 0xa1568
     0x32998 08050863 beqz a0, 0x90    (not taken: a0 = q <> 0)
                                           0x329d8 d4453503 ld a0, -0x2bc(a0))
     0x3299c ff048503 lb a0, -0x10(s1)     0x329dc 00053683 ld a3, 0(a0)     (cell 0xa1568 -> 0x98a20)
     0x329a0 00200593 addi a1, zero, 2     0x329e0 08068663 beqz a3, 0x8c    (not taken)
     0x329a4 0230000f fence r, rw          0x329e4 ff24d503 lhu a0, -0xe(s1) (UsedSize high half = 0)
     0x329a8 02b50663 beq a0, a1, 0x2c     0x329e8 ff44e583 lwu a1, -0xc(s1) (UsedSize low word = req_size n_old)
        (TAKEN -> 0x329d4; the two error arms 0x329ac-0x329d0, `jal 0x23bf4` / `jal 0x240f0`, stay UNTAKEN:
         R2 placement rule, the chunk state of a live block is 2 = CHUNK_ALLOCATED)
     0x329ec 02051513 slli a0, a0, 0x20    0x329fc 000a0513 mv a0, s4        (dst = q)
     0x329f0 00b56533 or a0, a0, a1        0x32a00 00048593 mv a1, s1        (src = p)
     0x329f4 00a9e463 bltu s3, a0, 8       0x32a04 00098613 mv a2, s3        (len = min n UsedSize)
     0x329f8 00050993 mv s3, a0            0x32a08 000680e7 jalr a3

   No Axiom, no Admitted. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YP09 YP03.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG02 YG03 YG06 YG07 YG08 YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import AllocG DeallocG ReallocG RGtop.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AB1w AF0m AF0x AE2y.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSRealloc_inst.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSRealloc_S2a_walk FSRealloc_S2a_ar.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI16.sink_head := _.
Fail Definition probe_SH : OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable.YI14.sink_syms := _.

Module FSP := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.
Module FSI := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSRealloc_inst.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variable Up : list (Z * Z).

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Small helpers.                                                                                                    *)

Lemma map_eq_In_loc : forall {X Y : Type} (f g : X -> Y) (l : list X) x,
  map f l = map g l -> In x l -> f x = g x.
Proof.
intros X Y f g l x. induction l as [|y t IH]; intros E Hin; [destruct Hin|].
cbn in E. injection E as E1 E2. destruct Hin as [<-|Hin]; [exact E1 | exact (IH E2 Hin)].
Qed.

Lemma pres_at : forall (regs regs' : bvmap 5 word) (r : Z) (rb : bv 5),
  aregs_preserved regs regs' -> acallee_saved r -> Z_to_bv 5 r = rb -> getr regs' rb = getr regs rb.
Proof. intros regs regs' r rb H Hc E. rewrite <- E. exact (H r Hc). Qed.

Lemma mbyte_eq_of_aview : forall (H H' : word -> bool) (m m' : word -> option byte) a,
  aview tfibsegs H' m' a = aview tfibsegs H m a ->
  mbyte tfibsegs (mrestrict H' m') a = mbyte tfibsegs (mrestrict H m) a.
Proof.
intros H H' m m' a E.
destruct (mbyte tfibsegs (mrestrict H m) a) as [b|] eqn:Eb.
- assert (A : aview tfibsegs H m a = Some (bv_unsigned b)) by (unfold aview; rewrite Eb; reflexivity).
  rewrite A in E. rewrite (AF0x.aview_byte H' m' a _ E), Z_to_bv_bv_unsigned. reflexivity.
- destruct (mbyte tfibsegs (mrestrict H' m') a) as [b'|] eqn:Eb'; [|reflexivity].
  exfalso. unfold aview in E. rewrite Eb, Eb' in E. discriminate E.
Qed.

Lemma val_mem_of_aview : forall (H H' : word -> bool) (m m' : word -> option byte) a (w : nat) v,
  (forall i, 0 <= i < Z.of_nat w -> aview tfibsegs H' m' (a + i) = aview tfibsegs H m (a + i)) ->
  val_mem tfibsegs (mrestrict H m) a w v -> val_mem tfibsegs (mrestrict H' m') a w v.
Proof.
intros H H' m m' a w v HE HV.
apply (AF0x.val_mem_ext (mrestrict H m) (mrestrict H' m') a w v); [|exact HV].
intros k Hk. apply mbyte_eq_of_aview. apply HE. lia.
Qed.

(* AFex.v:18 / AFfl.v:19 pairwise_nth, inlined: lib/A/AFex.v does not compile in this tree
   (batch_geom, AFex.v:244), so it must not be a dependency of this file. *)
Lemma pairwise_nth_loc {X} (R : X -> X -> Prop) : forall (l : list X) i j x y,
  pairwise R l -> nth_error l i = Some x -> nth_error l j = Some y -> (i < j)%nat -> R x y.
Proof.
induction l as [|a t IH]; intros [|i] [|j] x y P Hi Hj Hij; cbn in *; try discriminate; try lia.
- injection Hi as <-. destruct P as [F _]. apply nth_error_In in Hj. exact (proj1 (Forall_forall _ _) F _ Hj).
- destruct P as [_ P]. eapply IH; [exact P | exact Hi | exact Hj | lia].
Qed.

Lemma apresent_of_aview_high : forall (H : word -> bool) mem a,
  AF0x.TFIB_IMG_END <= a < 2 ^ 64 -> aview tfibsegs H mem a <> None -> apresent H mem a.
Proof.
intros H mem a Ha Hv. apply AF0x.aview_vis in Hv. unfold mbyte, mrestrict in Hv.
destruct (H (Z_to_bv 64 a)) eqn:Hh.
- exfalso. apply Hv. rewrite (AF0x.seg_rom_none_high a Ha). reflexivity.
- destruct (mem (Z_to_bv 64 a)) as [b|] eqn:Hb.
  + split; [exact Hh | exists b; exact Hb].
  + exfalso. apply Hv. rewrite (AF0x.seg_rom_none_high a Ha). reflexivity.
Qed.

Lemma aview_of_apresent : forall (H : word -> bool) mem a, apresent H mem a -> aview tfibsegs H mem a <> None.
Proof.
intros H mem a Hp. apply AF0x.aview_vis. destruct (AF0x.apresent_mbyte H mem a Hp) as (b & Hb).
rewrite Hb. discriminate.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)

Theorem fs_seg_mid_a : FSI.FS_seg_mid_a B Up.
Proof.
unfold FSI.FS_seg_mid_a, seg_mid_a.
intros ly S W regs mem md p n_old n ch S1 W1 so bp regsA memA mdA q ly2 S2 W2 regs2 mem2 md2.
intros RENT HK1 HAPRE HAPOST HQA HQNN HQIN HQP HLP HBLK1 HPIN2 HRPD.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (proj1 (@ASAN_CEIL_range _)) as CEILR. unfold ASAN_CEIL in CEILR.
(* the entry facts, the invariant at Allocate's call, Allocate's pre and post *)
destruct RENT as (RPRE & RP & HBLK & HFP & HA0 & HA1 & HN & HLB & HTR).
destruct RPRE as (RARX & RRET & RSP16 & RSLO & RBOT & RSHI & RPRES & RGP & RTP & RCH).
destruct HK1 as (HSEC & HRA & HSPA & H8 & H9 & H18 & H19 & HS7 & HFRAME & HTROBJ & HWIN & HSRC).
destruct HAPRE as (ARX1 & RPREA1 & RETOK & RA4096 & SP16 & SPLO & SPBOT & SPHI & PRESA & GP & TP
                   & PA0 & PA1 & PA2 & PA3 & PA4 & PA5 & SO1 & SO2 & SO3 & BP1 & BP2 & BP3
                   & TRLEN & VSO & VLEN & VTR & INU & NRG & LBND).
destruct HAPOST as (ARX2 & LLE & WLE2 & PRES & SIO & FRM & FRMW & PRESW).
assert (HARU1 : FSP.ARU tfibsegs B ly S1 Up W1 memA mdA) by (destruct ARX1 as (_ & HX); exact HX).
assert (HAR1 : AR tfibsegs B ly S1 W1 (FSP.unpoison Up memA) mdA) by (destruct HARU1 as (HX & _ & _); exact HX).
assert (HARU2 : FSP.ARU tfibsegs B ly2 S2 Up W2 mem2 md2) by (destruct ARX2 as (_ & HX); exact HX).
assert (HAR2 : AR tfibsegs B ly2 S2 W2 (FSP.unpoison Up mem2) md2) by (destruct HARU2 as (HX & _ & _); exact HX).
pose proof (am_layout B ly S1 _ (proj1 HAR1)) as LO1.
pose proof (lo_top ly LO1) as LTOP.
pose proof (lo_stk_ceil ly LO1) as LSC. unfold ASAN_CEIL in LSC.

(* ---- addresses: p's address does not move with the layout ---- *)
assert (EPA : sptr_addr B ly2 p = sptr_addr B ly p).
{ destruct (al_layout _ _ LAWS ly S1 W1 (FSP.unpoison Up memA) mdA ly2 HAR1 LLE) as (EAB & _ & _).
  unfold ablocks in EAB.
  pose proof (map_eq_In_loc (fun b : sptr * Z => (sptr_addr B ly2 (fst b), snd b))
                            (fun b : sptr * Z => (sptr_addr B ly (fst b), snd b)) (blocks S1) (p, n_old) EAB HBLK1) as E.
  cbn [fst snd] in E. injection E as E. exact E. }
assert (LLE0 : layout_le (length (st_secs S)) ly ly2)
  by exact (layout_le_trans (length (st_secs S)) (length (st_secs S1)) ly ly ly2 HSEC
              (layout_le_refl (length (st_secs S)) ly) LLE).
assert (LYSTK : ly_stk_lo ly2 = ly_stk_lo ly /\ ly_stk_hi ly2 = ly_stk_hi ly).
{ destruct LLE0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & E1 & E2 & _). split; [exact E1 | exact E2]. }
destruct LYSTK as (LYSLO & LYSHI).

(* ---- the two live blocks at (ly2, S2) ---- *)
assert (INQ : In (sptr_addr B ly2 q, n) (ablocks B ly2 S2))
  by (apply in_map_iff; exists (q, n); split; [reflexivity | exact HQIN]).
assert (INP2 : In (sptr_addr B ly p, n_old) (ablocks B ly2 S2)).
{ apply in_map_iff. exists (p, n_old). split; [cbn [fst snd]; rewrite EPA; reflexivity | exact HPIN2]. }
assert (INP1 : In (sptr_addr B ly p, n_old) (ablocks B ly S1))
  by (apply in_map_iff; exists (p, n_old); split; [reflexivity | exact HBLK1]).
destruct (al_blocks _ _ LAWS ly2 S2 W2 _ md2 _ _ HAR2 INQ) as (QM16 & Q4096 & QCEIL & QAPP & QPRES & QPW & QNR).
destruct (al_blocks _ _ LAWS ly2 S2 W2 _ md2 _ _ HAR2 INP2) as (PM16 & P4096 & PCEIL & PAPP & PPRES & _ & PNR).
destruct (al_blocks _ _ LAWS ly S1 W1 _ mdA _ _ HAR1 INP1) as (_ & _ & _ & _ & PPRES1 & _ & _).
assert (NN1 : 1 <= req_size n_old < 2 ^ 28)
  by (unfold req_size, MALLOC_MAX in *; destruct (Z.eqb_spec n_old 0); lia).
assert (NNQ' : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
assert (NMAX : 1 <= n < 2 ^ 28) by (unfold MALLOC_MAX in HN; lia).

(* ---- the two blocks are apart ---- *)
assert (DISJ : sptr_addr B ly2 q + req_size n <= sptr_addr B ly p
            \/ sptr_addr B ly p + req_size n_old <= sptr_addr B ly2 q).
{ destruct (In_nth_error _ _ HQIN) as (i & Hi).
  destruct (In_nth_error _ _ HPIN2) as (j & Hj).
  assert (IJ : i <> j) by (intros E; subst j; rewrite Hi in Hj; injection Hj as EQ1 EQ2; exact (HQP EQ1)).
  assert (HiA : nth_error (ablocks B ly2 S2) i = Some (sptr_addr B ly2 q, n)).
  { unfold ablocks.
    pose proof (map_nth_error (fun b : sptr * Z => (sptr_addr B ly2 (fst b), snd b)) i (blocks S2) Hi) as E.
    cbn [fst snd] in E. exact E. }
  assert (HjA : nth_error (ablocks B ly2 S2) j = Some (sptr_addr B ly p, n_old)).
  { unfold ablocks.
    pose proof (map_nth_error (fun b : sptr * Z => (sptr_addr B ly2 (fst b), snd b)) j (blocks S2) Hj) as E.
    cbn [fst snd] in E. rewrite EPA in E. exact E. }
  assert (HiL : nth_error (map (fun b : Z * Z => (fst b, req_size (snd b))) (ablocks B ly2 S2)) i
                = Some (sptr_addr B ly2 q, req_size n)).
  { pose proof (map_nth_error (fun b : Z * Z => (fst b, req_size (snd b))) i (ablocks B ly2 S2) HiA) as E.
    cbn [fst snd] in E. exact E. }
  assert (HjL : nth_error (map (fun b : Z * Z => (fst b, req_size (snd b))) (ablocks B ly2 S2)) j
                = Some (sptr_addr B ly p, req_size n_old)).
  { pose proof (map_nth_error (fun b : Z * Z => (fst b, req_size (snd b))) j (ablocks B ly2 S2) HjA) as E.
    cbn [fst snd] in E. exact E. }
  destruct (lt_eq_lt_dec i j) as [[LT|EQ]|GT]; [| exfalso; exact (IJ EQ) |].
  - pose proof (pairwise_nth_loc zdisjoint _ i j _ _ QPW HiL HjL LT) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. lia.
  - pose proof (pairwise_nth_loc zdisjoint _ j i _ _ QPW HjL HiL GT) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. lia. }

(* ---- the header and the two image cells, read through the user poison ---- *)
destruct (s2a_hdr B TB ly2 S2 W2 (FSP.unpoison Up mem2) md2 p n_old HAR2 HPIN2) as (HZP & HV0 & HV2 & HV4).
destruct (s2a_hdr B TB ly2 S2 W2 (FSP.unpoison Up mem2) md2 q n HAR2 HQIN) as (HZQ & _ & _ & _).
destruct (s2a_cells B TB ly2 S2 W2 (FSP.unpoison Up mem2) md2 HAR2) as (HC1 & HC2).
rewrite EPA in HZP, HV0, HV2, HV4.
unfold AF0x.zone3, AF0x.zone3cases, AF0x.TFIB_IMG_LO, AF0x.TFIB_IMG_END, ASAN_CEIL in HZP, HZQ.
assert (UNP : forall x : word, (bv_unsigned x < kLowShadowBeg \/ kHighMemBeg <= bv_unsigned x) ->
  FSP.unpoison Up mem2 x = mem2 x) by (intros x Hx; exact (s2a_unpoison_mem B ly2 S2 Up W2 mem2 md2 x HARU2 Hx)).
assert (MOVE : forall a (w : nat) v,
  (forall i, 0 <= i < Z.of_nat w -> 0 <= a + i < 2 ^ 64 /\ (a + i < kLowShadowBeg \/ kHighMemBeg <= a + i)) ->
  val_mem tfibsegs (mrestrict (w_H W2) (FSP.unpoison Up mem2)) a w v ->
  val_mem tfibsegs (mrestrict (w_H W2) mem2) a w v).
{ intros a w v HB HV.
  apply (AF0x.val_mem_ext (mrestrict (w_H W2) (FSP.unpoison Up mem2)) (mrestrict (w_H W2) mem2) a w v); [|exact HV].
  intros k Hk. apply (AF0x.mbyte_mrestrict_same (w_H W2) (FSP.unpoison Up mem2) mem2).
  destruct (HB (Z.of_nat k) ltac:(lia)) as (HR & HS).
  symmetry. apply UNP. rewrite YP03.unsigned_lit_small by lia. exact HS. }
assert (HV0' : val_mem tfibsegs (mrestrict (w_H W2) mem2) (sptr_addr B ly p - 16) 1 2).
{ apply MOVE; [intros i Hi; cbn [Z.of_nat] in Hi; unfold kLowShadowBeg, kHighMemBeg in *; lia | exact HV0]. }
assert (HV2' : val_mem tfibsegs (mrestrict (w_H W2) mem2) (sptr_addr B ly p - 14) 2 0).
{ apply MOVE; [intros i Hi; cbn [Z.of_nat] in Hi; unfold kLowShadowBeg, kHighMemBeg in *; lia | exact HV2]. }
assert (HV4' : val_mem tfibsegs (mrestrict (w_H W2) mem2) (sptr_addr B ly p - 12) 4 (req_size n_old)).
{ apply MOVE; [intros i Hi; cbn [Z.of_nat] in Hi; unfold kLowShadowBeg, kHighMemBeg in *; lia | exact HV4]. }
assert (HC1' : val_mem tfibsegs (mrestrict (w_H W2) mem2) 0x9f718 8 0xa1568).
{ apply MOVE; [intros i Hi; cbn [Z.of_nat] in Hi; unfold kLowShadowBeg, kHighMemBeg in *; lia | exact HC1]. }
assert (HC2' : val_mem tfibsegs (mrestrict (w_H W2) mem2) 0xa1568 8 0x98a20).
{ apply MOVE; [intros i Hi; cbn [Z.of_nat] in Hi; unfold kLowShadowBeg, kHighMemBeg in *; lia | exact HC2]. }

(* ---- the registers at Allocate's return ---- *)
assert (E2b : Z_to_bv 5 2 = (2%bv : bv 5)) by (apply bv_eq; vm_compute; reflexivity).
assert (E3b : Z_to_bv 5 3 = (3%bv : bv 5)) by (apply bv_eq; vm_compute; reflexivity).
assert (E4b : Z_to_bv 5 4 = (4%bv : bv 5)) by (apply bv_eq; vm_compute; reflexivity).
assert (E8b : Z_to_bv 5 8 = (8%bv : bv 5)) by (apply bv_eq; vm_compute; reflexivity).
assert (E9b : Z_to_bv 5 9 = (9%bv : bv 5)) by (apply bv_eq; vm_compute; reflexivity).
assert (E18b : Z_to_bv 5 18 = (18%bv : bv 5)) by (apply bv_eq; vm_compute; reflexivity).
assert (E19b : Z_to_bv 5 19 = (19%bv : bv 5)) by (apply bv_eq; vm_compute; reflexivity).
assert (R2 : getr regs2 2 = getr regsA 2)
  by exact (pres_at regsA regs2 2 _ PRES ltac:(unfold acallee_saved; lia) E2b).
assert (R3 : getr regs2 3 = getr regsA 3)
  by exact (pres_at regsA regs2 3 _ PRES ltac:(unfold acallee_saved; lia) E3b).
assert (R4 : getr regs2 4 = getr regsA 4)
  by exact (pres_at regsA regs2 4 _ PRES ltac:(unfold acallee_saved; lia) E4b).
assert (R8 : getr regs2 8 = getr regsA 8)
  by exact (pres_at regsA regs2 8 _ PRES ltac:(unfold acallee_saved; lia) E8b).
assert (R9 : getr regs2 9 = getr regsA 9)
  by exact (pres_at regsA regs2 9 _ PRES ltac:(unfold acallee_saved; lia) E9b).
assert (R18 : getr regs2 18 = getr regsA 18)
  by exact (pres_at regsA regs2 18 _ PRES ltac:(unfold acallee_saved; lia) E18b).
assert (R19 : getr regs2 19 = getr regsA 19)
  by exact (pres_at regsA regs2 19 _ PRES ltac:(unfold acallee_saved; lia) E19b).
assert (RS7 : forall r, 23 <= r <= 27 -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)).
{ intros r Hr. rewrite (PRES r ltac:(unfold acallee_saved; lia)). exact (HS7 r Hr). }
assert (SP2 : spZ regs2 = spZ regs - FS_RFRAME) by (unfold spZ; rewrite R2; exact HSPA).

(* ---- realloc's stack window: what lives there, and what does not ---- *)
assert (ERRV : as_errno B = TFIB_ERRNO) by exact (ts_errno B TB).
assert (STKIN : forall a, spZ regs - ASTACK <= a < spZ regs -> ly_stk_lo ly <= a < ly_stk_hi ly)
  by (intros a Ha; unfold ASTACK in *; lia).
assert (NOWN1 : forall a, spZ regs - ASTACK <= a < spZ regs -> ~ aowned B ly S1 a)
  by (intros a Ha; exact (al_stack _ _ LAWS ly S1 W1 _ mdA a HAR1 (STKIN a Ha))).
assert (NOWN2 : forall a, spZ regs - ASTACK <= a < spZ regs -> ~ aowned B ly2 S2 a).
{ intros a Ha. apply (al_stack _ _ LAWS ly2 S2 W2 _ md2 a HAR2).
  destruct (STKIN a Ha). rewrite LYSLO, LYSHI. lia. }
assert (STKNQ : forall a, spZ regs - ASTACK <= a < spZ regs ->
  ~ (q <> PNull /\ sptr_addr B ly2 q <= a < sptr_addr B ly2 q + req_size n)).
{ intros a Ha [_ Hb]. unfold ASTACK in *. lia. }
assert (STKR : forall a, spZ regs - ASTACK <= a < spZ regs -> AF0x.TFIB_IMG_END <= a < 2 ^ 64).
{ intros a Ha. unfold AF0x.TFIB_IMG_END, ASTACK, kHighMemEnd in *. lia. }
assert (FRUP : forall a, spZ regsA <= a < spZ regs ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W1) memA a).
{ intros a Ha. assert (HW : spZ regs - ASTACK <= a < spZ regs) by (unfold ASTACK, FS_RFRAME in *; lia).
  apply FRM.
  - pose proof (STKR a HW). unfold AF0x.TFIB_IMG_END in *. lia.
  - exact (NOWN1 a HW).
  - exact (NOWN2 a HW).
  - intros [Hs|Hs]; [unfold AFSTACK_G in Hs; lia|].
    rewrite ERRV in Hs. unfold TFIB_ERRNO in Hs. unfold ASTACK in *. lia.
  - exact (STKNQ a HW). }
assert (FRLOW : forall a, spZ regs - ASTACK <= a < spZ regsA - AFSTACK_G ->
  aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W1) memA a).
{ intros a Ha. assert (HW : spZ regs - ASTACK <= a < spZ regs) by (unfold AFSTACK_G, FS_RFRAME in *; lia).
  apply FRM.
  - pose proof (STKR a HW). unfold AF0x.TFIB_IMG_END in *. lia.
  - exact (NOWN1 a HW).
  - exact (NOWN2 a HW).
  - intros [Hs|Hs]; [unfold AFSTACK_G in *; lia|].
    rewrite ERRV in Hs. unfold TFIB_ERRNO in Hs. unfold ASTACK in *. lia.
  - exact (STKNQ a HW). }

(* ---- the machine walk ---- *)
rewrite HRA.
eapply SRr_mono.
{ apply (s2a_walk W2 md2 regs2 mem2 (sptr_addr B ly2 q) (sptr_addr B ly p) n (req_size n_old)).
  - rewrite R9. exact H9.
  - exact HQA.
  - rewrite R19. exact H19.
  - lia.
  - lia.
  - lia.
  - unfold AF0x.zone3, AF0x.zone3cases, AF0x.TFIB_IMG_LO, AF0x.TFIB_IMG_END, ASAN_CEIL.
    unfold kLowShadowBeg, kHighMemBeg in *. lia.
  - exact HV0'.
  - exact HV2'.
  - exact HV4'.
  - exact HC1'.
  - exact HC2'. }
intros W3 c3 _ (-> & regsM & memM & mat & -> & MEQ & RM1 & RM10 & RM11 & RM12 & RM20 & RMK).

(* ---- the postcondition ---- *)
assert (AVM : forall a, aview tfibsegs (w_H W2) memM a = aview tfibsegs (w_H W2) mem2 a)
  by (intros a; apply AF0x.aview_same; apply MEQ).
assert (SBM : same_but_materialized md2 (with_vm_backing (m_vm_lazy md2) mat md2))
  by apply with_vm_backing_same.
pose proof (same_but_materialized_frame md2 _ SBM) as MF.
assert (LENC : Z.min n (req_size n_old) = Z.min (req_size n_old) n) by apply Z.min_comm.
rewrite LENC in RM12.
assert (VMSTK : forall a (w : nat) v, spZ regsA <= a -> a + Z.of_nat w <= spZ regs ->
  val_mem tfibsegs (mrestrict (w_H W1) memA) a w v -> val_mem tfibsegs (mrestrict (w_H W2) memM) a w v).
{ intros a w v HA1' HA2' HV.
  apply (val_mem_of_aview (w_H W1) (w_H W2) memA memM a w v); [|exact HV].
  intros i Hi. rewrite AVM. apply FRUP. lia. }
exists regsM, memM, (with_vm_backing (m_vm_lazy md2) mat md2).
split; [reflexivity|].
(* rmemcpy_pre *)
split.
{ unfold rmemcpy_pre.
  split.
  { unfold YK0s.ret_ok. rewrite RM1. unfold FS_RA_COPY, w64. apply bv_eq. vm_compute. reflexivity. }
  split; [exact RM10|]. split; [exact RM11|]. split; [exact RM12|].
  split; [lia|]. split; [lia|].
  split; [lia|].
  split; [lia|].
  split; [lia|].
  split; [lia|].
  split.
  { intros a Ha. apply AE2y.apresent_writable.
    apply (AF0x.apresent_same (w_H W2) mem2 memM a (MEQ _)).
    destruct (QPRES a ltac:(lia)) as (HP & _).
    destruct HP as (Hh & bb & Hb). split; [exact Hh|]. exists bb. rewrite <- Hb. symmetry. apply UNP.
    rewrite YP03.unsigned_lit_small by lia. unfold kLowShadowBeg, kHighMemBeg in *. lia. }
  intros a Ha. rewrite AVM. apply aview_of_apresent.
  destruct (PPRES a ltac:(lia)) as (HP & _).
  destruct HP as (Hh & bb & Hb). split; [exact Hh|]. exists bb. rewrite <- Hb. symmetry. apply UNP.
  rewrite YP03.unsigned_lit_small by lia. unfold kLowShadowBeg, kHighMemBeg in *. lia. }
(* the source bytes are realloc's entry bytes *)
split.
{ intros i Hi. rewrite AVM.
  rewrite (FRM (sptr_addr B ly p + i)).
  - apply HSRC. lia.
  - lia.
  - exact (proj2 (PPRES1 (sptr_addr B ly p + i) ltac:(lia))).
  - exact (proj2 (PPRES (sptr_addr B ly p + i) ltac:(lia))).
  - intros [Hs|Hs]; [unfold AFSTACK_G in *; lia|].
    rewrite ERRV in Hs. unfold TFIB_ERRNO, kLowShadowBeg, kHighMemBeg in *. lia.
  - intros [_ Hb]. lia. }
(* the new block is off realloc's window *)
split.
{ intros a Ha. split; [lia|].
  intros [Hs|Hs]; [unfold ASTACK in *; lia|].
  rewrite ERRV in Hs. unfold TFIB_ERRNO, kLowShadowBeg, kHighMemBeg in *. lia. }
(* same_io *)
split; [exact (rg_sbm_io md2 _ SBM)|].
(* rkeep: the walk stores nothing (MEQ), in the view and in the raw memory *)
split; [split; [intros a _ _; exact (AVM a) | intros x _; exact (MEQ x)]|].
(* K2_fs *)
unfold FSI.K2_fs.
split; [exact HQNN|].
split; [rewrite (RMK 3%bv ltac:(cbn [In]; tauto)), R3; exact GP|].
split; [rewrite (RMK 4%bv ltac:(cbn [In]; tauto)), R4; exact TP|].
split; [exact HQIN|].
split; [unfold raZ; rewrite RM1; unfold FS_RA_COPY, w64; apply YP03.unsigned_lit_small; lia|].
split; [unfold spZ; rewrite (RMK 2%bv ltac:(cbn [In]; tauto)); exact SP2|].
split; [rewrite (RMK 8%bv ltac:(cbn [In]; tauto)), R8; exact H8|].
split; [rewrite (RMK 9%bv ltac:(cbn [In]; tauto)), R9; exact H9|].
split; [rewrite (RMK 18%bv ltac:(cbn [In]; tauto)), R18; exact H18|].
split; [exact RM20|].
split.
{ intros r Hr.
  assert (RB : In (Z_to_bv 5 r) [2; 3; 4; 8; 9; 18; 21; 22; 23; 24; 25; 26; 27; 29; 30; 31]%bv).
  { assert (CS : r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct CS as [->|[->|[->|[->| ->]]]]; cbn [In];
    repeat first [ left; apply bv_eq; vm_compute; reflexivity | right ]. }
  rewrite (RMK (Z_to_bv 5 r) RB). exact (RS7 r Hr). }
split.
{ unfold FSI.fs_rframe in HFRAME |- *.
  destruct HFRAME as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
  unfold FS_RFRAME in *.
  split; [apply VMSTK; [lia | lia | exact F1]|].
  split; [apply VMSTK; [lia | lia | exact F2]|].
  split; [apply VMSTK; [lia | lia | exact F3]|].
  split; [apply VMSTK; [lia | lia | exact F4]|].
  split; [apply VMSTK; [lia | lia | exact F5]|].
  split; [apply VMSTK; [lia | lia | exact F6]|].
  split; [apply VMSTK; [lia | lia | exact F7]|].
  split; [apply VMSTK; [lia | lia | exact F8]|].
  split; [apply VMSTK; [lia | lia | exact F9]|].
  apply VMSTK; [lia | lia | exact F10]. }
split.
{ unfold FSI.fs_trobj in HTROBJ |- *.
  destruct HTROBJ as (T0 & T1 & T2 & T3).
  unfold FS_SO, FS_RFRAME in *.
  split; [exact T0|].
  split; [apply VMSTK; [lia | lia | exact T1]|].
  split; [apply VMSTK; [lia | lia | exact T2]|].
  intros i Hi. apply VMSTK; [lia | lia | exact (T3 i Hi)]. }
split.
{ intros a Ha.
  apply (AF0x.apresent_same (w_H W2) mem2 memM a (MEQ _)).
  destruct (Z_lt_le_dec a (spZ regsA - AFSTACK_G)) as [L1|L1].
  - apply (apresent_of_aview_high (w_H W2) mem2 a (STKR a ltac:(unfold ASTACK in *; lia))).
    rewrite (FRLOW a ltac:(unfold ASTACK in *; lia)). apply aview_of_apresent. apply HWIN. lia.
  - destruct (Z_lt_le_dec a (spZ regsA)) as [L2|L2].
    + apply PRESW. lia.
    + apply (apresent_of_aview_high (w_H W2) mem2 a (STKR a ltac:(unfold ASTACK in *; lia))).
      rewrite (FRUP a ltac:(unfold ASTACK, FS_RFRAME in *; lia)). apply aview_of_apresent. apply HWIN. lia. }
split.
{ split; [reflexivity|].
  apply (FSP.ARU_frame tfibsegs B LAWS ly2 S2 Up W2 mem2 md2 memM
           (with_vm_backing (m_vm_lazy md2) mat md2) HARU2).
  - intros a _ _. exact (AVM a).
  - intros a Hv. rewrite AVM. exact Hv.
  - apply MF.
  - apply MF.
  - apply MF.
  - intros a _ _. apply MEQ. }
split; [exact LLE0 | exact EPA].
Qed.

End s.
