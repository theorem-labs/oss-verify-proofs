(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryAdmit), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACjo.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntryAdmit.v, with its module paths and module names changed; 2079 of its 2128 lines of code are new or changed and 610 lines of the source are left out. *)
(* The cuts of case 1 of fuzz_boxreg's LLVMFuzzerTestOneInput on the ASan build, the slots 0x803a8 .. 0x80ab4
   (fuzz_boxreg.c:287-362, `case 1:` of `switch (op & 3)`), and two of its four pieces. The case itself, from
   the cut GI_T 1 i to the cut GI_K i of lib/A/Prog/BoxLxDefs.v, is gb_case1 of lib/A/Prog/BoxLxCase1.v; the
   pieces of this file are c1_seg_scan (0x806cc .. 0x807a8) and c1_seg_want (0x807a8 .. 0x807e8).

   What the case does, and where this file cuts it:
     0x803a8 (GP_T 1)   read_mac (&in, op & 4, mac), inlined. op & 4 = 0: __asan_memcpy (mac, read_mac.base, 5)
                        at 0x803c4 from the registered global 0x20d00 (bytes 00 40 ab 00 00) and one input byte
                        into mac[5]; op & 4 <> 0: the six-byte loop 0x8048c .. 0x804d8, each byte read after the
                        check of its shadow byte, and 0 for each byte the input lacks. Then the nch byte (slot
                        0x58), 0 when the input is spent.
     0x806cc (PC1_nch)  bcmp (mac, ZERO, 6) -> s11, the `nonzero` flag; prev.n -> s9; then the scan of prev's
                        rows 0x80714 .. 0x80790, two bcmp per row and the shadow-tested load of prev.box[j].nch,
                        which leaves `held` in s6 and `bind` in s10.
     0x807a8 (PC1_dec)  the legal-width / nonzero decision and, when it is needed, lowest_free (prev, nch, fab)
                        at 0x80d0c; it leaves `want` in s6, n_before in s10 and lf in slot 0x30.
     0x807e8 (PC1_call) reac_boxreg_find (r, mac) at 0x807f4, reac_boxreg_add (r, mac, nch) at 0x80808, and the
                        checks 0x80810 .. 0x80920 (find again at 0x80878, add again at 0x8088c, bcmp of
                        r->box[idx].mac against mac at 0x80868, and the shadow-tested loads of r->box[idx].nch,
                        .base and .pinned). Every abort branch (0x80f60) is refuted by Pau's address-free lemmas
                        of lib/Prog/LLVMFuzzerTestOneInput_case1.v.
     0x80ab4 (GP_K)     the join: s5 = (-1) mod 2 ^ 32 (the case renames no row), r holds add's bytes.

   The MAC is the frame object mac = F + GO_MAC, an afobj of the side-stack frame (find, add and the bcmp
   wrapper read it); prev = F + GO_PREV holds the table as the turn found it. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG0s YI16 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal BoxSyms BoxList BoxPa BoxPaLib BoxBase.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import YC1g YC1h YC81 YC85 BoxFrame BoxCJ BoxRo.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import ReacBoxregInit.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require ReacBoxregFind ReacBoxregAdd LowestFree.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Rt Require SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Prog Require Import BoxLxDefs BoxLxSeat.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require
Boxreg LLVMFuzzerTestOneInput_inv LLVMFuzzerTestOneInput_case1
reac_boxreg_add_c reac_boxreg_find_c lowest_free_c reac_boxreg_add_inv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the pcs inside the case, as offsets in the listing (address - 0x7ff4c) ---- *)
Definition PC1_mac0 : Z := 0x45c.   (* 0x803a8  GP_T 1: read_mac is next                        *)
Definition PC1_nch : Z := 0x780.    (* 0x806cc  mac holds its six bytes, nch is in slot 0x58    *)
Definition PC1_scan : Z := 0x7c8.   (* 0x80714  the head of the scan of prev's rows             *)
Definition PC1_dec : Z := 0x85c.    (* 0x807a8  the scan is done: held in s6, bind in s10       *)
Definition PC1_call : Z := 0x89c.   (* 0x807e8  want in s6, n_before in s10, lf in slot 0x30    *)

(* ---- the model of the case, over Pau's address-free lemmas ---- *)

(* The scan's two results, at the end of the rows, as the add model states them. *)
Lemma c1_held_of : forall bs M v h,
  LLVMFuzzerTestOneInput_case1.c1_sh bs M v (Boxreg.bx_n bs) h -> 0 <= h ->
  reac_boxreg_add_c.add_held bs M h.
Proof.
  intros bs M v h [(E & _) | (_ & Hh & Hm & Hn)] H0; [lia|].
  split; [exact Hh|]. split; [exact Hm | exact Hn].
Qed.

Lemma c1_nheld_of : forall bs M v,
  LLVMFuzzerTestOneInput_case1.c1_sh bs M v (Boxreg.bx_n bs) (-1) -> v <> 0 ->
  reac_boxreg_add_c.add_none_held bs M.
Proof.
  intros bs M v [(_ & [E | N]) | (_ & H & _)] Hv; [contradiction | exact N | lia].
Qed.

Lemma c1_unb_of : forall bs k u,
  LLVMFuzzerTestOneInput_case1.c1_su bs k (Boxreg.bx_n bs) u -> 0 <= u ->
  reac_boxreg_add_c.add_unbound bs k u.
Proof.
  intros bs k u [(E & _) | (Hu & Hm & Hk & Hn)] H0; [lia|].
  split; [exact Hu|]. split; [exact Hm|]. split; [exact Hk | exact Hn].
Qed.

Lemma c1_nunb_of : forall bs k,
  LLVMFuzzerTestOneInput_case1.c1_su bs k (Boxreg.bx_n bs) (-1) ->
  reac_boxreg_add_c.add_none_unbound bs k.
Proof.
  intros bs k [(_ & N) | (H & _)]; [exact N | lia].
Qed.

(* The five shapes of `want` the case can reach (fuzz_boxreg.c:296-303), as Pau's c1_wantP. *)
Lemma c1_want_no : forall bs M k lf,
  ~ (reac_boxreg_add_c.add_width_ok k (Boxreg.bx_fabric bs) /\ M <> Boxreg.zero6) ->
  LLVMFuzzerTestOneInput_case1.c1_wantP bs M k lf (-1).
Proof. intros bs M k lf H. left. split; [exact H | reflexivity]. Qed.

Lemma c1_want_h : forall bs M k lf h,
  reac_boxreg_add_c.add_width_ok k (Boxreg.bx_fabric bs) -> M <> Boxreg.zero6 ->
  reac_boxreg_add_c.add_held bs M h ->
  LLVMFuzzerTestOneInput_case1.c1_wantP bs M k lf h.
Proof. intros bs M k lf h Ho Hz Hh. right; left. split; [exact Ho|]. split; [exact Hz | exact Hh]. Qed.

Lemma c1_want_u : forall bs M k lf u,
  reac_boxreg_add_c.add_width_ok k (Boxreg.bx_fabric bs) -> M <> Boxreg.zero6 ->
  reac_boxreg_add_c.add_none_held bs M -> reac_boxreg_add_c.add_unbound bs k u ->
  LLVMFuzzerTestOneInput_case1.c1_wantP bs M k lf u.
Proof.
  intros bs M k lf u Ho Hz Hn Hu. right; right; left.
  split; [exact Ho|]. split; [exact Hz|]. split; [exact Hn | exact Hu].
Qed.

Lemma c1_want_full : forall bs M k lf,
  reac_boxreg_add_c.add_width_ok k (Boxreg.bx_fabric bs) -> M <> Boxreg.zero6 ->
  reac_boxreg_add_c.add_none_held bs M -> reac_boxreg_add_c.add_none_unbound bs k ->
  (5 <= Boxreg.bx_n bs \/ lowest_free_c.lowest_free_res bs k (Boxreg.bx_fabric bs) (-1)) ->
  LLVMFuzzerTestOneInput_case1.c1_wantP bs M k lf (-1).
Proof.
  intros bs M k lf Ho Hz Hn Hu Hd. right; right; right; left.
  split; [exact Ho|]. split; [exact Hz|]. split; [exact Hn|]. split; [exact Hu|].
  split; [exact Hd | reflexivity].
Qed.

Lemma c1_want_new : forall bs M k lf,
  reac_boxreg_add_c.add_width_ok k (Boxreg.bx_fabric bs) -> M <> Boxreg.zero6 ->
  reac_boxreg_add_c.add_none_held bs M -> reac_boxreg_add_c.add_none_unbound bs k ->
  Boxreg.bx_n bs < 5 -> 0 <= lf -> lowest_free_c.lowest_free_res bs k (Boxreg.bx_fabric bs) lf ->
  LLVMFuzzerTestOneInput_case1.c1_wantP bs M k lf (Boxreg.bx_n bs).
Proof.
  intros bs M k lf Ho Hz Hn Hu Hlt Hl Hr. right; right; right; right.
  split; [exact Ho|]. split; [exact Hz|]. split; [exact Hn|]. split; [exact Hu|].
  split; [exact Hlt|]. split; [reflexivity|]. split; [exact Hl | exact Hr].
Qed.

(* The table after the call keeps the invariant and the fabric, and keeps what check_kept asks with ren = -1. *)
Lemma c1_after_add : forall bs M k z bs',
  Boxreg.boxreg_inv bs -> length M = 6%nat -> reac_boxreg_add_c.add_out bs M k z bs' ->
  Boxreg.boxreg_inv bs' /\ Boxreg.bx_fabric bs' = Boxreg.bx_fabric bs /\
  LLVMFuzzerTestOneInput_inv.llvm_kept bs bs' (-1) /\ -1 <= z <= 4.
Proof.
  intros bs M k z bs' HI HM HA.
  split; [exact (reac_boxreg_add_inv.reac_boxreg_add_keeps_inv_holds bs M bs' k z HI HM HA)|].
  split; [exact (LLVMFuzzerTestOneInput_case1.c1_add_fab bs M k z bs' HI HM HA)|].
  split; [exact (LLVMFuzzerTestOneInput_case1.c1_kept bs M k z bs' HI HM HA)
         | exact (LLVMFuzzerTestOneInput_case1.c1_add_range bs M k z bs' HI HA)].
Qed.

(* (-1) mod 2 ^ 32, the 32-bit value the case leaves in s5. *)
Lemma c1_ren_m1 : (-1) mod 2 ^ 32 = 2 ^ 32 - 1.
Proof. reflexivity. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg box_listing}.
#[local] Notation SEGS := (@pa_segs _ box_listing PI).
#[local] Notation VAL := (@pa_val _ box_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ box_listing PI).
#[local] Notation BASE := (@pa_val _ box_listing PI A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HISV : img_shadow_vis SEGS B.
Hypothesis HGLOB : globs_marked SEGS B BX_G.
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA BS___asan_memcpy).
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA BS___interceptor_trampoline_bcmp).
Hypothesis TFIND : ReacBoxregFind.treac_boxreg_find_spec B.
Hypothesis TADD : ReacBoxregAdd.treac_boxreg_add_spec B.
Hypothesis TLOWFREE : LowestFree.tlowest_free_spec B.

(* The two registered globals the case reads, as bytes of the read-only image: `ZERO` (A_OBJ 6, 0x20cc0, the six
   zero bytes the two bcmp calls of 0x806dc and 0x80750 compare against) and `read_mac.base` (A_OBJ 4, 0x20d00,
   the five bytes 00 40 ab 00 00 the __asan_memcpy of 0x803c4 copies into mac). `arodata_okP` of gb_base reads
   the image through the journal's view, but only at an address it knows is read-only, no owned static and no
   errno byte; `asn_rom_bytes` is that fact. HMRG is the margin every registered global has, which is what the
   wrappers' shadow hull asks of BoxRo.v's ro_read_ok_glob; the four margins the case uses follow from it. *)
Hypothesis HZERO : SnprintfDef.asn_rom_bytes SEGS B (VAL (A_OBJ 6))
  (map (fun b : byte => bv_unsigned b) Boxreg.zero6).
Hypothesis HRMB : SnprintfDef.asn_rom_bytes SEGS B (VAL (A_OBJ 4)) [0; 64; 171; 0; 0].
Hypothesis HMRG : Forall (fun g => IMG_LO + 64 <= fst g /\ fst g + snd g + 64 <= IMG_HI) BX_G.

Lemma c1_marg : forall a n, In (a, n) BX_G -> IMG_LO + 64 <= a /\ a + n + 64 <= IMG_HI.
Proof. intros a n Hin. rewrite Forall_forall in HMRG. exact (HMRG (a, n) Hin). Qed.

Lemma HZ1 : IMG_LO + 64 <= VAL (A_OBJ 6).
Proof. exact (proj1 (c1_marg _ 6 ltac:(unfold BX_G; cbn [In]; tauto))). Qed.
Lemma HZ2 : VAL (A_OBJ 6) + 6 + 64 <= IMG_HI.
Proof. exact (proj2 (c1_marg _ 6 ltac:(unfold BX_G; cbn [In]; tauto))). Qed.
Lemma HM1 : IMG_LO + 64 <= VAL (A_OBJ 4).
Proof. exact (proj1 (c1_marg _ 5 ltac:(unfold BX_G; cbn [In]; tauto))). Qed.
Lemma HM2 : VAL (A_OBJ 4) + 5 + 64 <= IMG_HI.
Proof. exact (proj2 (c1_marg _ 5 ltac:(unfold BX_G; cbn [In]; tauto))). Qed.

(* The allocator budget the turn may still spend grows with the turn number. *)
Lemma c1_acc_step : forall i acc, 0 <= i -> acc <= GB_A MT i -> acc <= GB_A MT (i + 1).
Proof.
  intros i acc Hi Hacc. unfold GB_A in *.
  pose proof (mo_malloc_nonneg MT MTL 48 ltac:(lia)) as H48.
  pose proof (mo_free_nonneg MT MTL) as Hfr.
  nia.
Qed.

(* ---- the landing: the facts the walk ends with, as the cut GI_K ---- *)
Lemma c1_fin_K : forall i cx fp k acc ly3 S3 W3 ms3 md3 r bs bs' pos,
  gb_body cx fp GP_K W3 ms3 GSH_it ->
  0 <= i < 64 -> k <= 3 + 2 * i -> acc <= GB_A MT (i + 1) ->
  gblk1 B cx ly3 S3 r -> greg B ly3 S3 W3 ms3 r bs' -> gprev cx fp W3 ms3 bs ->
  Boxreg.boxreg_inv bs -> Boxreg.boxreg_inv bs' ->
  Boxreg.bx_fabric bs' = Boxreg.bx_fabric bs ->
  LLVMFuzzerTestOneInput_inv.llvm_kept bs bs' (-1) ->
  getr (ms_regs ms3) 20 = w64 r -> getr (ms_regs ms3) 21 = w64 (2 ^ 32 - 1) ->
  getr (ms_regs ms3) 25 = w64 (Boxreg.bx_fabric bs) ->
  gslots_r cx fp W3 ms3 r (Boxreg.bx_fabric bs) -> gcursor cx W3 ms3 pos ->
  gslot cx W3 ms3 0x68 i ->
  GI_K B MT i cx fp k acc ly3 S3 W3 ms3 md3.
Proof.
  intros i cx fp k acc ly3 S3 W3 ms3 md3 r bs bs' pos
    HBD Hi Hk Hacc HBL HRG HPV HIb HIb' HFab HKept R20 R21 R25 HSR HCU H68.
  pose proof (LLVMFuzzerTestOneInput_case1.c1_inv_n bs HIb) as Hn.
  exists r, bs, bs', (-1), pos.
  split; [exact HBD|]. split; [exact Hi|]. split; [exact Hk|]. split; [exact Hacc|].
  split; [exact HBL|]. split; [exact HRG|]. split; [exact HPV|].
  split; [exact HIb|]. split; [exact HIb'|]. split; [exact HFab|].
  split; [exact HKept|]. split; [lia|].
  split; [exact R20|].
  split; [rewrite R21, c1_ren_m1; reflexivity|].
  split; [exact R25|]. split; [exact HSR|]. split; [exact HCU | exact H68].
Qed.

(* ---- the state at a cut inside the case ---- *)

(* The machine part: the pc and the registers every piece of the case keeps. *)
Definition c1_core (cx : bcx) (fp : Z) (pc : Z) (ms : machine_state) : Prop :=
  ms_pc_val ms = w64 (BASE + pc) /\ ms_resv ms = None /\ ms_svc_pending ms = None /\
  ms_rom ms = seg_rom SEGS /\ ms_fregs ms = fp_regs /\ ms_fcsr ms = fp_csr /\ gregs cx fp ms.

Lemma c1_core_mkst : forall cx fp pc ms,
  c1_core cx fp pc ms -> ms = mkst (ms_regs ms) (w64 (BASE + pc)) (ms_mem ms) (seg_rom SEGS).
Proof.
  intros cx fp pc ms (Hpc & Hrv & Hsv & Hro & Hfr & Hfc & _).
  destruct ms as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0].
  cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem] in *.
  subst. reflexivity.
Qed.

Lemma c1_core_of_body : forall cx fp pc W3 ms sh, gb_body cx fp pc W3 ms sh -> c1_core cx fp pc ms.
Proof.
  intros cx fp pc W3 ms sh (Hpc & Hrv & Hsv & Hro & Hfr & Hfc & Hgr & _).
  unfold c1_core. repeat (split; [assumption|]). exact Hgr.
Qed.

(* `uint8_t mac[6]`, the frame object at F + GO_MAC, and its six bytes. *)
Definition c1mac (cx : bcx) (fp : Z) (W3 : world SEGS) (ms : machine_state) (M : list byte) : Prop :=
  length M = 6%nat /\
  forall j, 0 <= j < 6 ->
    aview SEGS (w_H W3) (ms_mem ms) (gF cx fp + GO_MAC + j) =
    Some (bv_unsigned (nth (Z.to_nat j) M (Z_to_bv 8 0))).

(* The memory every piece of the case carries, over and above the spill slots it keeps in the engine's
   symbolic state: the machine frame's saved words, the frame's shadow and flag word, the caller's input,
   the frame slots that name the frame's objects, and the frame's copy `prev` of the table. *)
Definition c1mem (cx : bcx) (fp : Z) (W3 : world SEGS) (ms : machine_state) (bs : list byte) : Prop :=
  gsaved cx W3 ms /\ gshadow cx fp W3 ms GSH_it /\
  rdword (aview SEGS (w_H W3) (ms_mem ms)) (gF cx fp + fs_frame_bytes GB_CID - 8) = Some (gFL cx fp) /\
  garr8 SEGS (mrestrict (w_H W3) (ms_mem ms)) (c_p cx)
        (map (fun b : byte => bv_unsigned b) (c_pl cx)) /\
  gslots_fr cx fp W3 ms /\ gprev cx fp W3 ms bs.

(* What every cut of the case holds besides its own registers. *)
Definition c1_base (cx : bcx) (fp : Z) (k acc i : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms : machine_state) (r : Z) (bs : list byte) (pos : Z) : Prop :=
  0 <= i < 64 /\ k <= 1 + 2 * i /\ acc <= GB_A MT i /\
  gblk1 B cx ly3 S3 r /\ Boxreg.boxreg_inv bs /\
  c1mem cx fp W3 ms bs /\ gslots_r cx fp W3 ms r (Boxreg.bx_fabric bs) /\
  gcursor cx W3 ms pos /\ gslot cx W3 ms 0x68 i /\ gslot cx W3 ms 0x48 (Boxreg.bx_n bs) /\
  getr (ms_regs ms) 20 = w64 r.

(* ---- the three cuts inside the case ---- *)

(* 0x806cc: read_mac is done (mac holds M, s3 names it) and nch is in slot 0x58. The table has not moved,
   so the registry still holds the bytes prev holds. *)
Definition C1_nch (i : Z) (cx : bcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms : machine_state) (md : Model) : Prop :=
  exists r bs pos M nch,
  c1_core cx fp PC1_nch ms /\ c1_base cx fp k acc i ly3 S3 W3 ms r bs pos /\
  greg B ly3 S3 W3 ms r bs /\ c1mac cx fp W3 ms M /\
  0 <= nch < 256 /\ gslot cx W3 ms 0x58 nch /\
  getr (ms_regs ms) 19 = w64 (gF cx fp + GO_MAC) /\
  getr (ms_regs ms) 25 = w64 (Boxreg.bx_fabric bs).

(* 0x807a8: the scan of prev's rows is done. s11 is the `nonzero` flag (0 exactly for the zero MAC), s6 the
   first row whose MAC is the read one (-1 for none) and s10 the first unbound row of this width (-1 for
   none); slot 0x30 still holds the -1 the block at 0x806ec wrote. *)
Definition C1_dec (i : Z) (cx : bcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms : machine_state) (md : Model) : Prop :=
  exists r bs pos M nch h u v,
  c1_core cx fp PC1_dec ms /\ c1_base cx fp k acc i ly3 S3 W3 ms r bs pos /\
  greg B ly3 S3 W3 ms r bs /\ c1mac cx fp W3 ms M /\
  0 <= nch < 256 /\ gslot cx W3 ms 0x58 nch /\ gslot cx W3 ms 0x30 ((-1) mod 2 ^ 64) /\
  (v = 0 <-> M = Boxreg.zero6) /\ 0 <= v < 2 ^ 64 /\
  LLVMFuzzerTestOneInput_case1.c1_sh bs M v (Boxreg.bx_n bs) h /\
  LLVMFuzzerTestOneInput_case1.c1_su bs nch (Boxreg.bx_n bs) u /\
  -1 <= h <= 4 /\ -1 <= u <= 4 /\
  getr (ms_regs ms) 22 = w64 h /\ getr (ms_regs ms) 26 = w64 u /\ getr (ms_regs ms) 27 = w64 v.

(* 0x807e8: the index the contract asks for is in s6, the table's row count in s10 and the lowest free base
   (or -1) in slot 0x30. The two words the checks after the calls still read are kept as well, both of them
   registers the callees preserve: s11 (v), the `nonzero` flag the bcmp of 0x806dc left, and s5 (w5), whose low
   bit the block at 0x807a8 set to 1 exactly when the width is not a legal one (the checks at 0x80810 and
   0x8081c read them). *)
Definition C1_call (i : Z) (cx : bcx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms : machine_state) (md : Model) : Prop :=
  exists r bs pos M nch lf want v w5,
  c1_core cx fp PC1_call ms /\ c1_base cx fp k acc i ly3 S3 W3 ms r bs pos /\
  greg B ly3 S3 W3 ms r bs /\ c1mac cx fp W3 ms M /\
  0 <= nch < 256 /\ gslot cx W3 ms 0x58 nch /\ gslot cx W3 ms 0x30 (lf mod 2 ^ 64) /\ -1 <= lf <= 38 /\
  LLVMFuzzerTestOneInput_case1.c1_wantP bs M nch lf want /\ -1 <= want <= 4 /\
  getr (ms_regs ms) 22 = w64 want /\ getr (ms_regs ms) 26 = w64 (Boxreg.bx_n bs) /\
  getr (ms_regs ms) 25 = w64 (Boxreg.bx_fabric bs) /\
  (v = 0 <-> M = Boxreg.zero6) /\ 0 <= v < 2 ^ 64 /\ getr (ms_regs ms) 27 = w64 v /\
  0 <= w5 < 2 ^ 64 /\ getr (ms_regs ms) 21 = w64 w5 /\
  (Z.land w5 1 = 0 <-> reac_boxreg_add_c.add_width_ok nch (Boxreg.bx_fabric bs)).

(* ---- what a call that leaves the case's own memory alone keeps ---- *)

Section keep.
Variable cx : bcx.
Variable fp : Z.
Variable W3 : world SEGS.

Lemma c1mac_keep : forall rs ms ms' M,
  gb_keep cx fp W3 rs (ms_mem ms) (ms_mem ms') -> c1mac cx fp W3 ms M -> c1mac cx fp W3 ms' M.
Proof.
  intros rs ms ms' M Hk (HL & HB1). split; [exact HL|]. intros j Hj.
  rewrite (Hk (gF cx fp + GO_MAC + j)); [exact (HB1 j Hj)|].
  right; right; left. unfold GO_MAC. change (fs_frame_bytes GB_CID) with 512. lia.
Qed.

End keep.

(* ---- the case, from its four pieces ---- *)
Variable POST : bcx -> world SEGS -> config -> Prop.

Lemma c1_compose :
  (forall i, gb_from B MT POST (C1_nch i) -> gb_from B MT POST (GI_T B MT 1 i)) ->
  (forall i, gb_from B MT POST (C1_dec i) -> gb_from B MT POST (C1_nch i)) ->
  (forall i, gb_from B MT POST (C1_call i) -> gb_from B MT POST (C1_dec i)) ->
  (forall i, gb_from B MT POST (GI_K B MT i) -> gb_from B MT POST (C1_call i)) ->
  forall i, gb_from B MT POST (GI_K B MT i) -> gb_from B MT POST (GI_T B MT 1 i).
Proof.
  intros S1 S2 S3' S4 i HK. exact (S1 i (S2 i (S3' i (S4 i HK)))).
Qed.


End c.
End b.
End a.

(* ==== the piece 0x807a8 .. 0x807e8 (and the block 0x80cf0 .. 0x80d1c): the want of the add ==== *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg box_listing}.
#[local] Notation SEGS := (@pa_segs _ box_listing PI).
#[local] Notation VAL := (@pa_val _ box_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ box_listing PI).
#[local] Notation BASE := (@pa_val _ box_listing PI A_TEXT).
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HISV : img_shadow_vis SEGS B.
Hypothesis HGLOB : globs_marked SEGS B BX_G.
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA BS___asan_memcpy).
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA BS___interceptor_trampoline_bcmp).
Hypothesis TFIND : ReacBoxregFind.treac_boxreg_find_spec B.
Hypothesis TADD : ReacBoxregAdd.treac_boxreg_add_spec B.
Hypothesis TLOWFREE : LowestFree.tlowest_free_spec B.
Hypothesis HZERO : SnprintfDef.asn_rom_bytes SEGS B (VAL (A_OBJ 6))
  (map (fun b : byte => bv_unsigned b) Boxreg.zero6).
Hypothesis HRMB : SnprintfDef.asn_rom_bytes SEGS B (VAL (A_OBJ 4)) [0; 64; 171; 0; 0].
Hypothesis HMRG : Forall (fun g => IMG_LO + 64 <= fst g /\ fst g + snd g + 64 <= IMG_HI) BX_G.
Variable POST : bcx -> world SEGS -> config -> Prop.

(* ---- the decision at 0x807a8 .. 0x807c4, as words ---- *)

(* s5, the word the block builds at 0x807ac .. 0x807c0 from nch (k) and the fabric (f), as the engine computes it:
   ((f <s k) | k) | ((k - 41) <u 2 ^ 64 - 39). Its low bit is 1 exactly when the width is not a legal one. *)
Definition cw_s5 (k f : Z) : Z :=
  zalu64 ALU_OR (zalu64 ALU_OR (zalu64 ALU_SLT f k) k) (zalu64 ALU_SLTU (k + -41) (-39)).

Lemma cw_s5_grid : forall k f, 0 <= k < 256 -> 1 <= f <= 40 ->
  Z.land (cw_s5 k f) 1 = Z.b2z (negb (LLVMFuzzerTestOneInput_case1.c1_okb k f)).
Proof.
  intros k f Hk Hf.
  assert (H : forallb (fun k => forallb (fun f => Z.land (cw_s5 k f) 1 =?
                Z.b2z (negb (LLVMFuzzerTestOneInput_case1.c1_okb k f))) (map Z.of_nat (seq 1 40)))
                (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H.
  assert (Ik : In k (map Z.of_nat (seq 0 256))).
  { replace k with (Z.of_nat (Z.to_nat k)) by lia. apply in_map. apply in_seq. lia. }
  specialize (H k Ik). rewrite forallb_forall in H. apply Z.eqb_eq. apply H.
  replace f with (Z.of_nat (Z.to_nat f)) by lia. apply in_map. apply in_seq. lia.
Qed.

Lemma cw_s5_iff : forall k f, 0 <= k < 256 -> 1 <= f <= 40 ->
  (Z.land (cw_s5 k f) 1 = 0 <-> reac_boxreg_add_c.add_width_ok k f).
Proof.
  intros k f Hk Hf. rewrite cw_s5_grid by assumption. rewrite <- LLVMFuzzerTestOneInput_case1.c1_okb_spec.
  destruct (LLVMFuzzerTestOneInput_case1.c1_okb k f); cbn; split; intros H; congruence.
Qed.

Lemma cw_s5_range : forall k f, 0 <= cw_s5 k f < 2 ^ 64.
Proof. intros k f. unfold cw_s5, zalu64. apply zcanon_range. Qed.

Lemma cw_land1 : forall x, 0 <= Z.land x 1 <= 1.
Proof. intros x. apply Z_land_upper. lia. Qed.

(* s6 after the call of lowest_free: (lf >>s 63) | n_before (0x80d14 .. 0x80d18). *)
Lemma cw_or_grid : forall z n, -1 <= z <= 38 -> 0 <= n <= 4 ->
  zalu64 ALU_OR (zalu64 ALU_SRA z 63) n = zcanon (if z <? 0 then -1 else n).
Proof.
  intros z n Hz Hn.
  assert (H : forallb (fun z => forallb (fun n => zalu64 ALU_OR (zalu64 ALU_SRA z 63) n =?
                zcanon (if z <? 0 then -1 else n)) (map Z.of_nat (seq 0 5)))
                (map (fun x => Z.of_nat x - 1) (seq 0 40)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H.
  assert (Iz : In z (map (fun x => Z.of_nat x - 1) (seq 0 40))).
  { replace z with (Z.of_nat (Z.to_nat (z + 1)) - 1) by lia. apply (in_map (fun x => Z.of_nat x - 1)).
    apply in_seq. lia. }
  specialize (H z Iz). rewrite forallb_forall in H. apply Z.eqb_eq. apply H.
  replace n with (Z.of_nat (Z.to_nat n)) by lia. apply in_map. apply in_seq. lia.
Qed.

(* ---- the five branches of the piece, on words ---- *)
Lemma cw_bne0 : forall x, 0 <= x < 2 ^ 64 ->
  branch_taken BC_NE (Z_to_bv 64 x) (Z_to_bv 64 0) = negb (x =? 0).
Proof.
  intros x Hx.
  pose proof (branch_ne_U (mkEnv (fun _ => Z_to_bv 64 0) (fun _ => [])) (SLit x) (SLit 0)) as H.
  cbn [sv_denot] in H. rewrite H, !U_SLit, (zcanon_id x ltac:(unfold M64; lia)). reflexivity.
Qed.

Lemma cw_beq0 : forall x, 0 <= x < 2 ^ 64 ->
  branch_taken BC_EQ (Z_to_bv 64 x) (Z_to_bv 64 0) = (x =? 0).
Proof.
  intros x Hx.
  pose proof (branch_eq_U (mkEnv (fun _ => Z_to_bv 64 0) (fun _ => [])) (SLit x) (SLit 0)) as H.
  cbn [sv_denot] in H. rewrite H, !U_SLit, (zcanon_id x ltac:(unfold M64; lia)). reflexivity.
Qed.

Lemma cw_bge0 : forall x, -1 <= x <= 4 ->
  branch_taken BC_GE (Z_to_bv 64 x) (Z_to_bv 64 0) = (0 <=? x).
Proof.
  intros x Hx. assert (Hc : x = -1 \/ x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4) by lia.
  repeat (destruct Hc as [Hc|Hc]; [subst x; vm_compute; reflexivity|]). subst x. vm_compute. reflexivity.
Qed.

Lemma cw_blt0 : forall x, -1 <= x <= 4 ->
  branch_taken BC_LT (Z_to_bv 64 x) (Z_to_bv 64 0) = (x <? 0).
Proof.
  intros x Hx. assert (Hc : x = -1 \/ x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4) by lia.
  repeat (destruct Hc as [Hc|Hc]; [subst x; vm_compute; reflexivity|]). subst x. vm_compute. reflexivity.
Qed.

Lemma cw_blt4 : forall x, 0 <= x <= 5 ->
  branch_taken BC_LT (Z_to_bv 64 4) (Z_to_bv 64 x) = (4 <? x).
Proof.
  intros x Hx. assert (Hc : x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4 \/ x = 5) by lia.
  repeat (destruct Hc as [Hc|Hc]; [subst x; vm_compute; reflexivity|]). subst x. vm_compute. reflexivity.
Qed.

(* ---- the symbolic words the engine leaves, as values ---- *)
Lemma cw_denot_off0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.

(* s5 over the atoms 32 (nch) and 33 (the fabric). *)
Local Notation CW_S5 := (SAlu ALU_OR (SAlu ALU_OR (SAlu ALU_SLT (SOff 33 0) (SOff 32 0)) (SOff 32 0))
  (SAlu ALU_SLTU (SOff 32 (-41)) (SLit (-39)))).

Lemma cw_s5_denot : forall E k f, ew E 32 = Z_to_bv 64 k -> ew E 33 = Z_to_bv 64 f ->
  0 <= k < 2 ^ 64 -> 0 <= f < 2 ^ 64 -> sv_denot E CW_S5 = Z_to_bv 64 (cw_s5 k f).
Proof.
  intros E k f H32 H33 Hk Hf. cbn [sv_denot]. rewrite H32, H33.
  rewrite !(unsigned_lit_small k Hk), !(unsigned_lit_small f Hf), !Z.add_0_r, !zalu64_sound. reflexivity.
Qed.

Lemma cw_a0_denot : forall E k f, ew E 32 = Z_to_bv 64 k -> ew E 33 = Z_to_bv 64 f ->
  0 <= k < 2 ^ 64 -> 0 <= f < 2 ^ 64 ->
  sv_denot E (SAlu ALU_AND CW_S5 (SLit 1)) = Z_to_bv 64 (Z.land (cw_s5 k f) 1).
Proof.
  intros E k f H32 H33 Hk Hf.
  change (sv_denot E (SAlu ALU_AND CW_S5 (SLit 1))) with (alu64 ALU_AND (sv_denot E CW_S5) (Z_to_bv 64 1)).
  rewrite (cw_s5_denot E k f H32 H33 Hk Hf), zalu64_sound. unfold zalu64. rewrite Z_to_bv64_canon.
  cbn [zalu_raw]. rewrite (zcanon_id (cw_s5 k f)) by (pose proof (cw_s5_range k f); unfold M64; lia). reflexivity.
Qed.

Lemma cw_or_denot : forall E z n, ew E 10 = Z_to_bv 64 z -> ew E 26 = Z_to_bv 64 n ->
  -1 <= z <= 38 -> 0 <= n <= 4 ->
  sv_denot E (SAlu ALU_OR (SAlu ALU_SRA (SOff 10 0) (SLit 63)) (SOff 26 0)) =
  Z_to_bv 64 (if z <? 0 then -1 else n).
Proof.
  intros E z n H10 H26 Hz Hn.
  change (sv_denot E (SAlu ALU_OR (SAlu ALU_SRA (SOff 10 0) (SLit 63)) (SOff 26 0))) with
    (alu64 ALU_OR (alu64 ALU_SRA (sv_denot E (SOff 10 0)) (Z_to_bv 64 63)) (sv_denot E (SOff 26 0))).
  rewrite !cw_denot_off0, H10, H26, !zalu64_sound, (cw_or_grid z n Hz Hn). apply Z_to_bv64_canon.
Qed.

(* ---- small tactics ---- *)
Local Ltac cw_zbool :=
  repeat match goal with
  | H : negb _ = true |- _ => apply (proj1 (Bool.negb_true_iff _)) in H
  | H : negb _ = false |- _ => apply (proj1 (Bool.negb_false_iff _)) in H
  | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
  | H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
  | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
  | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
  | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
  | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
  end.

(* A register of the engine's state, as the denotation of the symbolic word it holds. *)
Local Ltac cwreg HS r R :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?Ex ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_pi_restrict_reg H Ex ss ms r HS) as R;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in R; cbn [ms_regs] in R
  | st_ok ?segs ?Ex ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_restrict_reg segs H Ex ss ms r HS) as R;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in R; cbn [ms_regs] in R
  end.

(* A run whose regions write nothing leaves the memory as it was, byte for byte. *)
Local Ltac cw_upd :=
  repeat match goal with H : frame_of _ _ (mrestrict _ _) _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  lazymatch goal with HF : frame_of ?Ex ?rs (ms_mem ?mp) (ms_mem ?mn), HM : forall x, ms_mem ?mp x = ms_mem ?m0 x |- _ =>
    let HM' := fresh "HM" in
    assert (HM' : forall x, ms_mem mn x = ms_mem m0 x) by
      (intros x; transitivity (ms_mem mp x); [|exact (HM x)]; apply HF;
       let rs' := eval vm_compute in rs in change rs with rs';
       intros (rr & Hr & Hb);
       repeat (destruct Hr as [Hr | Hr]; [subst rr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hb; lia |]);
       destruct Hr);
    clear HM HF; rename HM' into HM end.

Local Ltac cw_cs := unfold acallee_saved;
  repeat match goal with |- context [bv_unsigned ?x] =>
    let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia.

(* The registers every exit keeps from the entry of the piece (s1, s0, sp, gp, tp, s2, s4, s8, s11). *)
Definition cw_csl : list (bv 5) := [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 24%bv; 27%bv].
Definition cw_csl2 : list (bv 5) := [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 20%bv; 21%bv; 24%bv; 25%bv; 26%bv; 27%bv].
Local Ltac cw_in := cbn [cw_csl cw_csl2 In]; repeat (first [left; reflexivity | right]).

Local Ltac cw_rv :=
  first [ rewrite cw_denot_off0; assumption
        | cbn [sv_denot]; unfold w64; apply bv_eq; vm_compute; reflexivity ].

(* ---- the memory the piece keeps ---- *)

(* The bytes a phase's facts speak about (BoxLxSeat.v gb_keep_at, with the registry r), except the spill slot 0x30
   that the store at 0x80d10 writes. *)
Definition cw_kept (cx : bcx) (fp r : Z) (W3 : world SEGS) (m m' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> gb_keep_at cx fp [(r, REG_SIZE)] a ->
    ~ (c_sp1 cx + 0x30 <= a < c_sp1 cx + 0x38) -> aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a.

Lemma cw_aview_pw : forall (H : word -> bool) (m m' : word -> option byte) a,
  (forall x, m' x = m x) -> aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' a Hm. unfold aview, YP09.mbyte, mrestrict. rewrite Hm. reflexivity. Qed.

Lemma cw_kept_pw : forall cx fp r W3 (m m' : word -> option byte),
  (forall x, m' x = m x) -> cw_kept cx fp r W3 m m'.
Proof. intros cx fp r W3 m m' Hm a _ _ _. apply cw_aview_pw. exact Hm. Qed.

Lemma cw_keep_outside : forall E rs (m m' : word -> option byte) (H : word -> bool) a,
  frame_of E rs m m' -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a -> aview SEGS H m' a = aview SEGS H m a.
Proof.
  intros E rs m m' H a HF Ha Hn. unfold aview, YP09.mbyte, mrestrict.
  rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. exact Hn.
Qed.

(* A word the engine holds in a window of the machine frame at s1 (atom 9). *)
Lemma cw_slot_reg : forall E ss ms (W : world SEGS) i lo hi wlo whi cs od e v sp1,
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
  nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some 9%nat) lo hi wlo whi cs) ->
  bv_unsigned (ew E 9) = sp1 ->
  In (YP09.mkChunk od (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview SEGS (w_H W) (ms_mem ms)) (sp1 + od) = Some v.
Proof.
  intros E ss ms W i lo hi wlo whi cs od e v sp1 HS Hi Hb Hin He Hv.
  apply (rdword_of_val_mem SEGS (w_H W) (ms_mem ms)); [|exact Hv].
  pose proof (st_ok_pi_region_nth E ss (restrict (w_H W) ms) i _ HS Hi) as Hr.
  exact (YC4b.field_of_region E _ 9%nat sp1 cs lo hi wlo whi od 8%N e v Hr Hb Hin He
    ltac:(cbn [Z.of_N]; change (8 * 8) with 64; exact Hv) ltac:(cbn [Z.of_N]; lia)).
Qed.

Lemma cw_sub_mod16 : forall a b, a mod 32 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof.
  intros a b Ha Hb. apply Z.mod_divide in Ha; [|lia]. apply Z.mod_divide in Hb; [|lia]. apply Z.mod_divide; [lia|].
  destruct Ha as [x Hx]. destruct Hb as [y Hy]. exists (2 * x - y). lia.
Qed.

(* The callee chain at the realigned machine stack pointer (BoxLxSeat.v gb_achain), through the phase's layout. *)
Lemma cw_achain : forall cx ly3 S3 W3 mem md own k sp',
  gb_base B MT cx ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    own ly3 S3 W3 mem md k ->
  rdword (aview SEGS (w_H W3) mem) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) ->
  rdword (aview SEGS (w_H W3) mem) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)) ->
  sp' + 16 <= spZ (c_regs cx) ->
  achain ly3 (aview SEGS (w_H W3) mem) sp' (spZ (c_regs cx)) (gch cx).
Proof.
  intros cx ly3 S3 W3 mem md own k sp' HB HJ H8 H16 Hsp.
  pose proof HB as (HPRE & _). pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & _).
  pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
  pose proof asan_consts as (C1 & _).
  apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ Etop).
  eapply gb_achain; first [ exact HB | exact H8 | exact H16 | exact Hsp | (intros a Ha; apply F1; unfold GB_STK in *; lia) ].
Qed.

(* Every fact of the cut the piece keeps, across a memory that keeps the bytes cw_kept names. *)
Lemma cw_keep_all : forall i cx fp k acc ly3 S3 W3 md (ms ms' : machine_state) r bs pos M nch,
  gb_base B MT cx ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly3 S3 W3 (ms_mem ms) md k ->
  frames S3 = [(GB_CID, fp)] ->
  cw_kept cx fp r W3 (ms_mem ms) (ms_mem ms') ->
  getr (ms_regs ms') 20 = getr (ms_regs ms) 20 ->
  c1_base B MT cx fp k acc i ly3 S3 W3 ms r bs pos -> greg B ly3 S3 W3 ms r bs -> c1mac cx fp W3 ms M ->
  gslot cx W3 ms 0x58 nch ->
  c1_base B MT cx fp k acc i ly3 S3 W3 ms' r bs pos /\ greg B ly3 S3 W3 ms' r bs /\ c1mac cx fp W3 ms' M /\
  gslot cx W3 ms' 0x58 nch.
Proof.
  intros i cx fp k acc ly3 S3 W3 md ms ms' r bs pos M nch HB HJ HFR HK R20' HBASE HREG HMAC S58.
  destruct HBASE as (Hi & Hk & Hacc & HBL & HIb & HMEM & HSR & HCU & H68 & H48 & R20).
  destruct HMEM as ((Sra & Ssv) & HSH & HFL & HIN & HFRS & HPV).
  pose proof (gb_sp_facts B MT cx HB) as (Hal16 & Hlo & Hhi & Hsp1).
  pose proof (gb_F_facts B MT LAWS cx fp W3 ms ly3 S3 md k HB HJ HFR) as (HF0 & HFc & _ & _ & HSHeq).
  pose proof asan_consts as (C1 & _).
  pose proof HJ as (HAR & _).
  pose proof HREG as (Hrin & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ r REG_SIZE HAR Hrin) as (_ & Hr4096 & Hrceil & _).
  change (req_size REG_SIZE) with 288 in Hrceil.
  assert (Hinlo : c_n cx = 0 \/ (0 <= c_p cx /\ c_p cx + c_n cx <= alloc_ceiling)).
  { pose proof HB as (_ & _ & _ & Hpn & _).
    destruct Hpn as [(Hn0 & _) | (Hn & Hin)]; [left; exact Hn0 | right].
    assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3))
      by (unfold gblk1 in HBL; rewrite HBL; apply in_or_app; left; exact Hin).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin3) as (_ & Hp4096 & Hpceil & _).
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq]. lia. }
  assert (Hsh : 0 <= gSH cx fp /\ gSH cx fp + 64 <= alloc_ceiling).
  { rewrite HSHeq. unfold SHADOW_OFF.
    pose proof (Z.div_lt_upper_bound (gF cx fp) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
    pose proof (Z.div_pos (gF cx fp) 8 ltac:(lia) ltac:(lia)). lia. }
  assert (Hfb : fs_frame_bytes GB_CID = 512) by (vm_compute; reflexivity).
  assert (AV : forall a, 0 <= a < 2 ^ 64 -> gb_keep_at cx fp [(r, REG_SIZE)] a ->
      a < c_sp1 cx + 0x30 \/ c_sp1 cx + 0x38 <= a ->
      aview SEGS (w_H W3) (ms_mem ms') a = aview SEGS (w_H W3) (ms_mem ms) a)
    by (intros a Ha Hk1 Hn; apply HK; [exact Ha | exact Hk1 | lia]).
  assert (RK : forall a v, rdword (aview SEGS (w_H W3) (ms_mem ms)) a = Some v ->
      (forall j, 0 <= j < 8 -> 0 <= a + j < 2 ^ 64 /\ gb_keep_at cx fp [(r, REG_SIZE)] (a + j) /\
         (a + j < c_sp1 cx + 0x30 \/ c_sp1 cx + 0x38 <= a + j)) ->
      rdword (aview SEGS (w_H W3) (ms_mem ms')) a = Some v).
  { intros a v Hv Hj. rewrite <- Hv. apply rdword_ext. intros j Hj8.
    destruct (Hj j Hj8) as (H1 & H2 & H3). exact (AV (a + j) H1 H2 H3). }
  assert (SL : forall off v, 0 <= off <= 0x90 -> (off + 8 <= 0x30 \/ 0x38 <= off) ->
      gslot cx W3 ms off v -> gslot cx W3 ms' off v).
  { intros off v H1 H2 Hv. unfold gslot in *. apply RK; [exact Hv|].
    intros j Hj. split; [lia|]. split; [unfold gb_keep_at; left; lia | lia]. }
  split; [|split; [|split]].
  - unfold c1_base, c1mem.
    split; [exact Hi|]. split; [exact Hk|]. split; [exact Hacc|]. split; [exact HBL|]. split; [exact HIb|].
    split.
    { split.
      { split.
        - apply RK; [exact Sra|]. intros j Hj. split; [lia|]. split; [unfold gb_keep_at; left; lia | lia].
        - intros j Hj. apply RK; [exact (Ssv j Hj)|]. intros jj Hjj. split; [lia|].
          split; [unfold gb_keep_at; left; lia | lia]. }
      split.
      { intros j Hj. assert (Hl : length GSH_it = 52%nat) by reflexivity.
        assert (Hj52 : (j < 52)%nat) by (rewrite <- Hl; exact Hj).
        rewrite AV; [exact (HSH j Hj) | lia | | lia].
        unfold gb_keep_at. right; right; right; left. rewrite Hfb. change (512 / 8) with 64. lia. }
      split.
      { apply RK; [exact HFL|]. intros j Hj. rewrite Hfb. split; [lia|].
        split; [unfold gb_keep_at; right; right; left; rewrite Hfb; lia | lia]. }
      split.
      { apply (garr8_frame SEGS _ _ _ _ HIN). intros a Ha. apply (mbyte_of_aview SEGS).
        rewrite length_map in Ha. unfold c_n in Hinlo.
        apply AV; [destruct Hinlo; lia | unfold gb_keep_at; right; left; unfold c_n; lia | destruct Hinlo; lia]. }
      split.
      { destruct HFRS as (F18 & F28 & F70 & F78 & F80).
        split; [apply SL; [lia | lia | exact F18]|]. split; [apply SL; [lia | lia | exact F28]|].
        split; [apply SL; [lia | lia | exact F70]|]. split; [apply SL; [lia | lia | exact F78]|].
        apply SL; [lia | lia | exact F80]. }
      { intros j Hj. unfold REG_SIZE in Hj.
        rewrite AV; [exact (HPV j ltac:(unfold REG_SIZE; lia)) | unfold GO_PREV; lia
        | unfold gb_keep_at; right; right; left; rewrite Hfb; unfold GO_PREV; lia
        | unfold GO_PREV; lia]. } }
    split.
    { destruct HSR as (S10 & S20 & S38 & S40 & S50 & S60).
      split; [apply SL; [lia | lia | exact S10]|]. split; [apply SL; [lia | lia | exact S20]|].
      split; [apply SL; [lia | lia | exact S38]|]. split; [apply SL; [lia | lia | exact S40]|].
      split; [apply SL; [lia | lia | exact S50]|]. apply SL; [lia | lia | exact S60]. }
    split.
    { destruct HCU as (Hp & C88 & C90). split; [exact Hp|].
      split; [apply SL; [lia | lia | exact C88] | apply SL; [lia | lia | exact C90]]. }
    split; [apply SL; [lia | lia | exact H68]|].
    split; [apply SL; [lia | lia | exact H48]|].
    rewrite R20'. exact R20.
  - destruct HREG as (Hb & Hl & Hbytes). split; [exact Hb|]. split; [exact Hl|].
    intros j Hj. unfold REG_SIZE in Hj.
    rewrite AV; [exact (Hbytes j ltac:(unfold REG_SIZE; lia)) | lia
      | unfold gb_keep_at; right; right; right; right; apply Exists_exists; exists (r, REG_SIZE);
        split; [left; reflexivity | cbn [fst snd]; unfold REG_SIZE; lia]
      | lia].
  - destruct HMAC as (HL & HB1). split; [exact HL|]. intros j Hj.
    rewrite AV; [exact (HB1 j Hj) | unfold GO_MAC; lia
      | unfold gb_keep_at; right; right; left; rewrite Hfb; unfold GO_MAC; lia | unfold GO_MAC; lia].
  - apply SL; [lia | lia | exact S58].
Qed.

(* ---- the landing: the facts every exit of the piece ends with, as the cut C1_call ---- *)
Lemma cw_land : forall i cx fp k acc ly3 S3 W3 md (ms : machine_state) (regs' : bvmap 5 word) mem' md'
    r bs pos M nch lf want v,
  gb_from B MT POST (C1_call B MT i) -> gb_base B MT cx ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly3 S3 W3 (ms_mem ms) md k ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly3 S3 W3 mem' md' k ->
  frames S3 = [(GB_CID, fp)] -> mo_le MT (c_S cx) S3 acc ->
  c1_core cx fp PC1_dec ms ->
  (forall rr, In rr cw_csl -> getr regs' rr = getr (ms_regs ms) rr) ->
  cw_kept cx fp r W3 (ms_mem ms) mem' ->
  c1_base B MT cx fp k acc i ly3 S3 W3 ms r bs pos -> greg B ly3 S3 W3 ms r bs -> c1mac cx fp W3 ms M ->
  0 <= nch < 256 -> gslot cx W3 ms 0x58 nch ->
  rdword (aview SEGS (w_H W3) mem') (c_sp1 cx + 0x30) = Some (lf mod 2 ^ 64) -> -1 <= lf <= 38 ->
  LLVMFuzzerTestOneInput_case1.c1_wantP bs M nch lf want -> -1 <= want <= 4 ->
  getr regs' 22 = w64 want -> getr regs' 26 = w64 (Boxreg.bx_n bs) ->
  getr regs' 25 = w64 (Boxreg.bx_fabric bs) ->
  (v = 0 <-> M = Boxreg.zero6) -> 0 <= v < 2 ^ 64 -> getr (ms_regs ms) 27 = w64 v ->
  getr regs' 21 = w64 (cw_s5 nch (Boxreg.bx_fabric bs)) ->
  SRr SEGS W3 (mkCfg (mkst regs' (Z_to_bv 64 (BASE + PC1_call)) mem' (seg_rom SEGS)) md') (POST cx).
Proof.
  intros i cx fp k acc ly3 S3 W3 md ms regs' mem' md' r bs pos M nch lf want v
    HK HB HJ HJ' HFR HMO HCO KP HKP HBASE HREG HMAC Hnch S58 S30 Hlf HW Hwant R22 R26 R25 Hv Hvr R27 R21.
  pose proof HCO as (_ & _ & _ & _ & _ & _ & (G2 & G8 & G9 & G3 & G4 & G18 & G24)).
  pose proof HBASE as (_ & _ & _ & _ & HIb & _).
  pose proof (LLVMFuzzerTestOneInput_case1.c1_inv_fab bs HIb) as Hfab.
  destruct (cw_keep_all i cx fp k acc ly3 S3 W3 md ms (mkst regs' (Z_to_bv 64 (BASE + PC1_call)) mem' (seg_rom SEGS))
    r bs pos M nch HB HJ HFR HKP ltac:(cbn [ms_regs mkst]; apply KP; cw_in) HBASE HREG HMAC S58)
    as (HB' & HREG' & HMAC' & S58').
  apply (HK cx fp k acc ly3 S3 W3 (mkst regs' (Z_to_bv 64 (BASE + PC1_call)) mem' (seg_rom SEGS)) md' HB HJ' HFR HMO).
  exists r, bs, pos, M, nch, lf, want, v, (cw_s5 nch (Boxreg.bx_fabric bs)).
  split.
  { unfold c1_core. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    unfold gregs. cbn [ms_regs mkst].
    split; [rewrite KP by cw_in; exact G2|]. split; [rewrite KP by cw_in; exact G8|].
    split; [rewrite KP by cw_in; exact G9|]. split; [rewrite KP by cw_in; exact G3|].
    split; [rewrite KP by cw_in; exact G4|]. split; [rewrite KP by cw_in; exact G18|].
    rewrite KP by cw_in; exact G24. }
  split; [exact HB'|]. split; [exact HREG'|]. split; [exact HMAC'|].
  split; [exact Hnch|]. split; [exact S58'|]. split; [exact S30|]. split; [exact Hlf|].
  split; [exact HW|]. split; [exact Hwant|].
  split; [exact R22|]. split; [exact R26|]. split; [exact R25|].
  split; [exact Hv|]. split; [exact Hvr|].
  split; [cbn [ms_regs mkst]; rewrite KP by cw_in; exact R27|].
  split; [apply cw_s5_range|]. split; [exact R21|].
  apply cw_s5_iff; [exact Hnch | exact Hfab].
Qed.

(* ---- the engine's states ---- *)
Definition cw_SB : Z := 0x7fff8000.
Definition cw_Bspan : Z * Z := (cw_SB, cw_SB + 2 ^ 44 - 1).
(* At 0x807a8: the four spill slots the block reads, read-only: n_before (0x48), the fabric (0x50), nch (0x58)
   and &prev (0x78), as the atoms 34, 33, 32 and 35 of the environment. No region has a write window, so every run
   up to the call keeps the memory byte for byte. *)
Definition cw_R0 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x48 0x80 0 0
    [YP09.mkChunk 0x48 (CVal 8 (SOff 34 0)); YP09.mkChunk 0x50 (CVal 8 (SOff 33 0));
     YP09.mkChunk 0x58 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x78 (CVal 8 (SOff 35 0))].
Definition cw_ss0 : sstate := mkSS PC1_dec sr_atoms [cw_R0] None (mkFacts [] [] []).
(* At 0x80d10, after lowest_free: the slot 0x30 the store writes, over s1 (atom 9, a word of the stack above
   the shadow band). *)
Definition cw_R30 : YP09.region := YP09.mkRegion (Some 9%nat) 0x30 0x38 0x30 0x38 [].
Definition cw_ssC : sstate :=
  mkSS 0xdc4 sr_atoms [cw_R30] None (mkFacts [(9%nat, mkAF 0x7fff7f000000 (2 ^ 47) 5)] [] []).


(* A path that ends at 0x807e8 without the call: the engine's state there, the memory kept byte for byte, and the
   registers the state names, as the cut C1_call. *)
Lemma cw_fin0 : forall i cx fp k acc ly3 S3 W3 md (ms : machine_state) md' (msF : machine_state) r bs pos M nch
    want v E ss (extra : list word),
  gb_from B MT POST (C1_call B MT i) -> gb_base B MT cx ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly3 S3 W3 (ms_mem ms) md k ->
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly3 S3 W3 (ms_mem msF) md' k ->
  frames S3 = [(GB_CID, fp)] -> mo_le MT (c_S cx) S3 acc -> c1_core cx fp PC1_dec ms ->
  st_ok_pi SEGS VAL E ss (restrict (w_H W3) msF) -> env_agree 32 (Ereg (ms_regs ms) extra) E ->
  ss_pc ss = PC1_call -> ss_resv ss = None ->
  forallb (fun r0 : bv 5 => sv_eqb (sr_get (ss_regs ss) r0) (SOff (Z.to_nat (bv_unsigned r0)) 0)) cw_csl = true ->
  (forall x, ms_mem msF x = ms_mem ms x) ->
  c1_base B MT cx fp k acc i ly3 S3 W3 ms r bs pos -> greg B ly3 S3 W3 ms r bs -> c1mac cx fp W3 ms M ->
  0 <= nch < 256 -> gslot cx W3 ms 0x58 nch -> gslot cx W3 ms 0x30 ((-1) mod 2 ^ 64) ->
  LLVMFuzzerTestOneInput_case1.c1_wantP bs M nch (-1) want -> -1 <= want <= 4 ->
  sv_denot E (sr_get (ss_regs ss) 22) = w64 want ->
  sv_denot E (sr_get (ss_regs ss) 26) = w64 (Boxreg.bx_n bs) ->
  sv_denot E (sr_get (ss_regs ss) 25) = w64 (Boxreg.bx_fabric bs) ->
  (v = 0 <-> M = Boxreg.zero6) -> 0 <= v < 2 ^ 64 -> getr (ms_regs ms) 27 = w64 v ->
  sv_denot E (sr_get (ss_regs ss) 21) = w64 (cw_s5 nch (Boxreg.bx_fabric bs)) ->
  SRr SEGS W3 (mkCfg msF md') (POST cx).
Proof.
  intros i cx fp k acc ly3 S3 W3 md ms md' msF r bs pos M nch want v E ss extra
    HK HB HJ HJ' HFR HMO HCO HS HAE Hpc Hrv Hcs HM HBASE HREG HMAC Hnch S58 S30 HW Hwant D22 D26 D25 Hv Hvr R27 D21.
  pose proof (st_ok_pi_restrict_reg (w_H W3) E ss msF 22%bv HS) as Q22.
  pose proof (st_ok_pi_restrict_reg (w_H W3) E ss msF 26%bv HS) as Q26.
  pose proof (st_ok_pi_restrict_reg (w_H W3) E ss msF 25%bv HS) as Q25.
  pose proof (st_ok_pi_restrict_reg (w_H W3) E ss msF 21%bv HS) as Q21.
  pose proof (regs_kept_of_st_ok_pi E ss (restrict (w_H W3) msF) (ms_regs ms) extra cw_csl HS HAE Hcs) as KP.
  rewrite (st_ok_pi_restrict_mkst (w_H W3) E ss msF HS Hrv), Hpc.
  apply (cw_land i cx fp k acc ly3 S3 W3 md ms (ms_regs msF) (ms_mem msF) md' r bs pos M nch (-1) want v
    HK HB HJ HJ' HFR HMO HCO KP (cw_kept_pw cx fp r W3 (ms_mem ms) (ms_mem msF) HM) HBASE HREG HMAC Hnch S58).
  - unfold gslot in S30. rewrite <- S30. apply rdword_ext. intros jj Hjj. apply cw_aview_pw. exact HM.
  - lia.
  - exact HW.
  - exact Hwant.
  - rewrite Q22. exact D22.
  - rewrite Q26. exact D26.
  - rewrite Q25. exact D25.
  - exact Hv.
  - exact Hvr.
  - exact R27.
  - rewrite Q21. exact D21.
Qed.

(* A register value goal of cw_fin0, on the engine's own symbolic word. *)
Local Ltac cwv :=
  lazymatch goal with |- sv_denot ?Ex (sr_get (ss_regs ?ss) ?r) = _ =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e end;
  first [ rewrite cw_denot_off0; assumption | assumption
        | cbn [sv_denot]; unfold w64; apply bv_eq; vm_compute; reflexivity ].

Theorem c1_seg_want : forall i, gb_from B MT POST (C1_call B MT i) -> gb_from B MT POST (C1_dec B MT i).
Proof.
  intros i HK cx fp k acc ly3 S3 W3 ms md HB HJ HFR HMO HI.
  destruct HI as (r & bs & pos & M & nch & h & u & v & HCO & HBASE & HREG & HMAC & Hnch & S58 & S30 & Hv & Hvr &
    HSH & HSU & Hh & Hu & R22 & R26 & R27).
  pose proof HBASE as (Hi & Hk & Hacc & HBL & HIb & HMEM & HSR & HCU & H68 & H48 & R20).
  pose proof HMEM as (HSV & HSHD & HFL & HIN & HFRS & HPV).
  pose proof HFRS as (F18 & F28 & F70 & F78 & F80).
  pose proof HSR as (S10 & S20 & S38 & S40 & S50 & S60).
  pose proof HCO as (Hpc & Hrv & Hsv & Hro & Hfr & Hfc & (G2 & G8 & G9 & G3 & G4 & G18 & G24)).
  pose proof (LLVMFuzzerTestOneInput_case1.c1_inv_fab bs HIb) as Hfab.
  pose proof (LLVMFuzzerTestOneInput_case1.c1_inv_n bs HIb) as Hnb.
  pose proof (gb_sp_facts B MT cx HB) as (Hal16 & Hlo & Hhi & Hsp1).
  pose proof (gb_sp1_al B MT cx HB) as Hsp1al.
  pose proof (gb_F_facts B MT LAWS cx fp W3 ms ly3 S3 md k HB HJ HFR) as (HF0 & HFc & HFia & _ & HSHeq).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof pa_B_ok as HBok. pose proof (pa_base_lo (PL := PL_box) (PI := PI)) as HBLO.
  pose proof HB as (HPRE0 & _). pose proof HPRE0 as (_ & _ & _ & Hgp & Htp & _).
  pose proof HREG as (Hrin & _).
  pose proof HJ as HJ0.
  set (E := Eimg (Ereg (ms_regs ms) [w64 nch; w64 (Boxreg.bx_fabric bs); w64 (Boxreg.bx_n bs);
                                     w64 (gF cx fp + GO_PREV)])).
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg (ms_regs ms) [w64 nch; w64 (Boxreg.bx_fabric bs); w64 (Boxreg.bx_n bs);
                                                  w64 (gF cx fp + GO_PREV)]) E)
    by (split; [intros q Hq; subst E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EL : forall n, (n < A_TEXT)%nat ->
    ew E n = ew (Ereg (ms_regs ms) [w64 nch; w64 (Boxreg.bx_fabric bs); w64 (Boxreg.bx_n bs);
                                    w64 (gF cx fp + GO_PREV)]) n)
    by (intros n Hn; subst E; apply Eimg_low; exact Hn).
  assert (E2 : ew E 2 = w64 (c_sp1 cx))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (ms_regs ms) _ 2 2%bv eq_refl); exact G2).
  assert (E3 : ew E 3 = getr (ms_regs ms) 3)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat (ms_regs ms) _ 3 3%bv eq_refl)).
  assert (E4 : ew E 4 = getr (ms_regs ms) 4)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat (ms_regs ms) _ 4 4%bv eq_refl)).
  assert (E8 : ew E 8 = w64 (spZ (c_regs cx)))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (ms_regs ms) _ 8 8%bv eq_refl); exact G8).
  assert (E9 : ew E 9 = w64 (c_sp1 cx))
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (ms_regs ms) _ 9 9%bv eq_refl); exact G9).
  assert (E22 : ew E 22 = w64 h)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (ms_regs ms) _ 22 22%bv eq_refl); exact R22).
  assert (E26 : ew E 26 = w64 u)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (ms_regs ms) _ 26 26%bv eq_refl); exact R26).
  assert (E27 : ew E 27 = w64 v)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat (ms_regs ms) _ 27 27%bv eq_refl); exact R27).
  assert (E32 : ew E 32 = w64 nch) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
  assert (E33 : ew E 33 = w64 (Boxreg.bx_fabric bs))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
  assert (E34 : ew E 34 = w64 (Boxreg.bx_n bs)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 2)).
  assert (E35 : ew E 35 = w64 (gF cx fp + GO_PREV))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 3)).
  assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite E9; apply unsigned_lit_small; lia).
  assert (HS : st_ok_pi SEGS VAL E cw_ss0 (restrict (w_H W3) ms)).
  { rewrite (c1_core_mkst cx fp PC1_dec ms HCO) at 1.
    unfold cw_ss0. apply pa_entry_st_ok_full.
    - subst E. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil].
      unfold cw_R0, YP09.region_ok. cbv zeta.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil;
        (eapply chunk_ok_val; [rewrite cw_denot_off0; eassumption | cbn; unfold GO_PREV; lia | cbn; lia |];
         apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms)); eassumption).
    - cbn [YP09.pairwise_disjoint YP09.all_disjoint]. split; exact I.
    - split; [exact I | split; exact I]. }
  assert (SHOK : sh_ok SEGS (SLit cw_SB) [] E (mrestrict (w_H W3) (ms_mem ms))) by constructor.
  assert (HM : forall x, ms_mem ms x = ms_mem ms x) by reflexivity.
  assert (Hnch64 : 0 <= nch < 2 ^ 64) by lia.
  assert (Hfab64 : 0 <= Boxreg.bx_fabric bs < 2 ^ 64) by lia.
  pose proof (cw_a0_denot E nch (Boxreg.bx_fabric bs) E32 E33 Hnch64 Hfab64) as A0.
  pose proof (cw_s5_denot E nch (Boxreg.bx_fabric bs) E32 E33 Hnch64 Hfab64) as S5d.
  pose proof (cw_s5_iff nch (Boxreg.bx_fabric bs) Hnch Hfab) as W5.
  pose proof (cw_land1 (cw_s5 nch (Boxreg.bx_fabric bs))) as L1.
  (* 0x807a8 .. 0x807c8: s5 and its low bit *)
  paj_run_tok (paj_run B LAWS) HS HJ SHOK cw_Bspan; [awr_ok_tac|]. cw_upd.
  psrr_branch_tok (paj_run B LAWS) (paj_branch (PI := PI)) HS SHOK cw_Bspan.
  { (* 0x807c8 taken: the width is not a legal one; want = -1 (0x807e0) *)
    rewrite A0 in Hc. change (sv_denot E (SLit 0)) with (Z_to_bv 64 0) in Hc.
    rewrite cw_bne0 in Hc by lia. cw_zbool. rename Hc into Hb1.
    paj_run_to_tok (paj_run_to B LAWS) HS HJ SHOK cw_Bspan PC1_call; [awr_ok_tac|]. cw_upd.
    eapply (cw_fin0 i cx fp k acc ly3 S3 W3 md ms _ _ r bs pos M nch (-1) v E _ _ HK HB HJ0 HJ HFR HMO HCO HS HAE
      eq_refl eq_refl ltac:(vm_compute; reflexivity) HM HBASE HREG HMAC Hnch S58 S30
      (c1_want_no bs M nch (-1) (fun H => Hb1 (proj2 W5 (proj1 H))))
      ltac:(lia) ltac:(cwv) ltac:(cwv) ltac:(cwv) Hv Hvr R27 ltac:(cwv)). }
  rewrite A0 in Hc. change (sv_denot E (SLit 0)) with (Z_to_bv 64 0) in Hc.
  rewrite cw_bne0 in Hc by lia. cw_zbool. rename Hc into Hb1.
  assert (Ho : reac_boxreg_add_c.add_width_ok nch (Boxreg.bx_fabric bs)) by (apply W5; exact Hb1).
  pose proof Ho as (_ & Hk2 & _).
  (* 0x807cc: beqz s11 *)
  paj_run_tok (paj_run B LAWS) HS HJ SHOK cw_Bspan; [awr_ok_tac|]. cw_upd.
  psrr_branch_tok (paj_run B LAWS) (paj_branch (PI := PI)) HS SHOK cw_Bspan.
  { (* taken: the MAC is zero; want = -1 *)
    rewrite cw_denot_off0, E27 in Hc. change (sv_denot E (SLit 0)) with (Z_to_bv 64 0) in Hc. unfold w64 in Hc.
    rewrite cw_beq0 in Hc by lia. cw_zbool. rename Hc into Hb2.
    paj_run_to_tok (paj_run_to B LAWS) HS HJ SHOK cw_Bspan PC1_call; [awr_ok_tac|]. cw_upd.
    eapply (cw_fin0 i cx fp k acc ly3 S3 W3 md ms _ _ r bs pos M nch (-1) v E _ _ HK HB HJ0 HJ HFR HMO HCO HS HAE
      eq_refl eq_refl ltac:(vm_compute; reflexivity) HM HBASE HREG HMAC Hnch S58 S30
      (c1_want_no bs M nch (-1) (fun H => proj2 H (proj1 Hv Hb2)))
      ltac:(lia) ltac:(cwv) ltac:(cwv) ltac:(cwv) Hv Hvr R27 ltac:(cwv)). }
  rewrite cw_denot_off0, E27 in Hc. change (sv_denot E (SLit 0)) with (Z_to_bv 64 0) in Hc. unfold w64 in Hc.
  rewrite cw_beq0 in Hc by lia. cw_zbool. rename Hc into Hb2.
  assert (Hz : M <> Boxreg.zero6) by (intros HM0; apply Hb2; apply Hv; exact HM0).
  (* 0x807d0: bgez s6 *)
  paj_run_tok (paj_run B LAWS) HS HJ SHOK cw_Bspan; [awr_ok_tac|]. cw_upd.
  psrr_branch_tok (paj_run B LAWS) (paj_branch (PI := PI)) HS SHOK cw_Bspan.
  { (* taken: a row holds the MAC; want = h (0x807e4) *)
    rewrite cw_denot_off0, E22 in Hc. change (sv_denot E (SLit 0)) with (Z_to_bv 64 0) in Hc. unfold w64 in Hc.
    rewrite cw_bge0 in Hc by lia. cw_zbool. rename Hc into Hb3.
    paj_run_to_tok (paj_run_to B LAWS) HS HJ SHOK cw_Bspan PC1_call; [awr_ok_tac|]. cw_upd.
    eapply (cw_fin0 i cx fp k acc ly3 S3 W3 md ms _ _ r bs pos M nch h v E _ _ HK HB HJ0 HJ HFR HMO HCO HS HAE
      eq_refl eq_refl ltac:(vm_compute; reflexivity) HM HBASE HREG HMAC Hnch S58 S30
      (c1_want_h bs M nch (-1) h Ho Hz (c1_held_of bs M v h HSH Hb3))
      ltac:(lia) ltac:(cwv) ltac:(cwv) ltac:(cwv) Hv Hvr R27 ltac:(cwv)). }
  rewrite cw_denot_off0, E22 in Hc. change (sv_denot E (SLit 0)) with (Z_to_bv 64 0) in Hc. unfold w64 in Hc.
  rewrite cw_bge0 in Hc by lia. cw_zbool. rename Hc into Hb3.
  assert (Hh1 : h = -1) by lia. subst h.
  pose proof (c1_nheld_of bs M v HSH Hb2) as HNH.
  (* 0x807d4: bltz s10 *)
  paj_run_tok (paj_run B LAWS) HS HJ SHOK cw_Bspan; [awr_ok_tac|]. cw_upd.
  psrr_branch_tok (paj_run B LAWS) (paj_branch (PI := PI)) HS SHOK cw_Bspan.
  2: { (* not taken: a row of this width is unbound; want = u (0x807d8) *)
    rewrite cw_denot_off0, E26 in Hc. change (sv_denot E (SLit 0)) with (Z_to_bv 64 0) in Hc. unfold w64 in Hc.
    rewrite cw_blt0 in Hc by lia. cw_zbool. rename Hc into Hb4.
    paj_run_to_tok (paj_run_to B LAWS) HS HJ SHOK cw_Bspan PC1_call; [awr_ok_tac|]. cw_upd.
    eapply (cw_fin0 i cx fp k acc ly3 S3 W3 md ms _ _ r bs pos M nch u v E _ _ HK HB HJ0 HJ HFR HMO HCO HS HAE
      eq_refl eq_refl ltac:(vm_compute; reflexivity) HM HBASE HREG HMAC Hnch S58 S30
      (c1_want_u bs M nch (-1) u Ho Hz HNH (c1_unb_of bs nch u HSU Hb4))
      ltac:(lia) ltac:(cwv) ltac:(cwv) ltac:(cwv) Hv Hvr R27 ltac:(cwv)). }
  (* taken: no row to reuse, the block at 0x80cf0 *)
  rewrite cw_denot_off0, E26 in Hc. change (sv_denot E (SLit 0)) with (Z_to_bv 64 0) in Hc. unfold w64 in Hc.
  rewrite cw_blt0 in Hc by lia. cw_zbool. rename Hc into Hb4.
  assert (Hu1 : u = -1) by lia. subst u.
  pose proof (c1_nunb_of bs nch HSU) as HNU.
  (* 0x80cfc: blt 4, s10 *)
  paj_run_tok (paj_run B LAWS) HS HJ SHOK cw_Bspan; [awr_ok_tac|]. cw_upd.
  psrr_branch_tok (paj_run B LAWS) (paj_branch (PI := PI)) HS SHOK cw_Bspan.
  { (* taken: the table is full; want = -1, lowest_free is not called *)
    change (sv_denot E (SLit 4)) with (Z_to_bv 64 4) in Hc. rewrite cw_denot_off0, E34 in Hc. unfold w64 in Hc.
    rewrite cw_blt4 in Hc by lia. cw_zbool. rename Hc into Hb5.
    assert (H5 : 5 <= Boxreg.bx_n bs) by lia.
    paj_run_to_tok (paj_run_to B LAWS) HS HJ SHOK cw_Bspan PC1_call; [awr_ok_tac|]. cw_upd.
    eapply (cw_fin0 i cx fp k acc ly3 S3 W3 md ms _ _ r bs pos M nch (-1) v E _ _ HK HB HJ0 HJ HFR HMO HCO HS HAE
      eq_refl eq_refl ltac:(vm_compute; reflexivity) HM HBASE HREG HMAC Hnch S58 S30
      (c1_want_full bs M nch (-1) Ho Hz HNH HNU (or_introl H5))
      ltac:(lia) ltac:(cwv) ltac:(cwv) ltac:(cwv) Hv Hvr R27 ltac:(cwv)). }
  change (sv_denot E (SLit 4)) with (Z_to_bv 64 4) in Hc. rewrite cw_denot_off0, E34 in Hc. unfold w64 in Hc.
  rewrite cw_blt4 in Hc by lia. cw_zbool. rename Hc into Hb5.
  (* 0x80d00 .. 0x80d0c: lowest_free (&prev, nch, fabric) *)
  paj_run_tok (paj_run B LAWS) HS HJ SHOK cw_Bspan; [awr_ok_tac|]. cw_upd.
  lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) => rename m into m5 end.
  assert (KP1 : forall r0, In r0 cw_csl -> getr (ms_regs m5) r0 = getr (ms_regs ms) r0)
    by exact (regs_kept_of_st_ok SEGS E _ (restrict (w_H W3) m5) (ms_regs ms) _ cw_csl HS HAE
                ltac:(vm_compute; reflexivity)).
  destruct (cw_keep_all i cx fp k acc ly3 S3 W3 md ms m5 r bs pos M nch HB HJ0 HFR
    (cw_kept_pw cx fp r W3 (ms_mem ms) (ms_mem m5) HM) (KP1 20%bv ltac:(cw_in)) HBASE HREG HMAC S58)
    as (HB5 & HREG5 & HMAC5 & S585).
  pose proof HB5 as (_ & _ & _ & _ & _ & HMEM5 & _).
  pose proof HMEM5 as ((S8 & Sj) & HSH5 & _ & _ & _ & HPV5).
  assert (S16 : rdword (aview SEGS (w_H W3) (ms_mem m5)) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx))).
  { pose proof (Sj 0 ltac:(lia)) as H0. replace (spZ (c_regs cx) - 16 - 8 * 0) with (spZ (c_regs cx) - 16) in H0 by lia.
    rewrite H0. unfold s0Z. do 3 f_equal. }
  assert (HF64 : gF cx fp mod 64 = 0) by (eapply gb_F_al; first [exact LAWS | exact HB | exact HJ0 | exact HFR]).
  assert (EFA : frame_addr ly3 GB_CID fp = gF cx fp)
    by (eapply gb_frame_addr_eq; first [exact LAWS | exact HB | exact HJ0 | exact HFR]).
  assert (HRA : range_addressable (aview SEGS (w_H W3) (ms_mem m5)) SHADOW_OFF (gF cx fp + GO_PREV + 0) 288)
    by (eapply gb_prev_ra; first [exact LAWS | exact HB | exact HJ | exact HFR | exact HSH5 | lia | unfold REG_SIZE; lia]).
  rewrite Z.add_0_r in HRA.
  assert (HOBJ : afobj SEGS B ly3 S3 W3 (ms_mem m5) (gF cx fp + GO_PREV) REG_SIZE).
  { split; [|split; [|exact HRA]].
    - exists GB_CID, fp. rewrite EFA. change (fs_frame_bytes GB_CID) with 512. unfold GO_PREV, REG_SIZE.
      split; [rewrite HFR; left; reflexivity|]. split; [unfold GB_CID; lia|].
      split; [|lia]. apply Z.mod_divide; [lia|]. apply Z.mod_divide in HF64; [|lia].
      destruct HF64 as [q Hq]. exists (8 * q). lia.
    - unfold GO_PREV. apply Z.mod_divide; [lia|]. apply Z.mod_divide in HF64; [|lia].
      destruct HF64 as [q Hq]. exists (8 * q + 8). lia. }
  pose proof HIb as ((HLEN & HB1 & HB2 & HB3 & _) & _).
  assert (WS : LowestFree.LOWEST_FREE_STK = 4176) by reflexivity.
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12.
  cwreg HS (21%bv : bv 5) Q21. cwreg HS (25%bv : bv 5) Q25. cwreg HS (26%bv : bv 5) Q26.
  rewrite pa_sigma_lowest_free.
  assert (Usp : spZ (ms_regs m5) = spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))).
  { unfold spZ at 1. rewrite Q2, E2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
  eapply SRr_bind.
  { eapply (cl_callS B LAWS W3 (ms_regs m5) (ms_mem m5) _ GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx)
      (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 _ k LowestFree.LOWEST_FREE_STK [] 0 (c_sp1 cx - spZ (c_regs cx))
      (getr (ms_regs m5) 1) (gch cx)
      (fun ly2 S2 W2 regs2 mem2 md2 => ly2 = ly3 /\ S2 = S3 /\ W2 = W3 /\
         exists z, getr regs2 10 = w64 z /\ lowest_free_c.lowest_free_res bs nch (Boxreg.bx_fabric bs) z) HJ Usp).
    - apply cw_sub_mod16; [exact Hsp1al | exact Hal16].
    - lia.
    - rewrite WS. lia.
    - rewrite WS. unfold GB_STK. lia.
    - rewrite Q3, E3, G3. exact Hgp.
    - rewrite Q4, E4, G4. exact Htp.
    - reflexivity.
    - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite Q1, unsigned_lit_small by lia. lia.
    - replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) by lia.
      unfold s0Z at 1. rewrite Q8, E8. unfold w64. rewrite unsigned_lit_small by lia.
      exact (cw_achain cx ly3 S3 W3 (ms_mem m5) _ _ _ (c_sp1 cx) HB HJ S8 S16 ltac:(lia)).
    - intros HPRE1.
      exact (TLOWFREE ly3 S3 W3 (ms_regs m5) (ms_mem m5) _ (gch cx) (gF cx fp + GO_PREV) nch (Boxreg.bx_fabric bs) bs
        HPRE1 ltac:(rewrite Q10; exact E35) ltac:(rewrite Q11; exact E32) ltac:(rewrite Q12; exact E33)
        ltac:(lia) Hfab HOBJ HLEN HPV5 HB1 HB2 HB3).
    - intros a (rgx & [] & _). }
  cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HJc & HP2 & (-> & -> & -> & lf & Ha0 & Hres)).
  rewrite ?Z.add_0_r in HJ2.
  (* lowest_free kept every byte this phase's facts speak about *)
  assert (HKC : gb_keep cx fp W3 [(r, REG_SIZE)] (ms_mem m5) mem2).
  { replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) in HJc by lia.
    eapply gb_keep_call; first [ exact LAWS | exact HB | exact HJ | exact HFR | lia | exact HJc
      | (intros p0 n0 Hp0; unfold gblk1 in HBL; rewrite HBL; apply in_or_app; left; exact Hp0)
      | (constructor; [|constructor]; exists REG_SIZE; cbn [fst snd];
         split; [exact Hrin | change (req_size REG_SIZE) with 288; unfold REG_SIZE; lia]) ]. }
  assert (Hlf : -1 <= lf <= 38) by (destruct Hres as [(-> & _) | (H0 & _ & _)]; lia).
  (* 0x80d10: the state after the call *)
  set (EC := Eimg (Ereg regs2 [])).
  assert (HEIC : img_env VAL A_LIM EC) by (subst EC; apply Eimg_env).
  assert (EEC : forall q (r0 : bv 5), Z.of_nat q = bv_unsigned r0 -> ew EC q = getr regs2 r0)
    by (intros q r0 Hq; subst EC; apply ew_Eimg_Ereg_nat; exact Hq).
  assert (HAEC : env_agree 32 (Ereg regs2 []) EC)
    by (split; [intros q Hq; subst EC; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (KP2 : forall r0 : bv 5, acallee_saved (bv_unsigned r0) -> getr regs2 r0 = getr (ms_regs m5) r0)
    by (intros r0 Hr0; pose proof (HP2 (bv_unsigned r0) Hr0) as X; rewrite Z_to_bv_bv_unsigned in X; exact X).
  assert (P9 : ew EC 9 = w64 (c_sp1 cx)).
  { rewrite (EEC 9%nat 9%bv eq_refl). rewrite KP2 by cw_cs. rewrite (KP1 9%bv) by cw_in. exact G9. }
  assert (U9C : bv_unsigned (ew EC 9) = c_sp1 cx) by (rewrite P9; apply unsigned_lit_small; lia).
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & _).
  rewrite Q1.
  assert (HSC : st_ok_pi SEGS VAL EC cw_ssC
    (restrict (w_H W3) (mkst regs2 (Z_to_bv 64 (BASE + 0xdc4)) mem2 (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold cw_ssC. apply pa_entry_st_ok_full.
    - subst EC. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_cons; [|apply Forall_nil]. unfold cw_R30, YP09.region_ok. cbv zeta.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
      rewrite U9C. split; [lia|]. split; [lia|].
      split; [intros o0 Ho0; apply (apresent_writable SEGS); apply HJpres; unfold GB_STK; lia | apply Forall_nil].
    - cbn [YP09.pairwise_disjoint YP09.all_disjoint]. split; exact I.
    - split; [|split; exact I]. cbn [f_atoms atoms_ok]. split; [|exact I]. unfold afact_ok.
      cbn [af_lo af_hi af_al2]. rewrite U9C. change (2 ^ 5) with 32. split; [lia|]. split; [exact Hsp1al | lia]. }
  assert (SHOKC : sh_ok SEGS (SLit cw_SB) [] EC (mrestrict (w_H W3) mem2)) by constructor.
  clear SHOK.
  (* 0x80d10 .. 0x80d1c: slot 0x30 := lf; s6 := (lf >>s 63) | n_before; back to 0x807e8 *)
  paj_run_to_tok (paj_run_to B LAWS) HSC HJ2 SHOKC cw_Bspan PC1_call;
  [ lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end;
    repeat first [ apply awr_ok_nil
                 | apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
                   [reflexivity | rewrite U9C; lia | cbn; unfold GB_STK; lia | cbn; lia | ] ]
  | ].
  lazymatch type of HSC with st_ok_pi _ _ _ _ (restrict _ ?m) => rename m into mF end.
  assert (HKF : cw_kept cx fp r W3 (ms_mem ms) (ms_mem mF)).
  { intros a Ha Hka Hna.
    lazymatch goal with HFx : frame_of EC ?rs mem2 (ms_mem mF) |- _ =>
      rewrite (cw_keep_outside EC rs mem2 (ms_mem mF) (w_H W3) a HFx Ha);
      [ rewrite (HKC a Hka); apply cw_aview_pw; exact HM
      | let rs' := eval vm_compute in rs in change rs with rs';
        intros (rr & Hr & Hb);
        repeat (destruct Hr as [Hr | Hr];
          [subst rr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi YP09.base_val] in Hb; rewrite U9C in Hb; lia |]);
        destruct Hr ] end. }
  assert (S30F : rdword (aview SEGS (w_H W3) (ms_mem mF)) (c_sp1 cx + 0x30) = Some (lf mod 2 ^ 64)).
  { eapply (cw_slot_reg EC _ mF W3 0%nat); [exact HSC | reflexivity | exact U9C | cbn [In]; left; reflexivity | |
      apply Z.mod_pos_bound; lia].
    rewrite cw_denot_off0, (EEC 10%nat 10%bv eq_refl), Ha0. unfold w64. symmetry. apply Z_to_bv64_mod. }
  assert (KPF : forall r0, In r0 cw_csl2 -> getr (ms_regs mF) r0 = getr regs2 r0)
    by exact (regs_kept_of_st_ok_pi EC _ (restrict (w_H W3) mF) regs2 _ cw_csl2 HSC HAEC
                ltac:(vm_compute; reflexivity)).
  assert (KPA : forall r0, In r0 cw_csl -> getr (ms_regs mF) r0 = getr (ms_regs ms) r0).
  { intros r0 Hr0. rewrite (KPF r0) by (revert Hr0; cbn [cw_csl cw_csl2 In]; tauto).
    rewrite KP2 by (revert Hr0; cbn [cw_csl In]; intros Hr0;
                    repeat (destruct Hr0 as [<- | Hr0]; [cw_cs |]); destruct Hr0).
    exact (KP1 r0 Hr0). }
  cwreg HSC (22%bv : bv 5) T22.
  pmkst HSC.
  assert (Hnb4 : 0 <= Boxreg.bx_n bs <= 4) by lia.
  assert (V26 : ew EC 26 = Z_to_bv 64 (Boxreg.bx_n bs)).
  { rewrite (EEC 26%nat 26%bv eq_refl). rewrite KP2 by cw_cs. rewrite Q26, cw_denot_off0. exact E34. }
  assert (V10 : ew EC 10 = Z_to_bv 64 lf) by (rewrite (EEC 10%nat 10%bv eq_refl); exact Ha0).
  rewrite (cw_or_denot EC lf (Boxreg.bx_n bs) V10 V26 Hlf Hnb4) in T22.
  eapply (cw_land i cx fp k acc ly3 S3 W3 md ms (ms_regs mF) (ms_mem mF) _ r bs pos M nch lf
    (if lf <? 0 then -1 else Boxreg.bx_n bs) v HK HB HJ0 HJ2 HFR HMO HCO KPA HKF HBASE HREG HMAC Hnch S58 S30F Hlf).
  - destruct (Z.ltb_spec lf 0) as [Hl0 | Hl0].
    + assert (Hlm : lf = -1) by lia. subst lf.
      apply c1_want_full; [exact Ho | exact Hz | exact HNH | exact HNU | right; exact Hres].
    + apply c1_want_new; [exact Ho | exact Hz | exact HNH | exact HNU | lia | exact Hl0 | exact Hres].
  - destruct (lf <? 0); lia.
  - exact T22.
  - rewrite (KPF 26%bv) by cw_in. rewrite KP2 by cw_cs. rewrite Q26, cw_denot_off0. exact E34.
  - rewrite (KPF 25%bv) by cw_in. rewrite KP2 by cw_cs. rewrite Q25, cw_denot_off0. exact E33.
  - exact Hv.
  - exact Hvr.
  - exact R27.
  - rewrite (KPF 21%bv) by cw_in. rewrite KP2 by cw_cs. rewrite Q21. exact S5d.
Qed.

End c.
End b.
End a.

(* ==== the piece 0x806cc .. 0x807a8: bcmp (mac, ZERO), prev.n and the scan of prev's rows ==== *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg box_listing}.
#[local] Notation SEGS := (@pa_segs _ box_listing PI).
#[local] Notation VAL := (@pa_val _ box_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ box_listing PI).
#[local] Notation BASE := (@pa_val _ box_listing PI A_TEXT).
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis MTL : ameter_laws MT.
Hypothesis HISV : img_shadow_vis SEGS B.
Hypothesis HGLOB : globs_marked SEGS B BX_G.
Hypothesis AMEMCPY : aintrin_realizes SEGS B OCpy (SIGMA BS___asan_memcpy).
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA BS___interceptor_trampoline_bcmp).
Hypothesis TFIND : ReacBoxregFind.treac_boxreg_find_spec B.
Hypothesis TADD : ReacBoxregAdd.treac_boxreg_add_spec B.
Hypothesis TLOWFREE : LowestFree.tlowest_free_spec B.
Hypothesis HZERO : SnprintfDef.asn_rom_bytes SEGS B (VAL (A_OBJ 6))
  (map (fun b : byte => bv_unsigned b) Boxreg.zero6).
Hypothesis HRMB : SnprintfDef.asn_rom_bytes SEGS B (VAL (A_OBJ 4)) [0; 64; 171; 0; 0].
Hypothesis HMRG : Forall (fun g => IMG_LO + 64 <= fst g /\ fst g + snd g + 64 <= IMG_HI) BX_G.
Variable POST : bcx -> world SEGS -> config -> Prop.

(* ---- the symbolic states of the piece ---- *)
Definition cs_SB : Z := 0x7fff8000.
Definition cs_Bx : sv := SOff 18 0.
Definition cs_Bspan : Z * Z := (cs_SB, cs_SB + 2 ^ 44 - 1).
Definition cs_R0sp : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 0x98 0x30 0x38
    [YP09.mkChunk 0x20 (CVal 8 (SOff 32 12)); YP09.mkChunk 0x78 (CVal 8 (SOff 32 0))].
Definition cs_R0n : YP09.region := YP09.mkRegion (Some 32%nat) 280 284 0 0 [YP09.mkChunk 280 (CVal 4 (SOff 33 0))].
Definition cs_F0 : facts := mkFacts
  [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (18%nat, mkAF cs_SB cs_SB 0); (32%nat, mkAF 4096 140737479966720 3);
   (33%nat, mkAF 0 5 0)] [] [].
Definition cs_ss0 : sstate := mkSS PC1_nch sr_atoms [cs_R0sp; cs_R0n] None cs_F0.
Definition cs_RLsp : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0 0x98 0 0
    [YP09.mkChunk 0x58 (CVal 8 (SOff 33 0)); YP09.mkChunk 0x70 (CVal 8 (SOff 32 0))].
Definition cs_RLrow : YP09.region := YP09.mkRegion (Some 23%nat) 12 16 0 0 [YP09.mkChunk 12 (CVal 4 (SOff 34 0))].
Definition cs_FL : facts := mkFacts
  [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (18%nat, mkAF cs_SB cs_SB 0); (19%nat, mkAF 4096 140737479966720 2);
   (23%nat, mkAF 4096 140737479966720 3); (32%nat, mkAF 4096 140737479966720 3); (33%nat, mkAF 0 255 0);
   (34%nat, mkAF 0 255 0)] [] [].
Definition cs_SHL : list shent := [mkSHE 19 0 8].
Definition cs_ssL : sstate := mkSS PC1_scan sr_atoms [cs_RLsp; cs_RLrow] None cs_FL.

(* ---- words, branches and bytes ---- *)
Lemma cs_den0 : forall E n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma cs_den_off : forall E n v x, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  sv_denot E (SOff n x) = Z_to_bv 64 (v + x).
Proof.
  intros E n v x F Hv. rewrite denot_lit_U, U_SOff, F, unsigned_lit_small by exact Hv.
  unfold zcanon, M64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). apply Z.mod_mod. lia.
Qed.
Lemma cs_signed : forall z, - 2 ^ 63 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof. exact Boxreg.signed_lit. Qed.
Lemma cs_bge : forall E n h, ew E n = Z_to_bv 64 h -> - 2 ^ 63 <= h < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = negb (h <? 0).
Proof.
  intros E n h F Hh. rewrite (cs_den0 E n h F). cbn [sv_denot branch_taken]. unfold bv_lts.
  rewrite (cs_signed h Hh), (cs_signed 0) by lia. reflexivity.
Qed.
Lemma cs_ble : forall E n z, ew E n = Z_to_bv 64 z -> - 2 ^ 63 <= z < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E (SLit 0)) (sv_denot E (SOff n 0)) = negb (0 <? z).
Proof.
  intros E n z F Hz. rewrite (cs_den0 E n z F). cbn [sv_denot branch_taken]. unfold bv_lts.
  rewrite (cs_signed z Hz), (cs_signed 0) by lia. reflexivity.
Qed.
Lemma cs_addiw : forall E n j, ew E n = Z_to_bv 64 j -> 0 <= j < 2 ^ 31 - 1 ->
  sv_denot E (SAluw ALU_ADD (SOff n 0) (SLit 1)) = Z_to_bv 64 (j + 1).
Proof.
  intros E n j F Hj. rewrite denot_lit_U. apply Z_to_bv64_eq_mod. f_equal.
  rewrite U_of_S, S_SAluw, U_SOff, U_SLit, F, unsigned_lit_small by lia. cbn [zalu_raw].
  unfold zcanon, M64, bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (bv_modulus 64) with 18446744073709551616. change (2 ^ 32) with 4294967296.
  change (2 ^ 64) with 18446744073709551616.
  rewrite !(Z.mod_small (j + 0)) by lia. rewrite (Z.mod_small 1 18446744073709551616) by lia.
  rewrite (Z.mod_small 1 4294967296) by lia. rewrite (Z.mod_small (j + 0 + 1 + 2147483648)) by lia.
  rewrite Z.mod_small by lia. lia.
Qed.

(* The four bytes at offset o of a table as a number, and the word lw reads there when it is not negative. *)
Definition cs_b (bs : list byte) (o : Z) : Z := bv_unsigned (nth (Z.to_nat o) bs (Z_to_bv 8 0)).
Lemma cs_b_range : forall bs o, 0 <= cs_b bs o < 256.
Proof.
  intros bs o. unfold cs_b. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat o) bs (Z_to_bv 8 0))) as R.
  change (bv_modulus 8) with 256 in R. exact R.
Qed.
Definition cs_nu (bs : list byte) (o : Z) : Z :=
  cs_b bs o + 256 * (cs_b bs (o + 1) + 256 * (cs_b bs (o + 2) + 256 * cs_b bs (o + 3))).
Lemma cs_nu_range : forall bs o, 0 <= cs_nu bs o < 2 ^ 32.
Proof.
  intros bs o. unfold cs_nu. pose proof (cs_b_range bs o). pose proof (cs_b_range bs (o + 1)).
  pose proof (cs_b_range bs (o + 2)). pose proof (cs_b_range bs (o + 3)). lia.
Qed.
Lemma cs_skipn_cons : forall {A} (l : list A) k d, (k < length l)%nat -> skipn k l = nth k l d :: skipn (S k) l.
Proof.
  intros A l. induction l as [|x l IH]; intros k d Hk; cbn [length] in Hk; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.
Lemma cs_bsub4 : forall (bs : list byte) o, length bs = 288%nat -> 0 <= o -> o + 4 <= 288 ->
  Boxreg.bsub bs o 4 = [nth (Z.to_nat o) bs (Z_to_bv 8 0); nth (Z.to_nat (o + 1)) bs (Z_to_bv 8 0);
                        nth (Z.to_nat (o + 2)) bs (Z_to_bv 8 0); nth (Z.to_nat (o + 3)) bs (Z_to_bv 8 0)].
Proof.
  intros bs o Hl H0 H4. unfold Boxreg.bsub. change (Z.to_nat 4) with 4%nat.
  replace (Z.to_nat (o + 1)) with (S (Z.to_nat o)) by lia.
  replace (Z.to_nat (o + 2)) with (S (S (Z.to_nat o))) by lia.
  replace (Z.to_nat (o + 3)) with (S (S (S (Z.to_nat o)))) by lia.
  rewrite (cs_skipn_cons bs (Z.to_nat o) (Z_to_bv 8 0)) by lia.
  rewrite (cs_skipn_cons bs (S (Z.to_nat o)) (Z_to_bv 8 0)) by lia.
  rewrite (cs_skipn_cons bs (S (S (Z.to_nat o))) (Z_to_bv 8 0)) by lia.
  rewrite (cs_skipn_cons bs (S (S (S (Z.to_nat o)))) (Z_to_bv 8 0)) by lia.
  reflexivity.
Qed.
Lemma cs_rd4_nu : forall bs o, length bs = 288%nat -> 0 <= o -> o + 4 <= 288 -> 0 <= Boxreg.rd4 bs o ->
  Boxreg.rd4 bs o = cs_nu bs o.
Proof.
  intros bs o Hl H0 H4 Hn. pose proof (cs_nu_range bs o) as Hr. unfold Boxreg.rd4 in *.
  rewrite (cs_bsub4 bs o Hl H0 H4) in *.
  rewrite OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Bytes.bytes_le_to_Z_le_val in *.
  cbn [map OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib.Bytes.le_val] in *.
  unfold cs_nu, cs_b in *.
  set (b0 := bv_unsigned (nth (Z.to_nat o) bs (Z_to_bv 8 0))) in *.
  set (b1 := bv_unsigned (nth (Z.to_nat (o + 1)) bs (Z_to_bv 8 0))) in *.
  set (b2 := bv_unsigned (nth (Z.to_nat (o + 2)) bs (Z_to_bv 8 0))) in *.
  set (b3 := bv_unsigned (nth (Z.to_nat (o + 3)) bs (Z_to_bv 8 0))) in *.
  replace (b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 * 0)))) with (b0 + 256 * (b1 + 256 * (b2 + 256 * b3))) in * by lia.
  set (x := b0 + 256 * (b1 + 256 * (b2 + 256 * b3))) in *. clearbody x.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *. change (2 ^ Z.of_N 32) with (2 ^ 32) in *.
  change (2 ^ 32 / 2) with (2 ^ 31) in *. Z.div_mod_to_equations. lia.
Qed.
Lemma cs_nu_byte : forall bs o k, (k < 4)%nat -> (cs_nu bs o / 2 ^ (8 * Z.of_nat k)) mod 256 = cs_b bs (o + Z.of_nat k).
Proof.
  intros bs o k Hk. unfold cs_nu.
  pose proof (cs_b_range bs o) as R0. pose proof (cs_b_range bs (o + 1)) as R1.
  pose proof (cs_b_range bs (o + 2)) as R2. pose proof (cs_b_range bs (o + 3)) as R3.
  destruct k as [|[|[|[|k]]]]; [| | | | lia].
  - replace (o + Z.of_nat 0) with o by lia. change (2 ^ (8 * Z.of_nat 0)) with 1. Z.div_mod_to_equations. lia.
  - change (o + Z.of_nat 1) with (o + 1). change (2 ^ (8 * Z.of_nat 1)) with 256. Z.div_mod_to_equations. lia.
  - change (o + Z.of_nat 2) with (o + 2). change (2 ^ (8 * Z.of_nat 2)) with 65536. Z.div_mod_to_equations. lia.
  - change (o + Z.of_nat 3) with (o + 3). change (2 ^ (8 * Z.of_nat 3)) with 16777216. Z.div_mod_to_equations. lia.
Qed.
Lemma cs_nu_val_mem : forall H (mem : word -> option byte) base bs o, 0 <= o -> o + 4 <= REG_SIZE ->
  (forall i, 0 <= i < REG_SIZE -> aview SEGS H mem (base + i) = Some (bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)))) ->
  val_mem SEGS (mrestrict H mem) (base + o) (N.to_nat 4) (cs_nu bs o).
Proof.
  intros H mem base bs o H0 H4 Hbs. unfold val_mem. intros k Hk. change (N.to_nat 4) with 4%nat in Hk |- *.
  rewrite le_byte_small by (pose proof (cs_nu_range bs o); first [lia | (change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32); lia)]).
  destruct (aview_byte SEGS H mem (base + (o + Z.of_nat k)) _ (Hbs (o + Z.of_nat k) ltac:(unfold REG_SIZE in *; lia)))
    as (b & Hb & Hv & _).
  replace (base + o + Z.of_nat k) with (base + (o + Z.of_nat k)) by lia. rewrite Hb. f_equal.
  apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  rewrite Z.shiftr_div_pow2 by lia. rewrite (cs_nu_byte bs o k Hk). unfold cs_b. symmetry. exact Hv.
Qed.
(* A row's MAC, byte by byte, and two six-byte lists compared byte by byte. *)
Lemma cs_mac_nth : forall (bs : list byte) j i, length bs = 288%nat -> 0 <= j <= 4 -> 0 <= i < 6 ->
  nth (Z.to_nat i) (Boxreg.bx_mac bs j) (Z_to_bv 8 0) = nth (Z.to_nat (56 * j + i)) bs (Z_to_bv 8 0).
Proof.
  intros bs j i Hl Hj Hi. unfold Boxreg.bx_mac, Boxreg.bsub. rewrite nth_firstn.
  replace (Z.to_nat i <? Z.to_nat 6)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  rewrite nth_skipn. f_equal. lia.
Qed.
Lemma cs_bytes_eq : forall L1 L2 : list byte, length L1 = 6%nat -> length L2 = 6%nat ->
  ((forall i, 0 <= i < 6 -> bv_unsigned (nth (Z.to_nat i) L1 (Z_to_bv 8 0)) = bv_unsigned (nth (Z.to_nat i) L2 (Z_to_bv 8 0)))
   <-> L1 = L2).
Proof.
  intros L1 L2 H1 H2. split.
  - intros H. apply (nth_ext _ _ (Z_to_bv 8 0) (Z_to_bv 8 0)); [congruence|].
    intros k Hk. rewrite H1 in Hk. apply bv_eq. rewrite <- (Nat2Z.id k). apply H. lia.
  - intros <- i Hi. reflexivity.
Qed.

Section d.
Variable cx : bcx.
Variables fp k acc i r pos nch : Z.
Variable ly3 : alayout.
Variable S3 : astate.
Variable W3 : world SEGS.
Variables bs M : list byte.
Hypothesis HB : gb_base B MT cx.
Hypothesis HFR : frames S3 = [(GB_CID, fp)].
Hypothesis HFA : frame_addr ly3 GB_CID fp = gF cx fp.
Hypothesis HRIN : In (r, REG_SIZE) (ablocks B ly3 S3).
Hypothesis HINV : Boxreg.boxreg_inv bs.
Hypothesis HLM : length M = 6%nat.
Hypothesis HNCH : 0 <= nch < 256.

(* The numbers the piece's addresses obey: the machine stack, the frame and its shadow, the registry, the input. *)
Definition cs_geo : Prop :=
  spZ (c_regs cx) mod 16 = 0 /\ alloc_ceiling + 32768 <= spZ (c_regs cx) <= 2 ^ 47 /\
  spZ (c_regs cx) - 287 <= c_sp1 cx <= spZ (c_regs cx) - 256 /\ c_sp1 cx mod 32 = 0 /\
  4096 <= gF cx fp /\ gF cx fp + 512 <= alloc_ceiling /\ in_app (gF cx fp) 512 /\ gF cx fp mod 64 = 0 /\
  gSH cx fp = SHADOW_OFF + gF cx fp / 8 /\
  r mod 16 = 0 /\ 4096 <= r /\ r + 288 <= alloc_ceiling /\
  (c_n cx = 0 \/ (0 <= c_p cx /\ c_p cx + c_n cx <= alloc_ceiling)).
Hypothesis HGEO : cs_geo.

Definition cs_J (mem : word -> option byte) (md : Model) : Prop :=
  ajournal SEGS B GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GB_CID, fp)] ly3 S3 W3 mem md k.

(* The memory the piece carries, as facts of a machine state whose memory is m. *)
Definition cs_ms (m : word -> option byte) : machine_state := mkst (c_regs cx) (Z_to_bv 64 0) m (seg_rom SEGS).
Definition cs_mem0 (m : word -> option byte) : Prop :=
  c1mem cx fp W3 (cs_ms m) bs /\ gslots_r cx fp W3 (cs_ms m) r (Boxreg.bx_fabric bs) /\ gcursor cx W3 (cs_ms m) pos /\
  gslot cx W3 (cs_ms m) 0x68 i /\ gslot cx W3 (cs_ms m) 0x48 (Boxreg.bx_n bs) /\ greg B ly3 S3 W3 (cs_ms m) r bs /\
  c1mac cx fp W3 (cs_ms m) M /\ gslot cx W3 (cs_ms m) 0x58 nch.
Definition cs_mem (m : word -> option byte) : Prop :=
  cs_mem0 m /\ gslot cx W3 (cs_ms m) 0x30 ((-1) mod 2 ^ 64).

(* The bytes those facts speak about: below the allocator's ceiling (frame, shadow, registry, input), the spill
   slots other than 0x30, and the saved words below the caller's sp; cs_footx adds slot 0x30. *)
Definition cs_foot (a : Z) : Prop :=
  (0 <= a < alloc_ceiling) \/ (c_sp1 cx + 0x10 <= a < c_sp1 cx + 0x30) \/
  (c_sp1 cx + 0x38 <= a < c_sp1 cx + 0x98) \/ (spZ (c_regs cx) - 104 <= a < spZ (c_regs cx)).
Definition cs_footx (a : Z) : Prop := cs_foot a \/ (c_sp1 cx + 0x30 <= a < c_sp1 cx + 0x38).
Definition cs_kp (m m' : word -> option byte) : Prop :=
  forall a, cs_foot a -> aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a.
Definition cs_kpx (m m' : word -> option byte) : Prop :=
  forall a, cs_footx a -> aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a.

Lemma cs_rd_keep : forall (m m' : word -> option byte) a v,
  (forall j, 0 <= j < 8 -> aview SEGS (w_H W3) m' (a + j) = aview SEGS (w_H W3) m (a + j)) ->
  rdword (aview SEGS (w_H W3) m) a = Some v -> rdword (aview SEGS (w_H W3) m') a = Some v.
Proof. intros m m' a v Hk Hr. rewrite <- Hr. apply rdword_ext. intros j Hj. apply Hk. exact Hj. Qed.

Lemma cs_slot_keep : forall m m' off v, cs_kp m m' ->
  (0x10 <= off /\ off + 8 <= 0x30) \/ (0x38 <= off /\ off + 8 <= 0x98) ->
  gslot cx W3 (cs_ms m) off v -> gslot cx W3 (cs_ms m') off v.
Proof.
  intros m m' off v Hk Ho Hv. unfold gslot in *. cbn [cs_ms ms_mem mkst] in *.
  apply (cs_rd_keep m m' _ v); [|exact Hv]. intros j Hj. apply Hk. unfold cs_foot. lia.
Qed.

Lemma cs_low_keep : forall m m' a, cs_kp m m' -> 0 <= a < alloc_ceiling ->
  aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a.
Proof. intros m m' a Hk Ha. apply Hk. left. exact Ha. Qed.

Lemma cs_mem0_kp : forall m m', cs_mem0 m -> cs_kp m m' -> cs_mem0 m'.
Proof.
  intros m m' HM Hk.
  pose proof HGEO as (Hsp16 & Hsp & Hsp1 & Hsp32 & HF0 & HFc & HFia & HF64 & ESH & Hr16 & Hr0 & Hrc & Hinp).
  pose proof asan_consts as (C1 & _).
  assert (Hfb : fs_frame_bytes GB_CID = 512) by (vm_compute; reflexivity).
  assert (HSHlo : 0 <= gSH cx fp /\ gSH cx fp + 64 <= alloc_ceiling).
  { rewrite ESH. pose proof (Z.div_le_upper_bound (gF cx fp) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
    pose proof (Z.div_pos (gF cx fp) 8 ltac:(lia) ltac:(lia)). unfold SHADOW_OFF. lia. }
  destruct HM as ((HSV & HSH & HFL & HIN & HSF & HPV) & HSR & HCU & H68 & H48 & HRG & HMC & H58).
  unfold cs_mem0, c1mem, gslots_fr, gslots_r, gcursor.
  destruct HSF as (F18 & F28 & F70 & F78 & F80). destruct HSR as (R10 & R20 & R38 & R40 & R50 & R60).
  destruct HCU as (Cp & C88 & C90).
  repeat match goal with |- _ /\ _ => split end;
  first
  [ (apply (cs_slot_keep m m' _ _ Hk); [lia | assumption])
  | lia
  | lazymatch goal with
    | |- gsaved _ _ _ =>
      destruct HSV as (Hra & Hsj); unfold gsaved in *; cbn [cs_ms ms_mem mkst] in *; split;
      [ apply (cs_rd_keep m m' _ _); [|exact Hra]; intros j Hj; apply Hk; unfold cs_foot; lia
      | intros j Hj; apply (cs_rd_keep m m' _ _); [|exact (Hsj j Hj)]; intros q Hq; apply Hk; unfold cs_foot; lia ]
    | |- gshadow _ _ _ _ _ =>
      intros q Hq; cbn [cs_ms ms_mem mkst] in *;
      rewrite (cs_low_keep m m' _ Hk) by (unfold GSH_it in Hq; cbn [length app repeat] in Hq; lia);
      exact (HSH q Hq)
    | |- rdword _ _ = Some (gFL _ _) =>
      cbn [cs_ms ms_mem mkst] in *; apply (cs_rd_keep m m' _ _); [|exact HFL];
      intros j Hj; apply Hk; left; rewrite Hfb; lia
    | |- garr8 _ _ _ _ =>
      cbn [cs_ms ms_mem mkst] in *; intros q Hq; destruct (HIN q Hq) as [Hv Hb]; split; [|exact Hb];
      intros kk Hkk; assert (kk = 0)%nat by lia; subst kk;
      pose proof (Hv 0%nat ltac:(lia)) as Hv0; cbn [Z.of_nat] in Hv0 |- *; rewrite Z.add_0_r in Hv0 |- *;
      rewrite (mbyte_of_aview SEGS (w_H W3) (w_H W3) m m' (c_p cx + Z.of_nat q)); [exact Hv0|];
      apply Hk; left; rewrite length_map in Hq; unfold c_n in Hinp; lia
    | |- gprev _ _ _ _ _ =>
      intros q Hq; cbn [cs_ms ms_mem mkst] in *;
      rewrite (cs_low_keep m m' _ Hk) by (unfold GO_PREV, REG_SIZE in *; lia); exact (HPV q Hq)
    | |- greg _ _ _ _ _ _ _ =>
      destruct HRG as (Hin & Hl & Hb); split; [exact Hin|]; split; [exact Hl|]; intros q Hq; cbn [cs_ms ms_mem mkst] in *;
      rewrite (cs_low_keep m m' _ Hk) by (unfold REG_SIZE in *; lia); exact (Hb q Hq)
    | |- c1mac _ _ _ _ _ =>
      destruct HMC as (Hl & Hb); split; [exact Hl|]; intros q Hq; cbn [cs_ms ms_mem mkst] in *;
      rewrite (cs_low_keep m m' _ Hk) by (unfold GO_MAC in *; lia); exact (Hb q Hq)
    end ].
Qed.

Lemma cs_mem_kpx : forall m m', cs_mem m -> cs_kpx m m' -> cs_mem m'.
Proof.
  intros m m' (HM & H30) Hk. split.
  - apply (cs_mem0_kp m m' HM). intros a Ha. apply Hk. left. exact Ha.
  - unfold gslot in *. cbn [cs_ms ms_mem mkst] in *. apply (cs_rd_keep m m' _ _); [|exact H30].
    intros j Hj. apply Hk. right. lia.
Qed.

Hypothesis HBLK : gblk1 B cx ly3 S3 r.
Lemma cs_geo_of : forall mem md, cs_J mem md -> cs_geo.
Proof.
  intros mem md HJ.
  pose proof asan_consts as (Hac & _).
  pose proof HB as (HPRE & _ & _ & Hinp & _ & _ & _ & _ & _ & Hsp1 & _).
  pose proof HPRE as (HAR0 & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof HJ as (HAR3 & Hly3 & _).
  assert (Hfin : In (GB_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
  assert (Hfb : fs_frame_bytes GB_CID = 512) by (vm_compute; reflexivity).
  pose proof (frames_bounds _ _ LAWS _ _ _ _ _ GB_CID fp HAR3 Hfin) as (HF0 & HFc & HFia).
  destruct (frame_al64 SEGS B ly3 S3 W3 mem md GB_CID fp HAR3 Hfin) as (H64 & _ & _).
  rewrite HFA in HF0, HFc, HFia, H64. rewrite Hfb in HFc, HFia.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ r REG_SIZE HAR3 HRIN) as (Hr16 & Hr4096 & Hrceil & _).
  change (req_size REG_SIZE) with 288 in Hrceil.
  assert (Hin : c_n cx = 0 \/ (0 <= c_p cx /\ c_p cx + c_n cx <= alloc_ceiling)).
  { destruct Hinp as [(Hn0 & _) | (Hn & Hin)]; [left; exact Hn0 | right].
    assert (Hin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3))
      by (unfold gblk1 in HBLK; rewrite HBLK; apply in_or_app; left; exact Hin).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (_ & Hp4096 & Hpceil & _).
    pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrq]. lia. }
  assert (Hx : 0 <= spZ (c_regs cx) + -256) by (unfold GB_STK in *; lia).
  pose proof (Z.div_mod (spZ (c_regs cx) + -256) 32 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) + -256) 32 ltac:(lia)) as Hmp.
  unfold cs_geo. split; [exact Hal16|]. split; [unfold GB_STK in *; lia|].
  split; [rewrite Hsp1; lia|]. split; [rewrite Hsp1, Z.mul_comm; apply Z_mod_mult|].
  split; [lia|]. split; [lia|]. split; [exact HFia|]. split; [exact H64|].
  split; [unfold gSH, shadow_of_addr; reflexivity|].
  split; [exact Hr16|]. split; [lia|]. split; [lia | exact Hin].
Qed.

(* The frame's objects in scope (GSH_it): prev's 36 shadow bytes are 0, mac's shadow byte is 6. *)
Lemma cs_F8 : gF cx fp mod 8 = 0.
Proof.
  pose proof HGEO as (_ & _ & _ & _ & _ & _ & _ & Hal & _).
  pose proof (Z.div_mod (gF cx fp) 64 ltac:(lia)) as Hd. rewrite Hal, Z.add_0_r in Hd.
  rewrite Hd. replace (64 * (gF cx fp / 64)) with ((8 * (gF cx fp / 64)) * 8) by lia. apply Z.mod_mul. lia.
Qed.
Lemma cs_prev_ra : forall m o n, cs_mem0 m -> 0 <= o -> o + n <= REG_SIZE ->
  range_addressable (aview SEGS (w_H W3) m) SHADOW_OFF (gF cx fp + GO_PREV + o) n.
Proof.
  intros m o n HM Ho Hn x Hx.
  destruct HM as ((_ & Hsh & _) & _).
  pose proof cs_F8 as Hal8.
  unfold GO_PREV, REG_SIZE in *.
  assert (Hi : 8 <= (x - gF cx fp) / 8 < 44).
  { split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia. }
  exists 0. split; [|left; reflexivity].
  replace x with (gF cx fp + (x - gF cx fp)) by lia.
  rewrite shadow_of_addr_aligned_off by exact Hal8.
  change (shadow_of_addr SHADOW_OFF (gF cx fp)) with (gSH cx fp).
  pose proof (Hsh (Z.to_nat ((x - gF cx fp) / 8)) ltac:(rewrite gb_GSH_it_len; unfold GB_NSH; lia)) as H.
  cbn [cs_ms ms_mem mkst] in H.
  rewrite Z2Nat.id in H by lia. rewrite H. f_equal. apply gb_GSH_it_prev. lia.
Qed.
Lemma cs_mac_ra : forall m, cs_mem0 m -> range_addressable (aview SEGS (w_H W3) m) SHADOW_OFF (gF cx fp + GO_MAC) 6.
Proof.
  intros m HM x Hx.
  destruct HM as ((_ & Hsh & _) & _).
  pose proof HGEO as (_ & _ & _ & _ & _ & _ & _ & Hal & _).
  pose proof (Z.div_mod (gF cx fp) 64 ltac:(lia)) as Hd. rewrite Hal, Z.add_0_r in Hd.
  pose proof cs_F8 as Hal8.
  unfold GO_MAC in *.
  assert (Hq : (x - gF cx fp) / 8 = 4).
  { symmetry. apply (Z.div_unique (x - gF cx fp) 8 4 (x - gF cx fp - 32)); [left; lia | lia]. }
  assert (Hxm : x mod 8 = x - gF cx fp - 32).
  { symmetry. apply (Z.mod_unique x 8 (8 * (gF cx fp / 64) + 4) (x - gF cx fp - 32)); [left; lia | lia]. }
  exists 6. split; [|right; lia].
  replace x with (gF cx fp + (x - gF cx fp)) by lia.
  rewrite shadow_of_addr_aligned_off by exact Hal8. rewrite Hq.
  change (shadow_of_addr SHADOW_OFF (gF cx fp)) with (gSH cx fp).
  pose proof (Hsh 4%nat ltac:(rewrite gb_GSH_it_len; unfold GB_NSH; lia)) as H. cbn [cs_ms ms_mem mkst] in H.
  exact H.
Qed.

(* ---- the bcmp wrapper (abcmp_realizes) at a call from the realigned stack pointer ---- *)
Definition cs_src (memT : word -> option byte) (x : Z) (L : list byte) : Prop :=
  length L = 6%nat /\
  (forall j, 0 <= j < 6 -> aview SEGS (w_H W3) memT (x + j) = Some (bv_unsigned (nth (Z.to_nat j) L (Z_to_bv 8 0)))) /\
  0 <= x /\ x + 6 <= alloc_ceiling /\ amem_range x 6 /\
  range_addressable (aview SEGS (w_H W3) memT) SHADOW_OFF x 6 /\ shadow_hull_vis (aview SEGS (w_H W3) memT) x 6.

Lemma cs_bcmp : forall (regsT : bvmap 5 word) memT mdT x y Lx Ly,
  cs_J memT mdT ->
  spZ regsT = c_sp1 cx -> getr regsT 3 = getr (c_regs cx) 3 -> getr regsT 4 = getr (c_regs cx) 4 ->
  getr regsT 10 = w64 x -> getr regsT 11 = w64 y -> getr regsT 12 = w64 6 -> YK0s.ret_ok (getr regsT 1) ->
  cs_src memT x Lx -> cs_src memT y Ly ->
  SRr SEGS W3 (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA BS___interceptor_trampoline_bcmp)) memT (seg_rom SEGS)) mdT)
    (fun W2 c2 => W2 = W3 /\ exists regs2 mem2 md2,
       c2 = mkCfg (mkst regs2 (getr regsT 1) mem2 (seg_rom SEGS)) md2 /\ cs_J mem2 md2 /\
       aregs_preserved regsT regs2 /\ (bv_unsigned (getr regs2 10) = 0 <-> Lx = Ly) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx - 2 * ESTACK <= a < c_sp1 cx) ->
          aview SEGS (w_H W3) mem2 a = aview SEGS (w_H W3) memT a) /\
       (forall a, apresent (w_H W3) memT a -> apresent (w_H W3) mem2 a)).
Proof.
  intros regsT memT mdT x y Lx Ly HJ Hsp H3 H4 H10 H11 H12 Hra
    (Lx6 & Bx & Hx0 & Hx1 & Amx & Rax & Hvx) (Ly6 & By & Hy0 & Hy1 & Amy & Ray & Hvy).
  pose proof HGEO as (Hsp16 & Hspb & Hsp1 & Hsp32 & _).
  pose proof asan_consts as (C1 & _).
  pose proof HB as ((_ & _ & _ & Hgp & Htp & _) & _).
  assert (Hes : ESTACK = 4096) by reflexivity.
  assert (Ho16 : (c_sp1 cx - spZ (c_regs cx)) mod 16 = 0).
  { apply Z.mod_divide in Hsp16; [|lia]. apply Z.mod_divide in Hsp32; [|lia]. apply Z.mod_divide; [lia|].
    destruct Hsp16 as [p Hp]. destruct Hsp32 as [q Hq]. exists (2 * q - p). lia. }
  eapply SRr_mono.
  { eapply (aj_bcmp_at SEGS B LAWS pa_segs_low (SIGMA BS___interceptor_trampoline_bcmp) ABCMP W3 regsT memT
      GB_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(GB_CID, fp)] ly3 S3 mdT k
      x y 6 (c_sp1 cx - spZ (c_regs cx)) (getr regsT 1) HJ);
    first [ exact H10 | exact H11 | exact H12 | reflexivity | exact Hra | exact Ho16
          | (rewrite H3; exact Hgp) | (rewrite H4; exact Htp)
          | (rewrite Hsp; lia) | (unfold GB_STK; rewrite Hes; lia) | lia | exact Amx | exact Amy
          | exact Rax | exact Ray | (intros _; exact Hvx) | (intros _; exact Hvy)
          | (intros a Ha; replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) by lia;
             rewrite Hes; lia)
          | (intros a Ha; split;
             [ first [ (replace a with (x + (a - x)) by lia; rewrite (Bx (a - x)) by lia; discriminate)
                     | (replace a with (y + (a - y)) by lia; rewrite (By (a - y)) by lia; discriminate) ]
             | rewrite Hsp, Hes; lia ]) ]. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP & Hv & Hcmp & Hfr & Hpres2).
  split; [reflexivity|]. exists regs2, mem2, md2. split; [reflexivity|]. split; [exact HJ2|]. split; [exact HP|].
  split.
  { rewrite Hv. rewrite <- (cs_bytes_eq Lx Ly Lx6 Ly6). split.
    - intros H0 j Hj. assert (Hv0 : v = w64 0) by (apply bv_eq; rewrite H0; reflexivity).
      pose proof (proj1 Hcmp Hv0 j Hj) as Q. rewrite Bx, By in Q by lia. injection Q as Q. exact Q.
    - intros Q. assert (Hv0 : v = w64 0).
      { apply Hcmp. intros j Hj. rewrite Bx, By by lia. rewrite (Q j Hj). reflexivity. }
      rewrite Hv0. reflexivity. }
  split; [|exact Hpres2].
  intros a Ha Hna. apply Hfr; [exact Ha|].
  replace (spZ (c_regs cx) + (c_sp1 cx - spZ (c_regs cx))) with (c_sp1 cx) by lia. exact Hna.
Qed.

(* The three byte ranges the bcmp calls compare: mac, a row's MAC in prev, and ZERO. *)
Lemma cs_src_mac : forall memT mdT, cs_J memT mdT -> cs_mem0 memT -> cs_src memT (gF cx fp + GO_MAC) M.
Proof.
  intros memT mdT HJ HM.
  pose proof HGEO as (_ & _ & _ & _ & HF0 & HFc & HFia & _).
  pose proof HJ as (HAR & _).
  assert (Hfin : In (GB_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
  assert (Hfb : fs_frame_bytes GB_CID = 512) by (vm_compute; reflexivity).
  pose proof HM as (_ & _ & _ & _ & _ & _ & (HL & Hb) & _). cbn [cs_ms ms_mem mkst] in Hb.
  unfold GO_MAC in *.
  split; [exact HL|]. split; [exact Hb|]. split; [lia|]. split; [lia|].
  split; [exact (amem_range_sub_app (gF cx fp) 512 (gF cx fp + 32) 6 HFia HFc ltac:(lia) ltac:(lia) ltac:(lia))|].
  split; [exact (cs_mac_ra memT HM)|].
  apply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W3 memT mdT GB_CID fp _ _ HAR Hfin); rewrite ?HFA, ?Hfb; lia.
Qed.
Lemma cs_src_row : forall memT mdT j, cs_J memT mdT -> cs_mem0 memT -> 0 <= j < Boxreg.bx_n bs ->
  cs_src memT (gF cx fp + GO_PREV + 56 * j) (Boxreg.bx_mac bs j).
Proof.
  intros memT mdT j HJ HM Hj.
  pose proof HGEO as (_ & _ & _ & _ & HF0 & HFc & HFia & _).
  pose proof HJ as (HAR & _).
  pose proof (LLVMFuzzerTestOneInput_case1.c1_inv_n bs HINV) as Hn.
  pose proof (LLVMFuzzerTestOneInput_case1.c1_inv_len bs HINV) as Hl.
  assert (Hfin : In (GB_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
  assert (Hfb : fs_frame_bytes GB_CID = 512) by (vm_compute; reflexivity).
  pose proof HM as ((_ & _ & _ & _ & _ & HPV) & _). unfold gprev in HPV. cbn [cs_ms ms_mem mkst] in HPV.
  unfold GO_PREV, REG_SIZE in *.
  split; [apply LLVMFuzzerTestOneInput_case1.c1_mac_len; [exact Hl | lia]|].
  split.
  { intros q Hq. rewrite (cs_mac_nth bs j q Hl ltac:(lia) Hq).
    replace (gF cx fp + 64 + 56 * j + q) with (gF cx fp + 64 + (56 * j + q)) by lia. apply HPV. lia. }
  split; [lia|]. split; [lia|].
  split; [exact (amem_range_sub_app (gF cx fp) 512 (gF cx fp + 64 + 56 * j) 6 HFia HFc ltac:(lia) ltac:(lia) ltac:(lia))|].
  split; [exact (cs_prev_ra memT (56 * j) 6 HM ltac:(lia) ltac:(unfold REG_SIZE; lia))|].
  apply (shadow_hull_vis_of_frame SEGS B LAWS ly3 S3 W3 memT mdT GB_CID fp _ _ HAR Hfin); rewrite ?HFA, ?Hfb; lia.
Qed.
Lemma cs_src_zero : forall memT mdT, cs_J memT mdT -> cs_src memT (VAL (A_OBJ 6)) Boxreg.zero6.
Proof.
  intros memT mdT HJ.
  assert (HM6 : IMG_LO + 64 <= VAL (A_OBJ 6) /\ VAL (A_OBJ 6) + 6 + 64 <= IMG_HI)
    by (rewrite Forall_forall in HMRG; exact (HMRG (VAL (A_OBJ 6), 6) ltac:(unfold BX_G; cbn [In]; tauto))).
  unfold IMG_HI in HM6.
  pose proof asan_consts as (C1 & _).
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & HRO & _).
  pose proof (pa_val_range (A_OBJ 6)) as Hv6.
  split; [reflexivity|].
  split.
  { intros j Hj. destruct (HZERO j ltac:(cbn; lia)) as (Hrom & Hown & Herr & Hb).
    rewrite (F3 (VAL (A_OBJ 6) + j)); [| destruct Hrom as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]
      | exact Hown | exact Herr | apply fp_spares_closed; exact sink_closed_nil].
    rewrite (HRO (VAL (A_OBJ 6) + j)); [| left; exact Hrom | exact Hown | exact Herr].
    rewrite Hb. f_equal.
    rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; cbn; lia).
    rewrite map_nth. reflexivity. }
  split; [lia|]. split; [lia|].
  split; [unfold amem_range, kLowMemEnd; left; lia|].
  exact (ro_read_ok_glob SEGS B BX_G ly3 S3 W3 memT mdT (VAL (A_OBJ 6)) 6 (VAL (A_OBJ 6)) 6 HGLOB
    ltac:(unfold BX_G; cbn [In]; tauto) HISV HAR ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold IMG_HI; lia)).
Qed.

(* What a call of the wrapper and a run of the engine keep of the piece's memory. *)
Lemma cs_footx_rng : forall a, cs_footx a -> 0 <= a < 2 ^ 64 /\ ~ (c_sp1 cx - 2 * ESTACK <= a < c_sp1 cx).
Proof.
  intros a Ha. pose proof HGEO as (_ & Hsp & Hsp1 & _). pose proof asan_consts as (C1 & _).
  assert (Hes : ESTACK = 4096) by reflexivity. unfold cs_footx, cs_foot in Ha. lia.
Qed.
Lemma cs_kpx_bcmp : forall m m2,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (c_sp1 cx - 2 * ESTACK <= a < c_sp1 cx) ->
     aview SEGS (w_H W3) m2 a = aview SEGS (w_H W3) m a) -> cs_kpx m m2.
Proof. intros m m2 Hk a Ha. destruct (cs_footx_rng a Ha) as [H1 H2]. exact (Hk a H1 H2). Qed.
Lemma cs_kpx_frame : forall E rs m m',
  frame_of E rs (mrestrict (w_H W3) m) (mrestrict (w_H W3) m') -> (forall a, cs_footx a -> ~ in_wrange E rs a) ->
  cs_kpx m m'.
Proof.
  intros E rs m m' HF Hn a Ha. destruct (cs_footx_rng a Ha) as [H1 _].
  apply aview_eq_of. apply HF. rewrite unsigned_lit_small by exact H1. exact (Hn a Ha).
Qed.
Lemma cs_kp_frame : forall E rs m m',
  frame_of E rs (mrestrict (w_H W3) m) (mrestrict (w_H W3) m') -> (forall a, cs_foot a -> ~ in_wrange E rs a) ->
  cs_kp m m'.
Proof.
  intros E rs m m' HF Hn a Ha. assert (Hx : cs_footx a) by (left; exact Ha). destruct (cs_footx_rng a Hx) as [H1 _].
  apply aview_eq_of. apply HF. rewrite unsigned_lit_small by exact H1. exact (Hn a Ha).
Qed.
Lemma cs_kp_of_kpx : forall m m', cs_kpx m m' -> cs_kp m m'.
Proof. intros m m' H a Ha. apply H. left. exact Ha. Qed.

(* ---- the head of the scan (0x80714) as the engine's symbolic state ---- *)
(* Atoms 0 .. 31: the registers; 32: mac (the word slot 0x70 holds); 33: nch (slot 0x58); 34: the nch field of
   row j (prev.box[j].nch, the word at s7 + 12). s3 = prev + 56 j + 12 is one shadow entry (prev's shadow is 0). *)
Definition cs_EL (regs : bvmap 5 word) (j : Z) : env :=
  Eimg (Ereg regs [Z_to_bv 64 (gF cx fp + GO_MAC); Z_to_bv 64 nch; Z_to_bv 64 (Boxreg.bx_nch bs j)]).

Lemma cs_nchj : forall j, 0 <= j < Boxreg.bx_n bs -> 2 <= Boxreg.bx_nch bs j <= 40.
Proof.
  intros j Hj. destruct HINV as ((_ & _ & HB2 & HB3 & _) & _).
  destruct (Boxreg.B3_bounds bs j HB2 HB3 Hj) as (_ & H & _). exact H.
Qed.

Lemma cs_seatL : forall regs mem j,
  0 <= j < Boxreg.bx_n bs -> cs_mem0 mem ->
  getr regs 9 = w64 (c_sp1 cx) -> getr regs 18 = w64 SHADOW_OFF ->
  getr regs 19 = w64 (gF cx fp + GO_PREV + 56 * j + 12) -> getr regs 23 = w64 (gF cx fp + GO_PREV + 56 * j) ->
  st_ok_pi SEGS VAL (cs_EL regs j) cs_ssL
    (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + PC1_scan)) mem (seg_rom SEGS))) /\
  sh_ok SEGS cs_Bx cs_SHL (cs_EL regs j) (mrestrict (w_H W3) mem).
Proof.
  intros regs mem j Hj HM G9 G18 G19 G23.
  pose proof HGEO as (Hsp16 & Hsp & Hsp1 & Hsp32 & HF0 & HFc & HFia & HF64 & ESH & _).
  pose proof asan_consts as (C1 & _).
  pose proof (LLVMFuzzerTestOneInput_case1.c1_inv_n bs HINV) as Hn.
  pose proof (LLVMFuzzerTestOneInput_case1.c1_inv_len bs HINV) as Hl.
  pose proof (cs_nchj j Hj) as Hnj.
  pose proof (Z.div_mod (gF cx fp) 64 ltac:(lia)) as HFd. rewrite HF64, Z.add_0_r in HFd.
  pose proof HM as ((_ & _ & _ & _ & (_ & _ & S70 & _) & HPV) & _ & _ & _ & _ & _ & _ & S58).
  unfold gslot in S70, S58. cbn [cs_ms ms_mem mkst] in S70, S58. unfold gprev in HPV. cbn [cs_ms ms_mem mkst] in HPV.
  set (E := cs_EL regs j).
  assert (EE : forall q (rg : bv 5), Z.of_nat q = bv_unsigned rg -> ew E q = getr regs rg).
  { intros q rg Hq. unfold E, cs_EL. pose proof (bv_unsigned_in_range 5 rg) as R. change (bv_modulus 5) with 32 in R.
    rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hq. }
  assert (EX : forall q, (q < 3)%nat -> ew E (32 + q)%nat =
    nth q [Z_to_bv 64 (gF cx fp + GO_MAC); Z_to_bv 64 nch; Z_to_bv 64 (Boxreg.bx_nch bs j)] (Z_to_bv 64 0)).
  { intros q Hq. unfold E, cs_EL. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
  assert (F9 : ew E 9 = Z_to_bv 64 (c_sp1 cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact G9).
  assert (F18 : ew E 18 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 18%nat 18%bv eq_refl); exact G18).
  assert (F19 : ew E 19 = Z_to_bv 64 (gF cx fp + GO_PREV + 56 * j + 12)) by (rewrite (EE 19%nat 19%bv eq_refl); exact G19).
  assert (F23 : ew E 23 = Z_to_bv 64 (gF cx fp + GO_PREV + 56 * j)) by (rewrite (EE 23%nat 23%bv eq_refl); exact G23).
  assert (F32 : ew E 32 = Z_to_bv 64 (gF cx fp + GO_MAC)) by exact (EX 0%nat ltac:(lia)).
  assert (F33 : ew E 33 = Z_to_bv 64 nch) by exact (EX 1%nat ltac:(lia)).
  assert (F34 : ew E 34 = Z_to_bv 64 (Boxreg.bx_nch bs j)) by exact (EX 2%nat ltac:(lia)).
  unfold GO_PREV, GO_MAC, REG_SIZE in *.
  assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite F9; apply unsigned_lit_small; lia).
  assert (U23 : bv_unsigned (ew E 23) = gF cx fp + 64 + 56 * j) by (rewrite F23; apply unsigned_lit_small; lia).
  split.
  - rewrite restrict_mkst_fx. unfold cs_ssL. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold cs_RLsp, cs_RLrow. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      * rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        -- apply (chunk_ok_val SEGS E _ (c_sp1 cx) 0x58 8 (SOff 33 0) nch (cs_den0 E 33 nch F33));
             [cbn [Z.of_N]; lia | cbn [Z.of_N]; lia | apply (val_mem_of_rdword SEGS (w_H W3) mem); exact S58].
        -- apply (chunk_ok_val SEGS E _ (c_sp1 cx) 0x70 8 (SOff 32 0) (gF cx fp + 32) (cs_den0 E 32 _ F32));
             [cbn [Z.of_N]; lia | cbn [Z.of_N]; lia | apply (val_mem_of_rdword SEGS (w_H W3) mem); exact S70].
      * rewrite U23. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ (gF cx fp + 64 + 56 * j) 12 4 (SOff 34 0) (Boxreg.bx_nch bs j) (cs_den0 E 34 _ F34));
          [cbn [Z.of_N]; lia | cbn [Z.of_N]; lia |].
        unfold Boxreg.bx_nch. rewrite (cs_rd4_nu bs (56 * j + 12) Hl ltac:(lia) ltac:(lia)) by (unfold Boxreg.bx_nch in Hnj; lia).
        replace (gF cx fp + 64 + 56 * j + 12) with (gF cx fp + 64 + (56 * j + 12)) by lia.
        apply (cs_nu_val_mem (w_H W3) mem (gF cx fp + 64) bs (56 * j + 12)); [lia | unfold REG_SIZE; lia | exact HPV].
    + apply pairwise_disjoint_of_extents. unfold cs_RLsp, cs_RLrow, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U23.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
    + split; [|split; exact I].
      cbn [cs_FL f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite F9, F18, F19, F23, F32, F33, F34.
      rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 5) with 32. change (2 ^ 3) with 8. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold cs_SB, SHADOW_OFF.
      repeat match goal with |- _ /\ _ => split end; try exact I; try lia; rewrite HFd;
        first [ (replace (64 * (gF cx fp / 64) + 64 + 56 * j + 12) with ((16 * (gF cx fp / 64) + 19 + 14 * j) * 4) by lia;
                 apply Z.mod_mul; lia)
              | (replace (64 * (gF cx fp / 64) + 64 + 56 * j) with ((8 * (gF cx fp / 64) + 8 + 7 * j) * 8) by lia;
                 apply Z.mod_mul; lia)
              | (replace (64 * (gF cx fp / 64) + 32) with ((8 * (gF cx fp / 64) + 4) * 8) by lia;
                 apply Z.mod_mul; lia) ].
  - unfold sh_ok, cs_SHL. apply Forall_cons; [|apply Forall_nil].
    apply (shent_ok_of_range SEGS (w_H W3) mem E cs_Bx 19 (gF cx fp + 64 + (56 * j + 12)) 8
             (gF cx fp + 64 + 56 * j + 12) 0 8).
    + exact (cs_prev_ra mem (56 * j + 12) 8 HM ltac:(lia) ltac:(unfold REG_SIZE; lia)).
    + unfold cs_Bx. rewrite (U_atom E 18 SHADOW_OFF F18) by (unfold SHADOW_OFF; lia). reflexivity.
    + rewrite (U_atom E 19 _ F19) by lia. reflexivity.
    + lia.
    + lia.
    + intros x Hx. cbn [Z.min Z.max] in Hx. revert HFia HFc Hx Hj Hn HF0. clear.
      unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia.
Qed.

(* ---- the landing at 0x807a8: the cut C1_dec ---- *)
Hypothesis HDEC : gb_from B MT POST (C1_dec B MT i).
Hypothesis HMO : mo_le MT (c_S cx) S3 acc.
Hypothesis Hi : 0 <= i < 64.
Hypothesis Hk : k <= 1 + 2 * i.
Hypothesis Hacc : acc <= GB_A MT i.

Lemma cs_land_dec : forall v h u (regs : bvmap 5 word) mem md,
  cs_J mem md -> cs_mem mem -> (v = 0 <-> M = Boxreg.zero6) -> 0 <= v < 2 ^ 64 ->
  LLVMFuzzerTestOneInput_case1.c1_sh bs M v (Boxreg.bx_n bs) h ->
  LLVMFuzzerTestOneInput_case1.c1_su bs nch (Boxreg.bx_n bs) u -> -1 <= h <= 4 -> -1 <= u <= 4 ->
  getr regs 2 = w64 (c_sp1 cx) -> getr regs 8 = w64 (spZ (c_regs cx)) -> getr regs 9 = w64 (c_sp1 cx) ->
  getr regs 3 = getr (c_regs cx) 3 -> getr regs 4 = getr (c_regs cx) 4 ->
  getr regs 18 = w64 SHADOW_OFF -> getr regs 24 = w64 (gSH cx fp) -> getr regs 20 = w64 r ->
  getr regs 22 = w64 h -> getr regs 26 = w64 u -> getr regs 27 = w64 v ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + PC1_dec)) mem (seg_rom SEGS)) md) (POST cx).
Proof.
  intros v h u regs mem md HJ (HM & H30) HV HVR HSH HSU Hh Hu G2 G8 G9 G3 G4 G18 G24 G20 G22 G26 G27.
  pose proof HM as (HC1 & HSR & HCU & H68 & H48 & HRG & HMC & H58).
  eapply HDEC; [exact HB | exact HJ | exact HFR | exact HMO |].
  exists r, bs, pos, M, nch, h, u, v.
  split; [unfold c1_core; repeat (split; [reflexivity|]); repeat (split; [assumption|]); assumption|].
  split; [unfold c1_base; repeat (split; [assumption|]); exact G20|].
  split; [exact HRG|]. split; [exact HMC|]. split; [exact HNCH|]. split; [exact H58|]. split; [exact H30|].
  split; [exact HV|]. split; [exact HVR|]. split; [exact HSH|]. split; [exact HSU|].
  split; [exact Hh|]. split; [exact Hu|]. split; [exact G22|]. split; [exact G26 | exact G27].
Qed.

(* ---- the scan: one turn of the loop 0x80714 .. 0x80790 per row ---- *)
Definition cs_inv (v j h u : Z) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  0 <= j < Boxreg.bx_n bs /\ -1 <= h < j /\ -1 <= u < j /\
  LLVMFuzzerTestOneInput_case1.c1_sh bs M v j h /\ LLVMFuzzerTestOneInput_case1.c1_su bs nch j u /\
  getr regs 2 = w64 (c_sp1 cx) /\ getr regs 8 = w64 (spZ (c_regs cx)) /\ getr regs 9 = w64 (c_sp1 cx) /\
  getr regs 3 = getr (c_regs cx) 3 /\ getr regs 4 = getr (c_regs cx) 4 /\
  getr regs 18 = w64 SHADOW_OFF /\ getr regs 24 = w64 (gSH cx fp) /\ getr regs 20 = w64 r /\
  getr regs 19 = w64 (gF cx fp + GO_PREV + 56 * j + 12) /\ getr regs 21 = w64 j /\ getr regs 22 = w64 h /\
  getr regs 23 = w64 (gF cx fp + GO_PREV + 56 * j) /\ getr regs 25 = w64 (Boxreg.bx_n bs - j) /\
  getr regs 26 = w64 u /\ getr regs 27 = w64 v /\
  cs_J mem md /\ cs_mem mem.

Let cs_RUN := paj_run B LAWS.
Let cs_RUNTO := paj_run_to B LAWS.
Let cs_BR := paj_branch (PI := PI).

Lemma cs_kpx_frame_ro : forall E rs m m',
  frame_of E rs (mrestrict (w_H W3) m) (mrestrict (w_H W3) m') ->
  forallb (fun r0 => YP09.r_whi r0 <=? YP09.r_wlo r0) rs = true -> cs_kpx m m'.
Proof.
  intros E rs m m' HF Hw. apply (cs_kpx_frame E rs m m' HF). intros a _ (r0 & Hin & Hb).
  rewrite forallb_forall in Hw. specialize (Hw r0 Hin). apply Z.leb_le in Hw. lia.
Qed.
Lemma cs_shokL : forall E m j, cs_mem0 m -> 0 <= j < Boxreg.bx_n bs ->
  ew E 18 = Z_to_bv 64 SHADOW_OFF -> ew E 19 = Z_to_bv 64 (gF cx fp + GO_PREV + 56 * j + 12) ->
  sh_ok SEGS cs_Bx cs_SHL E (mrestrict (w_H W3) m).
Proof.
  intros E m j HM Hj F18 F19.
  pose proof HGEO as (_ & _ & _ & _ & HF0 & HFc & HFia & _).
  pose proof (LLVMFuzzerTestOneInput_case1.c1_inv_n bs HINV) as Hn.
  pose proof asan_consts as (C1 & _).
  unfold GO_PREV in *.
  unfold sh_ok, cs_SHL. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W3) m E cs_Bx 19 (gF cx fp + 64 + (56 * j + 12)) 8 (gF cx fp + 64 + 56 * j + 12) 0 8).
  - exact (cs_prev_ra m (56 * j + 12) 8 HM ltac:(lia) ltac:(unfold REG_SIZE; lia)).
  - unfold cs_Bx. rewrite (U_atom E 18 SHADOW_OFF F18) by (unfold SHADOW_OFF; lia). reflexivity.
  - rewrite (U_atom E 19 _ F19) by lia. reflexivity.
  - lia.
  - lia.
  - intros x Hx. cbn [Z.min Z.max] in Hx. revert HFia HFc Hx Hj Hn HF0. clear.
    unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia.
Qed.

Local Ltac cs_zbool :=
  repeat match goal with
  | H : negb _ = true |- _ => apply (proj1 (Bool.negb_true_iff _)) in H
  | H : negb _ = false |- _ => apply (proj1 (Bool.negb_false_iff _)) in H
  | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
  | H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
  | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
  | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
  | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
  | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
  end.
Local Ltac cs_U_in H :=
  repeat match type of H with
  | context [U ?Ex (SOff ?n 0)] =>
      match goal with F : ew Ex n = Z_to_bv 64 ?v |- _ => rewrite (U_atom Ex n v F) in H by lia end
  | context [U ?Ex (SOff ?n ?x)] =>
      match goal with F : ew Ex n = Z_to_bv 64 ?v |- _ => rewrite (U_atom_off Ex n v x F) in H by lia end
  | context [U ?Ex (SLit ?z)] => rewrite (U_lit Ex z) in H by lia
  end.
(* The branch condition of a path as a fact on Z. *)
Local Ltac cs_bfact :=
  lazymatch goal with Hc : branch_taken ?c (sv_denot ?Ex ?a) (sv_denot ?Ex ?b) = _ |- _ =>
    lazymatch c with
    | BC_GE =>
        lazymatch a with
        | SOff ?n 0 => match goal with F : ew Ex n = Z_to_bv 64 ?v |- _ => rewrite (cs_bge Ex n v F) in Hc by lia end
        | SLit 0 => lazymatch b with SOff ?n 0 =>
            match goal with F : ew Ex n = Z_to_bv 64 ?v |- _ => rewrite (cs_ble Ex n v F) in Hc by lia end end
        end
    | BC_EQ => rewrite branch_eq_U in Hc; cs_U_in Hc
    | BC_NE => rewrite branch_ne_U in Hc; cs_U_in Hc
    end; cs_zbool
  end.
(* The regions after a run that writes nothing: the piece's memory is kept. *)
Local Ltac cs_upd :=
  lazymatch goal with
  | HFr : frame_of ?Ex ?rs (mrestrict _ ?m) (mrestrict _ ?m'), HM : cs_mem ?m |- _ =>
      let HM2 := fresh "HM" in
      assert (HM2 : cs_mem m') by (apply (cs_mem_kpx _ _ HM); apply (cs_kpx_frame_ro Ex rs _ _ HFr);
                                   vm_compute; reflexivity);
      clear HM; rename HM2 into HM
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Local Ltac cs_awr_ro :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
(* A register of the symbolic state, as the invariant states it. *)
Local Ltac cs_reg HS :=
  lazymatch goal with |- getr _ ?rr = _ =>
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ss (restrict ?H ?ms) =>
    let R := fresh "R" in pose proof (st_ok_pi_restrict_reg H Ex ss ms rr HS) as R;
    let e := eval vm_compute in (sr_get (ss_regs ss) rr) in change (sr_get (ss_regs ss) rr) with e in R;
    cbn [ms_regs mkst] in R |- *; rewrite R; clear R;
    lazymatch e with
    | SOff ?n 0 => match goal with F : ew Ex n = Z_to_bv 64 ?v |- _ => rewrite (cs_den0 Ex n v F) end
    | SOff ?n ?x => match goal with F : ew Ex n = Z_to_bv 64 ?v |- _ => rewrite (cs_den_off Ex n v x F) by lia end
    | SLit ?z => cbn [sv_denot]
    | SAluw ALU_ADD (SOff ?n 0) (SLit 1) =>
        match goal with F : ew Ex n = Z_to_bv 64 ?v |- _ => rewrite (cs_addiw Ex n v F) by lia end
    end;
    first [ reflexivity | (rewrite Z_to_bv_bv_unsigned; reflexivity)
          | (unfold w64; apply Z_to_bv64_eq_mod; first [reflexivity | f_equal; lia]) ]
  end end.

Local Ltac cs_Fall :=
  repeat match goal with |- context [ew ?Ex ?n] =>
    match goal with F : ew Ex n = _ |- _ => rewrite F end end.
Local Ltac cs_restate OLD :=
  lazymatch type of OLD with forall q, (q < ?K)%nat -> ew ?En q = ew ?Eo q =>
  repeat match goal with
  | F : ew Eo ?n = Z_to_bv 64 ?v |- _ =>
      lazymatch goal with
      | _ : ew En n = Z_to_bv 64 v |- _ => fail
      | _ => let F' := fresh "F" in assert (F' : ew En n = Z_to_bv 64 v) by (rewrite OLD by (cbv; lia); exact F)
      end
  end end.
Local Ltac cs_mac_eq :=
  lazymatch goal with H : _ <-> ?g |- ?g => apply H; lia end.
Local Ltac cs_mac_neq :=
  lazymatch goal with |- ?a <> ?b => lazymatch goal with H : _ <-> a = b |- _ => intros X; apply H in X; lia end end.
Local Ltac cs_sh := first
  [ (apply LLVMFuzzerTestOneInput_case1.c1_sh_keep; [assumption | lia])
  | (apply LLVMFuzzerTestOneInput_case1.c1_sh_v0; lia)
  | (apply LLVMFuzzerTestOneInput_case1.c1_sh_hit; [assumption | lia | lia | cs_mac_eq])
  | (apply LLVMFuzzerTestOneInput_case1.c1_sh_miss; [assumption | lia | cs_mac_neq]) ].
Local Ltac cs_su := first
  [ (apply LLVMFuzzerTestOneInput_case1.c1_su_keep; [assumption | lia])
  | (apply LLVMFuzzerTestOneInput_case1.c1_su_hit; [assumption | lia | cs_mac_eq | lia])
  | (apply LLVMFuzzerTestOneInput_case1.c1_su_miss; [assumption | lia |];
     let X := fresh "X" in let Y := fresh "Y" in intros (X & Y);
     first [ lia | lazymatch type of X with ?a = ?b => lazymatch goal with H : _ <-> a = b |- _ => apply H in X; lia end end ]) ].
Local Ltac cs_m1 :=
  repeat match goal with Hh : -1 <= ?x < _, Hx : ?x < 0 |- _ => assert (x = -1) by lia; subst x end.
Local Ltac cs_run :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
    paj_run_tok cs_RUN HS HJ SHOK cs_Bspan; [cs_awr_ro |]; cs_upd;
    repeat match goal with H1 : img_env _ _ ?Ex, H2 : img_env _ _ ?Ex |- _ => clear H2 end;
    lazymatch goal with HJ' : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => repeat rewrite wvb_collapse in HJ' end
  end.
Local Ltac cs_run_to stop :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
    paj_run_to_tok cs_RUNTO HS HJ SHOK cs_Bspan stop; [cs_awr_ro |]; cs_upd;
    repeat match goal with H1 : img_env _ _ ?Ex, H2 : img_env _ _ ?Ex |- _ => clear H2 end;
    lazymatch goal with HJ' : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => repeat rewrite wvb_collapse in HJ' end
  end.
Local Ltac cs_val Ex e :=
  lazymatch e with
  | SOff ?n 0 => lazymatch goal with F : ew Ex n = Z_to_bv 64 ?v |- _ => v end
  | SLit 18446744073709551615 => constr:(-1)
  end.

(* The call of the bcmp wrapper at 0x80728 (row j's MAC against mac) or 0x80750 (row j's MAC against ZERO). *)
Local Ltac cs_kept Ex m m2 HK HPR :=
  lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some ?n) _ _ _ _ _) =>
    match goal with F : ew Ex n = Z_to_bv 64 ?b |- _ =>
      apply (@YC4b.region_kept_aview SEGS Ex (w_H W3) m m2 n b);
      [rewrite F; apply unsigned_lit_small; lia | intros a Ha; apply HK; [lia | lia] | exact HPR] end end.
Local Ltac cs_after_call HS Ex msc kk k4 regs2 mem2 HP2 HK2 HPR2 HEIx :=
  let HS2 := fresh "HS" in
  jafter_call_keep_hi HS kk regs2 (mrestrict (w_H W3) mem2) HP2 [0%nat; 1%nat] HS2;
  match type of HS2 with ?Q -> _ =>
    let HQ := fresh "HQ" in
    assert (HQ : Q);
    [ cbn [ms_mem restrict mkst]; repeat apply Forall_cons; try apply Forall_nil; cs_kept Ex (ms_mem msc) mem2 HK2 HPR2
    | specialize (HS2 HQ); clear HQ ] end;
  rewrite <- restrict_mkst_fx in HS2; clear HS; rename HS2 into HS;
  let E2 := fresh "E" in let HE2 := fresh "HE" in
  remember (havoc Ex kk (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS;
  let HEI2 := fresh "HEI" in
  assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc_hi; [exact HEIx | cbv; lia]);
  let OLD := fresh "OLD" in
  assert (OLD : forall q, (q < kk)%nat -> ew E2 q = ew Ex q)
    by (intros q Hq; rewrite HE2; apply YN3v.ew_havoc_old; exact Hq);
  let FA := fresh "F" in
  assert (FA : ew E2 k4 = Z_to_bv 64 (bv_unsigned (getr regs2 10)))
    by (rewrite HE2; change k4 with (kk + 4)%nat;
        rewrite (YN3v.ew_havoc_new Ex kk (map (getr regs2) CLOB) 4 (Z_to_bv 64 0)) by (cbv; lia);
        cbn [nth map]; rewrite Z_to_bv_bv_unsigned; reflexivity);
  cs_restate OLD; clear HE2 OLD;
  repeat match goal with Fo : ew Ex _ = _ |- _ => clear Fo end; clear HEIx;
  let RR := fresh "RR" in
  assert (RR : 0 <= bv_unsigned (getr regs2 10) < 2 ^ 64)
    by (pose proof (bv_unsigned_in_range 64 (getr regs2 10)) as RR0; change (bv_modulus 64) with (2 ^ 64) in RR0; exact RR0);
  lazymatch goal with HM : cs_mem _ |- _ =>
    let HM2 := fresh "HM" in
    assert (HM2 : cs_mem mem2) by (apply (cs_mem_kpx _ _ HM); apply cs_kpx_bcmp; exact HK2);
    clear HM; rename HM2 into HM end;
  clear HP2 HK2 HPR2.
Local Ltac cs_callL :=
  lazymatch goal with
  | HS : st_ok _ ?Ex ?ssc (restrict (w_H W3) ?msc), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    HM : cs_mem _, HEIx : img_env _ _ ?Ex, Hj : 0 <= ?j < Boxreg.bx_n bs |- _ =>
    let retk := eval vm_compute in (match sr_get (ss_regs ssc) 1 with SOff _ z => z | _ => 0 end) in
    let kk := eval vm_compute in (run_K A_LIM cs_Bx cs_SHL ssc) in
    let k4 := eval vm_compute in (kk + 4)%nat in
    pmkst HS;
    let Ra0 := fresh "Ra" in let Ra1 := fresh "Ra" in let Ra2 := fresh "Ra" in let Rra := fresh "Rra" in
    let Rsp := fresh "Rsp" in let Rgp := fresh "Rgp" in let Rtp := fresh "Rtp" in
    prreg HS (10%bv : bv 5) Ra0; prreg HS (11%bv : bv 5) Ra1; prreg HS (12%bv : bv 5) Ra2;
    prreg HS (1%bv : bv 5) Rra; prreg HS (2%bv : bv 5) Rsp; prreg HS (3%bv : bv 5) Rgp; prreg HS (4%bv : bv 5) Rtp;
    eapply SRr_bind;
    [ lazymatch retk with
      | 2016 => eapply (cs_bcmp (ms_regs msc) (ms_mem msc) _ (gF cx fp + 64 + 56 * j) (gF cx fp + 32)
                          (Boxreg.bx_mac bs j) M HJ)
      | 2056 => eapply (cs_bcmp (ms_regs msc) (ms_mem msc) _ (gF cx fp + 64 + 56 * j) (VAL (A_OBJ 6))
                          (Boxreg.bx_mac bs j) Boxreg.zero6 HJ)
      end;
      first
      [ (unfold spZ at 1; rewrite Rsp; cs_Fall; rewrite unsigned_lit_small by lia; reflexivity)
      | (rewrite Rgp; cs_Fall; rewrite Z_to_bv_bv_unsigned; reflexivity)
      | (rewrite Rtp; cs_Fall; rewrite Z_to_bv_bv_unsigned; reflexivity)
      | (rewrite Ra0; cs_Fall; reflexivity)
      | (rewrite Ra1; cs_Fall; reflexivity)
      | (rewrite Ra1; rewrite (img_env_atomP Ex 247 HEIx ltac:(cbv; lia)); reflexivity)
      | (rewrite Ra2; reflexivity)
      | (rewrite Rra; apply ret_ok_codeptr_v; [lia | reflexivity])
      | exact (cs_src_row (ms_mem msc) _ j HJ (proj1 HM) Hj)
      | exact (cs_src_mac (ms_mem msc) _ HJ (proj1 HM))
      | exact (cs_src_zero (ms_mem msc) _ HJ) ]
    | ];
    cbv beta;
    let W2 := fresh "W" in let c2 := fresh "c" in let regs2 := fresh "regs" in let mem2 := fresh "mem" in
    let md2 := fresh "md" in let HJ2 := fresh "HJ" in let HP2 := fresh "HP" in let HCMP := fresh "HCMP" in
    let HK2 := fresh "HK" in let HPR2 := fresh "HPR" in
    intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HCMP & HK2 & HPR2);
    cs_after_call HS Ex msc kk k4 regs2 mem2 HP2 HK2 HPR2 HEIx;
    rewrite Rra; clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp;
    unfold cs_J in HJ2; clear HJ; rename HJ2 into HJ;
    lazymatch goal with SH0 : sh_ok _ _ _ _ _ |- _ => clear SH0 end;
    lazymatch goal with HS' : st_ok_pi _ _ ?E2 _ _, HM' : cs_mem _ |- _ =>
      let SH2 := fresh "SHOK" in
      assert (SH2 : sh_ok SEGS cs_Bx cs_SHL E2 (mrestrict (w_H W3) mem2))
        by (apply (cs_shokL E2 mem2 j (proj1 HM') Hj); assumption) end
  end.
Local Ltac cs_land_scan :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?Ex ?ss (restrict _ ?ms), Hj : 0 <= ?j < Boxreg.bx_n bs |- _ =>
    let e22 := eval vm_compute in (sr_get (ss_regs ss) (22%bv : bv 5)) in
    let e26 := eval vm_compute in (sr_get (ss_regs ss) (26%bv : bv 5)) in
    let h2 := cs_val Ex e22 in let u2 := cs_val Ex e26 in
    pmkst HS;
    lazymatch goal with IH : forall (j0 h0 u0 : Z) (regs0 : bvmap 5 word) mem0 md0, _ |- _ =>
      apply (IH (j + 1) h2 u2 (ms_regs ms) (ms_mem ms) _); [lia|] end;
    unfold cs_inv, GO_PREV, GO_MAC;
    split; [lia|]; split; [lia|]; split; [lia|]; split; [cs_sh|]; split; [cs_su|];
    do 15 (split; [cs_reg HS|]);
    lazymatch goal with HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, HM : cs_mem _ |- _ => split; [exact HJ | exact HM] end
  end.
Local Ltac cs_land_end :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?Ex ?ss (restrict _ ?ms), Hj : 0 <= ?j < Boxreg.bx_n bs,
    HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, HM : cs_mem _ |- _ =>
    let e22 := eval vm_compute in (sr_get (ss_regs ss) (22%bv : bv 5)) in
    let e26 := eval vm_compute in (sr_get (ss_regs ss) (26%bv : bv 5)) in
    let h2 := cs_val Ex e22 in let u2 := cs_val Ex e26 in
    pmkst HS;
    lazymatch goal with HV : (?v = 0 <-> M = Boxreg.zero6), HVR : 0 <= ?v < 2 ^ 64 |- _ =>
      eapply (cs_land_dec v h2 u2 (ms_regs ms) (ms_mem ms) _ HJ HM HV HVR) end;
    [ replace (Boxreg.bx_n bs) with (j + 1) by lia; cs_sh
    | replace (Boxreg.bx_n bs) with (j + 1) by lia; cs_su
    | lia | lia | cs_reg HS .. ]
  end.
Local Ltac cs_go :=
  lazymatch goal with
  | HS : st_ok _ _ _ _ |- _ => cs_callL; cs_run; cs_go
  | HS : st_ok_pi _ _ ?Ex ?ss _, SHOK : sh_ok _ _ _ _ _ |- _ =>
    let pc := eval vm_compute in (ss_pc ss) in
    lazymatch pc with
    | 2116 => psrr_branch_tok cs_RUN cs_BR HS SHOK cs_Bspan;
              [ cs_bfact; cs_m1; tryif solve [exfalso; lia] then idtac else (cs_run_to PC1_scan; cs_land_scan)
              | cs_bfact; cs_m1; tryif solve [exfalso; lia] then idtac else (cs_run_to PC1_dec; cs_land_end) ]
    | _ => psrr_branch_tok cs_RUN cs_BR HS SHOK cs_Bspan;
           [ cs_bfact; cs_m1; tryif solve [exfalso; lia] then idtac else (cs_run; cs_go)
           | cs_bfact; cs_m1; tryif solve [exfalso; lia] then idtac else (cs_run; cs_go) ]
    end
  end.

Lemma cs_loop : forall v, (v = 0 <-> M = Boxreg.zero6) -> 0 <= v < 2 ^ 64 ->
  forall n j h u regs mem md, (Z.to_nat (Boxreg.bx_n bs - j) <= n)%nat -> cs_inv v j h u regs mem md ->
  SRr SEGS W3 (mkCfg (mkst regs (Z_to_bv 64 (BASE + PC1_scan)) mem (seg_rom SEGS)) md) (POST cx).
Proof.
  intros v HV HVR n. induction n as [|n IH]; intros j h u regs mem md Hn HI.
  { destruct HI as (Hj & _). lia. }
  destruct HI as (Hj & Hh & Hu & HSH & HSU & G2 & G8 & G9 & G3 & G4 & G18 & G24 & G20 & G19 & G21 & G22 & G23 & G25
    & G26 & G27 & HJ & HM).
  pose proof HGEO as (Hsp16 & Hspb & Hsp1 & Hsp32 & HF0 & HFc & HFia & HF64 & ESH & Hr16 & Hr0 & Hrc & Hinp).
  pose proof asan_consts as (C1 & _).
  pose proof (LLVMFuzzerTestOneInput_case1.c1_inv_n bs HINV) as HnB.
  pose proof (cs_nchj j Hj) as Hnj.
  assert (HSHb : 0 <= gSH cx fp < 2 ^ 47).
  { rewrite ESH. pose proof (Z.div_le_upper_bound (gF cx fp) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
    pose proof (Z.div_pos (gF cx fp) 8 ltac:(lia) ltac:(lia)). unfold SHADOW_OFF. lia. }
  pose proof (cs_seatL regs mem j Hj (proj1 HM) G9 G18 G19 G23) as [HS SHOK].
  pose proof (Eimg_env (Ereg regs [Z_to_bv 64 (gF cx fp + GO_MAC); Z_to_bv 64 nch; Z_to_bv 64 (Boxreg.bx_nch bs j)]))
    as HEI.
  change (Eimg (Ereg regs _)) with (cs_EL regs j) in HEI.
  assert (EE : forall q (rg : bv 5), Z.of_nat q = bv_unsigned rg -> ew (cs_EL regs j) q = getr regs rg).
  { intros q rg Hq. unfold cs_EL. pose proof (bv_unsigned_in_range 5 rg) as R. change (bv_modulus 5) with 32 in R.
    rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hq. }
  assert (EX : forall q, (q < 3)%nat -> ew (cs_EL regs j) (32 + q)%nat =
    nth q [Z_to_bv 64 (gF cx fp + GO_MAC); Z_to_bv 64 nch; Z_to_bv 64 (Boxreg.bx_nch bs j)] (Z_to_bv 64 0)).
  { intros q Hq. unfold cs_EL. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
  remember (cs_EL regs j) as E eqn:HE.
  assert (F2 : ew E 2 = Z_to_bv 64 (c_sp1 cx)) by (rewrite (EE 2%nat 2%bv eq_refl); exact G2).
  assert (F3 : ew E 3 = Z_to_bv 64 (bv_unsigned (getr (c_regs cx) 3)))
    by (rewrite (EE 3%nat 3%bv eq_refl), G3, Z_to_bv_bv_unsigned; reflexivity).
  assert (F4 : ew E 4 = Z_to_bv 64 (bv_unsigned (getr (c_regs cx) 4)))
    by (rewrite (EE 4%nat 4%bv eq_refl), G4, Z_to_bv_bv_unsigned; reflexivity).
  assert (F8 : ew E 8 = Z_to_bv 64 (spZ (c_regs cx))) by (rewrite (EE 8%nat 8%bv eq_refl); exact G8).
  assert (F9 : ew E 9 = Z_to_bv 64 (c_sp1 cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact G9).
  assert (F18 : ew E 18 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 18%nat 18%bv eq_refl); exact G18).
  assert (F19 : ew E 19 = Z_to_bv 64 (gF cx fp + GO_PREV + 56 * j + 12)) by (rewrite (EE 19%nat 19%bv eq_refl); exact G19).
  assert (F20 : ew E 20 = Z_to_bv 64 r) by (rewrite (EE 20%nat 20%bv eq_refl); exact G20).
  assert (F21 : ew E 21 = Z_to_bv 64 j) by (rewrite (EE 21%nat 21%bv eq_refl); exact G21).
  assert (F22 : ew E 22 = Z_to_bv 64 h) by (rewrite (EE 22%nat 22%bv eq_refl); exact G22).
  assert (F23 : ew E 23 = Z_to_bv 64 (gF cx fp + GO_PREV + 56 * j)) by (rewrite (EE 23%nat 23%bv eq_refl); exact G23).
  assert (F24 : ew E 24 = Z_to_bv 64 (gSH cx fp)) by (rewrite (EE 24%nat 24%bv eq_refl); exact G24).
  assert (F25 : ew E 25 = Z_to_bv 64 (Boxreg.bx_n bs - j)) by (rewrite (EE 25%nat 25%bv eq_refl); exact G25).
  assert (F26 : ew E 26 = Z_to_bv 64 u) by (rewrite (EE 26%nat 26%bv eq_refl); exact G26).
  assert (F27 : ew E 27 = Z_to_bv 64 v) by (rewrite (EE 27%nat 27%bv eq_refl); exact G27).
  assert (F32 : ew E 32 = Z_to_bv 64 (gF cx fp + GO_MAC)) by exact (EX 0%nat ltac:(lia)).
  assert (F33 : ew E 33 = Z_to_bv 64 nch) by exact (EX 1%nat ltac:(lia)).
  assert (F34 : ew E 34 = Z_to_bv 64 (Boxreg.bx_nch bs j)) by exact (EX 2%nat ltac:(lia)).
  clear HE EE EX G2 G3 G4 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27.
  pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 3)) as R3. pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 4)) as R4.
  change (bv_modulus 64) with (2 ^ 64) in R3, R4.
  unfold cs_J in HJ. unfold GO_PREV, GO_MAC in *.
  assert (Hes : ESTACK = 4096) by reflexivity.
  cs_go.
Qed.

(* ---- the block 0x806cc .. 0x80710 ---- *)
Lemma cs_slot30 : forall Ex ss ms lo hi wlo whi cs,
  st_ok_pi SEGS VAL Ex ss (restrict (w_H W3) ms) ->
  nth_error (ss_mem ss) 0 = Some (YP09.mkRegion (Some 9%nat) lo hi wlo whi cs) ->
  In (YP09.mkChunk 48 (CVal 8 (SLit 18446744073709551615))) cs -> bv_unsigned (ew Ex 9) = c_sp1 cx ->
  gslot cx W3 (cs_ms (ms_mem ms)) 0x30 ((-1) mod 2 ^ 64).
Proof.
  intros Ex ss ms lo hi wlo whi cs HS Hn Hin H9.
  pose proof (st_ok_pi_region_nth Ex ss (restrict (w_H W3) ms) 0 _ HS Hn) as Hr.
  unfold gslot. cbn [cs_ms ms_mem mkst]. change ((-1) mod 2 ^ 64) with 18446744073709551615.
  apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem ms)); [|lia].
  exact (YC4b.field_of_region Ex _ 9%nat (c_sp1 cx) cs lo hi wlo whi 48 8%N (SLit 18446744073709551615)
    18446744073709551615 Hr H9 Hin eq_refl ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia)).
Qed.

Local Ltac cs_upd0 :=
  lazymatch goal with
  | HFr : frame_of ?Ex ?rs (mrestrict _ ?m) (mrestrict _ ?m'), HM : cs_mem0 ?m |- _ =>
      let HM2 := fresh "HM" in
      assert (HM2 : cs_mem0 m');
      [ apply (cs_mem0_kp _ _ HM); apply (cs_kp_frame Ex rs _ _ HFr);
        let a := fresh "a" in let Ha := fresh "Ha" in let r0 := fresh "r0" in let Hin := fresh "Hin" in
        let Hb := fresh "Hb" in
        intros a Ha (r0 & Hin & Hb);
        let rs' := eval vm_compute in rs in change rs with rs' in Hin;
        cbn [In] in Hin;
        repeat (destruct Hin as [<- | Hin];
                [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
                  try (match goal with F : ew Ex 9%nat = Z_to_bv 64 ?b |- _ =>
                         rewrite F, unsigned_lit_small in Hb by lia end);
                  unfold cs_foot in Ha; lia |]);
        destruct Hin
      | clear HM; rename HM2 into HM ]
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end;
  repeat match goal with H1 : img_env _ _ ?Ex, H2 : img_env _ _ ?Ex |- _ => clear H2 end;
  lazymatch goal with HJ' : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => repeat rewrite wvb_collapse in HJ' end.
Local Ltac cs_awr0 :=
  lazymatch goal with |- awr_ok ?E0 ?rs ?stk ?sp0 ?fpp ?b0 ?bc ?lyy ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok E0 rs' stk sp0 fpp b0 bc lyy own) end;
  repeat first
    [ apply awr_ok_nil
    | (apply awr_ok_cons_ro; [cbn; lia|])
    | (apply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (c_sp1 cx - spZ (c_regs cx)));
       [reflexivity | match goal with F : ew _ 9%nat = Z_to_bv 64 _ |- _ => rewrite F, unsigned_lit_small by lia end; lia
       | cbn; unfold GB_STK; lia | cbn; lia |]) ].

Lemma cs_seg0 : forall (ms : machine_state) md,
  cs_J (ms_mem ms) md -> cs_mem0 (ms_mem ms) -> c1_core cx fp PC1_nch ms ->
  getr (ms_regs ms) 19 = w64 (gF cx fp + GO_MAC) -> getr (ms_regs ms) 20 = w64 r ->
  SRr SEGS W3 (mkCfg ms md) (POST cx).
Proof.
  intros ms md HJ HM HC G19 G20.
  pose proof HC as (_ & _ & _ & _ & _ & _ & (G2 & G8 & G9 & G3 & G4 & G18 & G24)).
  rewrite (c1_core_mkst cx fp PC1_nch ms HC).
  pose proof HGEO as (Hsp16 & Hspb & Hsp1 & Hsp32 & HF0 & HFc & HFia & HF64 & ESH & Hr16 & Hr0 & Hrc & Hinp).
  pose proof asan_consts as (C1 & _).
  pose proof (LLVMFuzzerTestOneInput_case1.c1_inv_n bs HINV) as HnB.
  pose proof (LLVMFuzzerTestOneInput_case1.c1_inv_len bs HINV) as Hl.
  assert (Hes : ESTACK = 4096) by reflexivity.
  assert (HSHb : 0 <= gSH cx fp < 2 ^ 47).
  { rewrite ESH. pose proof (Z.div_le_upper_bound (gF cx fp) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
    pose proof (Z.div_pos (gF cx fp) 8 ltac:(lia) ltac:(lia)). unfold SHADOW_OFF. lia. }
  pose proof (Z.div_mod (gF cx fp) 64 ltac:(lia)) as HFd. rewrite HF64, Z.add_0_r in HFd.
  pose proof HM as ((_ & _ & _ & _ & (_ & _ & _ & S78 & _) & HPV) & (_ & S20 & _) & _).
  unfold gslot in S78, S20. cbn [cs_ms ms_mem mkst] in S78, S20. unfold gprev in HPV. cbn [cs_ms ms_mem mkst] in HPV.
  pose proof (Eimg_env (Ereg (ms_regs ms) [Z_to_bv 64 (gF cx fp + GO_PREV); Z_to_bv 64 (Boxreg.bx_n bs)])) as HEI.
  assert (EE : forall q (rg : bv 5), Z.of_nat q = bv_unsigned rg ->
    ew (Eimg (Ereg (ms_regs ms) [Z_to_bv 64 (gF cx fp + GO_PREV); Z_to_bv 64 (Boxreg.bx_n bs)])) q = getr (ms_regs ms) rg).
  { intros q rg Hq. pose proof (bv_unsigned_in_range 5 rg) as R. change (bv_modulus 5) with 32 in R.
    rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hq. }
  assert (EX : forall q, (q < 2)%nat ->
    ew (Eimg (Ereg (ms_regs ms) [Z_to_bv 64 (gF cx fp + GO_PREV); Z_to_bv 64 (Boxreg.bx_n bs)])) (32 + q)%nat =
    nth q [Z_to_bv 64 (gF cx fp + GO_PREV); Z_to_bv 64 (Boxreg.bx_n bs)] (Z_to_bv 64 0)).
  { intros q Hq. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
  remember (Eimg (Ereg (ms_regs ms) [Z_to_bv 64 (gF cx fp + GO_PREV); Z_to_bv 64 (Boxreg.bx_n bs)])) as E eqn:HE.
  assert (F2 : ew E 2 = Z_to_bv 64 (c_sp1 cx)) by (rewrite (EE 2%nat 2%bv eq_refl); exact G2).
  assert (F3 : ew E 3 = Z_to_bv 64 (bv_unsigned (getr (c_regs cx) 3)))
    by (rewrite (EE 3%nat 3%bv eq_refl), G3, Z_to_bv_bv_unsigned; reflexivity).
  assert (F4 : ew E 4 = Z_to_bv 64 (bv_unsigned (getr (c_regs cx) 4)))
    by (rewrite (EE 4%nat 4%bv eq_refl), G4, Z_to_bv_bv_unsigned; reflexivity).
  assert (F8 : ew E 8 = Z_to_bv 64 (spZ (c_regs cx))) by (rewrite (EE 8%nat 8%bv eq_refl); exact G8).
  assert (F9 : ew E 9 = Z_to_bv 64 (c_sp1 cx)) by (rewrite (EE 9%nat 9%bv eq_refl); exact G9).
  assert (F18 : ew E 18 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 18%nat 18%bv eq_refl); exact G18).
  assert (F19 : ew E 19 = Z_to_bv 64 (gF cx fp + GO_MAC)) by (rewrite (EE 19%nat 19%bv eq_refl); exact G19).
  assert (F20 : ew E 20 = Z_to_bv 64 r) by (rewrite (EE 20%nat 20%bv eq_refl); exact G20).
  assert (F24 : ew E 24 = Z_to_bv 64 (gSH cx fp)) by (rewrite (EE 24%nat 24%bv eq_refl); exact G24).
  assert (F32 : ew E 32 = Z_to_bv 64 (gF cx fp + GO_PREV)) by exact (EX 0%nat ltac:(lia)).
  assert (F33 : ew E 33 = Z_to_bv 64 (Boxreg.bx_n bs)) by exact (EX 1%nat ltac:(lia)).
  pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 3)) as R3. pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 4)) as R4.
  change (bv_modulus 64) with (2 ^ 64) in R3, R4.
  unfold cs_J in HJ. unfold GO_PREV, GO_MAC in *.
  assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx) by (rewrite F9; apply unsigned_lit_small; lia).
  assert (U32 : bv_unsigned (ew E 32) = gF cx fp + 64) by (rewrite F32; apply unsigned_lit_small; lia).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES & _).
  (* the state at 0x806cc as the engine's symbolic state *)
  assert (HS : st_ok_pi SEGS VAL E cs_ss0
    (restrict (w_H W3) (mkst (ms_regs ms) (Z_to_bv 64 (BASE + PC1_nch)) (ms_mem ms) (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. unfold cs_ss0. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold cs_R0sp, cs_R0n. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + rewrite U9. split; [lia|]. split; [lia|].
        split; [intros o Ho; apply (apresent_writable SEGS); apply HPRES; unfold GB_STK; lia|].
        apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
        * apply (chunk_ok_val SEGS E _ (c_sp1 cx) 0x20 8 (SOff 32 12) (gF cx fp + 64 + 12) (cs_den_off E 32 _ 12 F32 ltac:(lia)));
            [cbn [Z.of_N]; lia | cbn [Z.of_N]; lia | apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms)); exact S20].
        * apply (chunk_ok_val SEGS E _ (c_sp1 cx) 0x78 8 (SOff 32 0) (gF cx fp + 64) (cs_den0 E 32 _ F32));
            [cbn [Z.of_N]; lia | cbn [Z.of_N]; lia | apply (val_mem_of_rdword SEGS (w_H W3) (ms_mem ms)); exact S78].
      + rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        apply Forall_cons; [|apply Forall_nil].
        apply (chunk_ok_val SEGS E _ (gF cx fp + 64) 280 4 (SOff 33 0) (Boxreg.bx_n bs) (cs_den0 E 33 _ F33));
          [cbn [Z.of_N]; lia | cbn [Z.of_N]; lia |].
        unfold Boxreg.bx_n. rewrite (cs_rd4_nu bs 280 Hl ltac:(lia) ltac:(lia)) by (unfold Boxreg.bx_n in HnB; lia).
        apply (cs_nu_val_mem (w_H W3) (ms_mem ms) (gF cx fp + 64) bs 280); [lia | unfold REG_SIZE; lia | exact HPV].
    - apply pairwise_disjoint_of_extents. unfold cs_R0sp, cs_R0n, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
    - split; [|split; exact I].
      cbn [cs_F0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite F9, F18, F32, F33. rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia).
      change (2 ^ 5) with 32. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold cs_SB, SHADOW_OFF.
      repeat match goal with |- _ /\ _ => split end; try exact I; try lia; rewrite HFd;
        replace (64 * (gF cx fp / 64) + 64) with ((8 * (gF cx fp / 64) + 8) * 8) by lia; apply Z.mod_mul; lia. }
  assert (SHOK : sh_ok SEGS cs_Bx [] E (mrestrict (w_H W3) (ms_mem ms))) by apply Forall_nil.
  clear HE EE EX.

  paj_run_tok cs_RUN HS HJ SHOK cs_Bspan; [cs_awr0 |]. cs_upd0.

  pmkst HS.
  prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
  prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
  eapply SRr_bind.
  { eapply (cs_bcmp (ms_regs ms0) (ms_mem ms0) _ (gF cx fp + 32) (VAL (A_OBJ 6)) M Boxreg.zero6 HJ);
    first
      [ (unfold spZ at 1; rewrite Rsp; cs_Fall; rewrite unsigned_lit_small by lia; reflexivity)
      | (rewrite Rgp; cs_Fall; rewrite Z_to_bv_bv_unsigned; reflexivity)
      | (rewrite Rtp; cs_Fall; rewrite Z_to_bv_bv_unsigned; reflexivity)
      | (rewrite Ra0; cs_Fall; reflexivity)
      | (rewrite Ra1; rewrite (img_env_atomP E 247 HEI ltac:(cbv; lia)); reflexivity)
      | (rewrite Ra2; reflexivity)
      | (rewrite Rra; apply ret_ok_codeptr_v; [lia | reflexivity])
      | exact (cs_src_mac (ms_mem ms0) _ HJ HM)
      | exact (cs_src_zero (ms_mem ms0) _ HJ) ]. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HCMP & HK2 & HPR2).
  jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W3) mem2) HP2 [0%nat; 1%nat] HS2.
  match type of HS2 with ?Q -> _ => assert (HQ : Q);
    [ cbn [ms_mem restrict mkst]; repeat apply Forall_cons; try apply Forall_nil; cs_kept E (ms_mem ms0) mem2 HK2 HPR2
    | specialize (HS2 HQ); clear HQ ] end.
  rewrite <- restrict_mkst_fx in HS2. clear HS. rename HS2 into HS. rewrite Rra.
  remember (havoc E 512 (map (getr regs2) CLOB)) as E2 eqn:HE2 in HS.
  assert (HEI2 : img_env VAL A_LIM E2) by (rewrite HE2; apply img_env_havoc_hi; [exact HEI | cbv; lia]).
  assert (OLD : forall q, (q < 512)%nat -> ew E2 q = ew E q)
    by (intros q Hq; rewrite HE2; apply YN3v.ew_havoc_old; exact Hq).
  assert (F516 : ew E2 516 = Z_to_bv 64 (bv_unsigned (getr regs2 10)))
    by (rewrite HE2; change 516%nat with (512 + 4)%nat;
        rewrite (YN3v.ew_havoc_new E 512 (map (getr regs2) CLOB) 4 (Z_to_bv 64 0)) by (cbv; lia);
        cbn [nth map]; rewrite Z_to_bv_bv_unsigned; reflexivity).
  cs_restate OLD. clear HE2 OLD.
  repeat match goal with Fo : ew E _ = _ |- _ => clear Fo end. clear HEI U9 U32.
  assert (RR : 0 <= bv_unsigned (getr regs2 10) < 2 ^ 64)
    by (pose proof (bv_unsigned_in_range 64 (getr regs2 10)) as RR0; change (bv_modulus 64) with (2 ^ 64) in RR0; exact RR0).
  assert (HM2 : cs_mem0 mem2) by (apply (cs_mem0_kp _ _ HM); apply cs_kp_of_kpx; apply cs_kpx_bcmp; exact HK2).
  clear HM. rename HM2 into HM.
  unfold cs_J in HJ2. clear HJ. rename HJ2 into HJ.
  clear SHOK. assert (SHOK : sh_ok SEGS cs_Bx [] E2 (mrestrict (w_H W3) mem2)) by apply Forall_nil.
  clear Ra0 Ra1 Ra2 Rra Rsp Rgp Rtp HP2 HK2 HPR2.
  paj_run_tok cs_RUN HS HJ SHOK cs_Bspan; [cs_awr0 |]. cs_upd0.

  psrr_branch_tok cs_RUN cs_BR HS SHOK cs_Bspan.
  - (* prev.n = 0: the scan is skipped *)
    cs_bfact. assert (HN0 : Boxreg.bx_n bs = 0) by lia.
    paj_run_to_tok cs_RUNTO HS HJ SHOK cs_Bspan PC1_dec; [cs_awr0 |]. cs_upd0.
    lazymatch goal with HS' : st_ok_pi _ _ ?Ex _ (restrict _ ?msF), HM' : cs_mem0 _ |- _ =>
      assert (H30 : gslot cx W3 (cs_ms (ms_mem msF)) 0x30 ((-1) mod 2 ^ 64))
        by (eapply (cs_slot30 _ _ _ _ _ _ _ _ HS'); [reflexivity | cbn [In]; auto 10 |];
            match goal with F : ew Ex 9%nat = Z_to_bv 64 _ |- _ => rewrite F end; apply unsigned_lit_small; lia);
      pmkst HS';
      eapply (cs_land_dec (bv_unsigned (getr regs2 10)) (-1) (-1) (ms_regs msF) (ms_mem msF) _ HJ (conj HM' H30) HCMP RR);
      [ rewrite HN0; left; split; [reflexivity | right; intros; lia]
      | rewrite HN0; left; split; [reflexivity | intros; lia]
      | lia | lia | cs_reg HS' .. ]
    end.
  - (* prev.n > 0: the head of the scan, row 0 *)
    cs_bfact.
    paj_run_to_tok cs_RUNTO HS HJ SHOK cs_Bspan PC1_scan; [cs_awr0 |]. cs_upd0.
    lazymatch goal with HS' : st_ok_pi _ _ ?Ex _ (restrict _ ?msF), HM' : cs_mem0 _ |- _ =>
      assert (H30 : gslot cx W3 (cs_ms (ms_mem msF)) 0x30 ((-1) mod 2 ^ 64))
        by (eapply (cs_slot30 _ _ _ _ _ _ _ _ HS'); [reflexivity | cbn [In]; auto 10 |];
            match goal with F : ew Ex 9%nat = Z_to_bv 64 _ |- _ => rewrite F end; apply unsigned_lit_small; lia);
      pmkst HS';
      apply (cs_loop (bv_unsigned (getr regs2 10)) HCMP RR (Z.to_nat (Boxreg.bx_n bs)) 0 (-1) (-1) (ms_regs msF) (ms_mem msF) _);
      [ lia | ];
      unfold cs_inv, GO_PREV, GO_MAC;
      split; [lia|]; split; [lia|]; split; [lia|];
      split; [left; split; [reflexivity | right; intros; lia]|];
      split; [left; split; [reflexivity | intros; lia]|];
      do 15 (split; [cs_reg HS'|]);
      split; [exact HJ | exact (conj HM' H30)]
    end.
Qed.

End d.

(* ---- the piece: from 0x806cc (C1_nch) to 0x807a8 (C1_dec) ---- *)
Theorem c1_seg_scan : forall i, gb_from B MT POST (C1_dec B MT i) -> gb_from B MT POST (C1_nch B MT i).
Proof.
  intros i HDEC cx fp k acc ly3 S3 W3 ms3 md3 HB HJ HFR HMO HI.
  destruct HI as (r & bs & pos & M & nch & HC & HBASE & HREG & HMAC & HNCH & H58 & G19 & G25).
  destruct HBASE as (Hi & Hk & Hacc & HBLK & HINV & HC1 & HSR & HCU & H68 & H48 & G20).
  assert (HFA : frame_addr ly3 GB_CID fp = gF cx fp).
  { pose proof HB as ((HAR0 & _) & _). pose proof HJ as (_ & Hly3 & _).
    destruct (al_layout _ _ LAWS _ _ _ _ _ ly3 HAR0 Hly3) as (_ & Efa & _). unfold gF. apply Efa. }
  pose proof HREG as (HRIN & _). pose proof HMAC as (HLM & _).
  eapply cs_seg0 with (cx := cx) (fp := fp) (k := k) (acc := acc) (i := i) (r := r) (pos := pos) (nch := nch)
    (ly3 := ly3) (S3 := S3) (W3 := W3) (bs := bs) (M := M) (ms := ms3) (md := md3);
    try eassumption.
  - eapply cs_geo_of with (mem := ms_mem ms3) (md := md3); eassumption.
  - unfold cs_mem0. split; [exact HC1|]. split; [exact HSR|]. split; [exact HCU|]. split; [exact H68|].
    split; [exact H48|]. split; [exact HREG|]. split; [exact HMAC | exact H58].
Qed.

End c.
End b.
End a.
