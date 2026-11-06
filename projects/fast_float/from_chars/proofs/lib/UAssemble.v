(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec StoreOk DriverCfg RealizesCfg RealizesAbort.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Image.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Frame.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require Import HIface HIfaceInit U_hbase U_h_fuzz_base U_h_fuzz.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import U_memcpy_stmt U_from_chars_double_stmt
  U_from_chars_float_stmt U_from_chars_int_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_memcpy U_lib_closed.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import UDrvHeap UDrvRead UDir UTgt3 PKeepMono UHeapIGlue UTop UHeapInst.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel MallocInv.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import MngL4 MngL4I MngL4F MngL4H.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require AXG_mwd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Notation ioutside := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.outside.
Local Notation ivl := OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Frame.ivl.
Local Notation PSEGS := Ubsan.M.loaded_segments.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ivl_disj (a b : ivl) : bool := (Z.leb (snd a) (fst b) || Z.leb (snd b) (fst a))%bool.
(* [comment removed for export] *)
Definition sub_or_disj (A C B : list ivl) : bool :=
  forallb (fun s => existsb (fun c => (Z.leb (fst c) (fst s) && Z.leb (snd s) (snd c))%bool) C || forallb (ivl_disj s) A)%bool B.

Lemma not_outside_in : forall A x, ~ ioutside A x -> exists a, In a A /\ fst a <= x < snd a.
Proof.
  induction A as [|[lo hi] A IH]; intros x H; cbn [ioutside] in H; [exfalso; exact (H I)|].
  destruct (Z_le_dec lo x) as [H1|H1]; [destruct (Z_lt_dec x hi) as [H2|H2]|].
  - exists (lo, hi). split; [left; reflexivity | cbn; lia].
  - destruct (IH x) as (a & Ha & Hx); [intros Ho; apply H; split; [lia | exact Ho]|]. exists a. split; [right; exact Ha | exact Hx].
  - destruct (IH x) as (a & Ha & Hx); [intros Ho; apply H; split; [lia | exact Ho]|]. exists a. split; [right; exact Ha | exact Hx].
Qed.
Lemma outside_in : forall C c x, ioutside C x -> In c C -> ~ (fst c <= x < snd c).
Proof.
  induction C as [|[lo hi] C IH]; intros c x H Hc; [destruct Hc|]. cbn [ioutside] in H. destruct H as [H1 H2].
  destruct Hc as [<-|Hc]; [exact H1 | exact (IH c x H2 Hc)].
Qed.
Lemma outside_all : forall B x, (forall b, In b B -> ~ (fst b <= x < snd b)) -> ioutside B x.
Proof.
  induction B as [|[lo hi] B IH]; intros x H; cbn [ioutside]; [exact I|].
  split; [exact (H (lo, hi) (or_introl eq_refl)) | apply IH; intros b Hb; exact (H b (or_intror Hb))].
Qed.
Lemma outside_sub_or_disj : forall A C B x, sub_or_disj A C B = true -> ~ ioutside A x -> ioutside C x -> ioutside B x.
Proof.
  intros A C B x H HA HC. destruct (not_outside_in A x HA) as (a & Ha & Hxa). apply outside_all. intros b Hb Hxb.
  unfold sub_or_disj in H. rewrite forallb_forall in H. specialize (H b Hb). apply orb_prop in H as [H|H].
  - apply existsb_exists in H as (c & Hc & Hcb). apply andb_prop in Hcb as [H1 H2]. apply Z.leb_le in H1, H2.
    exact (outside_in C c x HC Hc ltac:(lia)).
  - rewrite forallb_forall in H. specialize (H a Ha). unfold ivl_disj in H. apply orb_prop in H as [H|H]; apply Z.leb_le in H; lia.
Qed.

Lemma stat_x : forall x, ~ ioutside EXGX x -> ioutside STATIC_P x.
Proof. intros x H. apply (outside_sub_or_disj EXGX [] STATIC_P x); [vm_compute; reflexivity | exact H | exact I]. Qed.
Lemma stat_i : forall x, ~ ioutside IMGIV x -> ioutside (CELLS_NE ++ ERRC) x -> ioutside STATIC_P x.
Proof. intros x H1 H2. apply (outside_sub_or_disj IMGIV (CELLS_NE ++ ERRC) STATIC_P x); [vm_compute; reflexivity | exact H1 | exact H2]. Qed.
Lemma stat_r : forall x, RSX x -> ioutside STATIC_P x.
Proof.
  intros x H. apply (outside_sub_or_disj [(RS_LO, RS_LO + 65536)] [] STATIC_P x); [vm_compute; reflexivity | | exact I].
  unfold RSX in H. cbn [ioutside]. tauto.
Qed.
Lemma stat_ro : forall x, 0x10000 <= x < 0x22000 \/ 0x66b98 <= x < 0x66b9c -> ~ UTgt3.KRO x -> ioutside STATIC_P x.
Proof.
  intros x H1 H2. apply (outside_sub_or_disj PRO [(0x18288, 0x182a8); (0x182a8, 0x18327)] STATIC_P x); [vm_compute; reflexivity | |].
  - unfold PRO. cbn [ioutside]. tauto.
  - unfold UTgt3.KRO in H2. cbn [ioutside]. lia.
Qed.
(* [comment removed for export] *)
Lemma stat_sro : Forall (fun r => forall x, fst r <= x < snd r -> ioutside STATIC_P x \/ ~ ioutside U_KEEP x) U_RO.
Proof.
  apply Forall_forall. intros [lo hi] Hr x Hx. cbn [fst snd] in Hx.
  destruct (HIface.outside_dec U_KEEP x) as [Ho|Ho]; [left | right; exact Ho].
  apply (outside_sub_or_disj [(lo, hi)] U_KEEP STATIC_P x); [| cbn [ioutside]; lia | exact Ho].
  unfold U_RO in Hr. destruct Hr as [E|[E|[]]]; injection E as <- <-; vm_compute; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma keep_cells : keep_sub CELLS_NE U_KEEP.
Proof. intros a H. unfold CELLS_NE in H. unfold U_KEEP. cbn [ioutside] in *. tauto. Qed.

Lemma heap_ok_keep : forall cfg HI GP TP IMG_LO IMG_END HTOP STATIC PCM MNEED PCF FNEED,
  heap_ok PSEGS cfg HI GP TP IMG_LO IMG_END HTOP STATIC U_KEEP PCM MNEED PCF FNEED ->
  heap_ok PSEGS cfg HI GP TP IMG_LO IMG_END HTOP STATIC CELLS_NE PCM MNEED PCF FNEED.
Proof.
  intros cfg HI GP TP IMG_LO IMG_END HTOP STATIC PCM MNEED PCF FNEED (A & B & C & D & E).
  split; [exact A|]. split; [exact (malloc_contract_mono _ _ _ _ _ _ _ _ _ _ _ keep_cells _ _ B)|].
  split; [exact (free_contract_mono _ _ _ _ _ _ _ _ _ _ _ keep_cells _ _ C)|]. split; [exact D | exact E].
Qed.

Lemma malloc_contract_init_mono : forall segs cfg HS Heap blocks owned GP TP HTOP K1 K2 HeapI INIT PCM NEED, keep_sub K1 K2 ->
  malloc_contract_init segs cfg HS Heap blocks owned GP TP HTOP K2 HeapI INIT PCM NEED ->
  malloc_contract_init segs cfg HS Heap blocks owned GP TP HTOP K1 HeapI INIT PCM NEED.
Proof.
  intros segs cfg HS Heap blocks owned GP TP HTOP K1 K2 HeapI INIT PCM NEED HK H fx regs m md hs n ret K A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 KC.
  apply (H fx regs m md hs n ret K A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14).
  intros fx' regs' m' md' hs' p C1 C2 C3 C4 C5 C6. apply (KC fx' regs' m' md' hs' p C1 C2 C3 C4 C5).
  intros a Ha. exact (C6 a (HK a Ha)).
Qed.

(* [comment removed for export] *)
Section Asm.
(* [comment removed for export] *)
Let DIRWK := fun fx => @AXG_mwd.direct_wk fx.

#[using="Type"] Lemma dcfg_alloc_off : sc_alloc DCFG = false.
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

#[using="DIRWK"] Lemma hok_p : forall HTOP, HTR HTOP -> U_heap_ok DCFG (HI HTOP) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x77990) HTOP STATIC_P.
Proof. LiaFast.lf_pins (fun (DIRWK : LiaFast.U) => LiaFast.u0). intros HTOP HR. unfold HTR in HR. exact (plain_heap_ok DCFG HTOP (Z_to_bv 64 0x10800) dcfg_alloc_off ltac:(lia) DIRWK). Qed.

#[using="DIRWK"] Lemma hok_c : forall HTOP, HTR HTOP ->
  heap_ok PSEGS DCFG (HI HTOP) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x77990) 0x10000 0x99000 HTOP STATIC_P CELLS_NE 0x530c8 8192 0x52f88 8192.
Proof. LiaFast.lf_pins (fun (DIRWK : LiaFast.U) => LiaFast.u0). intros HTOP HR. apply heap_ok_keep. exact (hok_p HTOP HR). Qed.

#[using="DIRWK"] Lemma hoki_c : forall HTOP, HTR HTOP ->
  heap_init_ok PSEGS DCFG (HI HTOP) (HeapI HTOP) INIT (Z_to_bv 64 0x10800) (Z_to_bv 64 0x77990) HTOP CELLS_NE 0x530c8 8192.
Proof. LiaFast.lf_pins (fun (DIRWK : LiaFast.U) => LiaFast.u0).
  intros HTOP HR. split.
  - apply (malloc_contract_init_mono _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ keep_cells). unfold HTR in HR.
    exact (proj1 (plain_heap_init_ok DCFG HTOP (Z_to_bv 64 0x10800) dcfg_alloc_off ltac:(lia) DIRWK)).
  - exact (heap_frame_init_L4 HTOP).
Qed.

#[using="DIRWK"] Lemma hfz_c : forall HTOP, HTR HTOP ->
  fuzz_contract PSEGS DCFG (hi_HS (HI HTOP)) (hi_Heap (HI HTOP)) (hi_blocks (HI HTOP)) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x77990)
    0x10000 0x99000 HTOP STATIC_P CELLS_NE 0x22e0c 8592 PRO.
Proof. LiaFast.lf_pins (fun (DIRWK : LiaFast.U) => LiaFast.u0).
  intros HTOP HR. eapply fuzz_contract_mono; [exact keep_cells|].
  exact (fuzz_ok DCFG (HI HTOP) (Z_to_bv 64 0x10800) (Z_to_bv 64 0x77990) HTOP STATIC_P (hok_p HTOP HR)
           U_memcpy.memcpy_spec U_lib_closed.U_ciir_closed U_lib_closed.U_from_chars_double_closed
           U_lib_closed.U_from_chars_float_closed U_lib_closed.U_from_chars_int_closed stat_sro).
Qed.

(* [comment removed for export] *)
#[using="DIRWK"] Theorem ubsan_realizes_A_lim : forall lim, 2 ^ 31 <= lim ->
  image_realizes_cfg_e DCFG PSEGS Ubsan.M.init_pc
  Ubsan.M.phdrs lim SPEC.
Proof. LiaFast.lf_pins (fun (DIRWK : LiaFast.U) => LiaFast.u0).
  exact (plain_realizes_lim STATIC_P stat_x stat_i stat_r stat_ro HI hok_c
    (fun HTOP hs m m' md H1 H2 H3 => heap_errno_frame HTOP hs m m' md H1 H2 H3)
    (fun HTOP hs m m' md H1 H2 H3 H4 => heap_cells_frame HTOP hs m m' md H1 H2 H3 H4)
    (fun HTOP hs m md H1 => heap_need_locks HTOP hs m md H1)
    (fun HTOP hs m md md' H1 H2 _ _ => heap_model_vm HTOP hs m md md' H1 H2)
    (fun HTOP hs m md H1 => hp_kro HTOP hs m md H1)
    (fun HTOP => HeapI HTOP) (fun HTOP => INIT) hoki_c
    (fun HTOP hs m md H1 => heapI_owned HTOP hs m md H1)
    (fun HTOP hs m m' md H1 H2 H3 => heapI_errno_frame HTOP hs m m' md H1 H2 H3)
    (fun HTOP hs m m' md H1 H2 H3 H4 => heapI_cells_frame HTOP hs m m' md H1 H2 H3 H4)
    (fun HTOP hs m md md' H1 H2 _ _ => heapI_model_vm HTOP hs m md md' H1 H2)
    (fun sp0 av ev uid tid hw rdraw regs mem brk mbase lim inp Hsp Hva Hve Hfits Hbrk Hmb Hlim ME =>
       heapI_main sp0 av ev uid tid hw rdraw regs mem Hsp Hva Hve Hfits ME brk mbase lim inp Hbrk Hmb Hlim)
    hfz_c).
Qed.

(* [comment removed for export] *)
#[using="DIRWK"] Theorem ubsan_realizes_A : image_realizes_cfg_e DCFG PSEGS Ubsan.M.init_pc
  Ubsan.M.phdrs target_alloc_limit SPEC.
Proof. LiaFast.lf_pins (fun (DIRWK : LiaFast.U) => LiaFast.u0). apply ubsan_realizes_A_lim. unfold target_alloc_limit. lia. Qed.
End Asm.
