(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySweepS1c), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* The ground the four segments of the sweep phase share: a cut's machine state as
   the engine's symbolic state (the spill slots, the bytes of the frame on the side
   stack), what a call of the memory-checking runtime's wrappers for malloc and free
   keeps of a cut's memory, the blocks of the phase being distinct, and the range of
   the row count the input names. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YC5d YI16 YM05 YFen.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal GrantSyms GrantList GrantPa GrantPaLib GrantBase GrantRo
GrantEntryDefs GrantEntrySweepDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import YC1g YC1h YC45 YC85 GrantFrame GrantACja.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import HeadampTxEffective GrantEntrySeat.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import
HeadampModel GrantModel GrantSweepModel BuildSweepModel GrantSlotPlan.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require SlotNeeds_c SegSetModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.



Lemma pairwise_dup : forall {X} (R : X -> X -> Prop) (l1 : list X) (x : X) (l2 l3 : list X),
  pairwise R (l1 ++ x :: l2 ++ x :: l3) -> R x x.
Proof.
intros X R l1. induction l1 as [|y l1 IH]; intros x l2 l3 Hp; cbn in Hp.
- destruct Hp as [HF _]. apply (proj1 (Forall_forall _ _) HF). apply in_or_app. right. left. reflexivity.
- destruct Hp as [_ Hp]. exact (IH x l2 l3 Hp).
Qed.

Lemma split_last_unique : forall {X} (x : X) (pre l1 l2 : list X),
  pre ++ [x] = l1 ++ x :: l2 -> ~ In x pre -> l1 = pre /\ l2 = [].
Proof.
intros X x pre. induction pre as [|y pre IH]; intros l1 l2 E Hni.
- cbn in E. destruct l1 as [|z l1]; cbn in E.
  + assert (E2 : l2 = []) by (injection E; intros; congruence). subst l2. split; reflexivity.
  + exfalso. assert (Hlen := f_equal (@length X) E). cbn in Hlen. rewrite length_app in Hlen. cbn in Hlen. lia.
- destruct l1 as [|z l1]; cbn in E.
  + exfalso. apply Hni. left. injection E as E1 _. exact E1.
  + injection E as <- E. destruct (IH l1 l2 E ltac:(intros H; apply Hni; right; exact H)) as [-> ->].
    split; reflexivity.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

(* ---- reading a byte and a word out of the view ---- *)

Lemma gs_rdword_range : forall (H : word -> bool) (mem : word -> option byte) a v,
  rdword (aview SEGS H mem) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros H mem a v Hr. unfold rdword in Hr.
assert (Hb : forall x y, aview SEGS H mem x = Some y -> 0 <= y < 256).
{ intros x y Hx. unfold aview in Hx. destruct (mbyte SEGS (mrestrict H mem) x) as [b|]; [|discriminate].
  cbn in Hx. injection Hx as <-. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. exact R. }
repeat match type of Hr with context [match aview SEGS H mem ?x with _ => _ end] =>
  let y := fresh "y" in let Hy := fresh "Hy" in
  destruct (aview SEGS H mem x) as [y|] eqn:Hy; [apply Hb in Hy | discriminate Hr] end.
injection Hr as <-. lia.
Qed.

Lemma gs_byte_range : forall (H : word -> bool) (mem : word -> option byte) a v,
  aview SEGS H mem a = Some v -> 0 <= v < 256.
Proof.
intros H mem a v Hx. unfold aview in Hx. destruct (mbyte SEGS (mrestrict H mem) a) as [b|]; [|discriminate].
cbn in Hx. injection Hx as <-. pose proof (bv_unsigned_in_range 8 b) as R. change (bv_modulus 8) with 256 in R. exact R.
Qed.

Lemma gs_val_mem_of_byte : forall (H : word -> bool) (mem : word -> option byte) a v,
  aview SEGS H mem a = Some v -> val_mem SEGS (mrestrict H mem) a 1 v.
Proof.
intros H mem a v Hx. pose proof (gs_byte_range H mem a v Hx) as Hr.
intros k Hk. assert (k = 0%nat) as -> by lia. cbn [Z.of_nat]. rewrite Z.add_0_r.
unfold aview in Hx. destruct (mbyte SEGS (mrestrict H mem) a) as [b|] eqn:Hb; [|discriminate].
cbn in Hx. injection Hx as Hx. f_equal. unfold YO0f.le_byte.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. rewrite !(Z.mod_small v 256 ltac:(lia)).
rewrite <- Hx. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* ---- a byte of a data slot of the environment, as a number ---- *)
Lemma gs_firstn1_skipn : forall {A} (l : list A) n b, nth_error l n = Some b -> firstn 1 (skipn n l) = [b].
Proof.
intros A l. induction l as [|x l IH]; intros n b H; destruct n as [|n]; cbn in H |- *; try discriminate.
- injection H as ->. reflexivity.
- apply IH. exact H.
Qed.

Lemma gs_U_data1 : forall (E : env) i b, 0 <= i -> nth_error (ed E 0) (Z.to_nat i) = Some b ->
  U E (SData 0 i 1) = bv_unsigned b.
Proof.
intros E i b Hi Hb. unfold U. cbn [sv_denot]. unfold data_word.
change (N.to_nat 1) with 1%nat. rewrite (gs_firstn1_skipn _ _ _ Hb), bytes_le_single.
apply unsigned_lit_small. pose proof (u8_range b). lia.
Qed.

(* ---- the seat: a symbolic state from a machine state ---- *)

Lemma gs_seat : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) extra pc rs at0,
  YP09.regions_wf rs = true ->
  Forall (YP09.region_ok SEGS (Eimg (Ereg regs extra)) (mrestrict (w_H W) mem)) rs ->
  YP09.pairwise_disjoint (Eimg (Ereg regs extra)) rs ->
  atoms_ok (Eimg (Ereg regs extra)) at0 ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs extra)) (mkSS pc sr_atoms rs None (mkFacts at0 [] []))
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem extra pc rs at0 Hwf Hrs Hpd Hat. rewrite restrict_mkst_fx.
apply pa_entry_st_ok_full; [apply regs_ok_Eimg_Ereg | exact Hwf | exact Hrs | exact Hpd |].
split; [exact Hat | split; exact I].
Qed.

(* The same, with the bytes of one object of the cut in a data slot of the
   environment, which is how the engine reads a byte of the frame. *)
Lemma gs_seatD : forall (W : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte) extra
  (D : nat) (RB : list byte) pc rs at0,
  YP09.regions_wf rs = true ->
  Forall (YP09.region_ok SEGS (Eimg (edset (Ereg regs extra) D RB)) (mrestrict (w_H W) mem)) rs ->
  YP09.pairwise_disjoint (Eimg (edset (Ereg regs extra) D RB)) rs ->
  atoms_ok (Eimg (edset (Ereg regs extra) D RB)) at0 ->
  st_ok_pi SEGS VAL (Eimg (edset (Ereg regs extra) D RB))
    (mkSS pc sr_atoms rs None (mkFacts at0 [] []))
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem extra D RB pc rs at0 Hwf Hrs Hpd Hat. rewrite restrict_mkst_fx.
apply pa_entry_st_ok_full; [| exact Hwf | exact Hrs | exact Hpd |].
- apply (regs_ok_agree_on (fun _ => true) (Eimg (Ereg regs extra)));
    [intros n _; reflexivity | vm_compute; reflexivity | apply regs_ok_Eimg_Ereg].
- split; [exact Hat | split; exact I].
Qed.

(* A window of the realigned machine frame, one 8-byte chunk per spill slot the walk
   reads; a phase says which of the 184 bytes it may write. *)
Lemma gs_slotreg_ok : forall (W : world SEGS) (E : env) (mem : word -> option byte) (cs : list YP09.chunk) base wlo whi,
  bv_unsigned (ew E 9%nat) = base -> 0 <= base -> base + 192 <= 2 ^ 64 ->
  (forall o, wlo <= o < whi -> YP09.writable_at SEGS (mrestrict (w_H W) mem) (base + o)) ->
  Forall (YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base) cs ->
  YP09.region_ok SEGS E (mrestrict (w_H W) mem) (YP09.mkRegion (Some 9%nat) 0 192 wlo whi cs).
Proof.
intros W E mem cs base wlo whi Hb H0 H1 Hw Hcs. unfold YP09.region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.base_val].
rewrite Hb. split; [lia|]. split; [lia|]. split; [exact Hw | exact Hcs].
Qed.

Lemma gs_slot_chunk : forall (W : world SEGS) (E : env) (mem : word -> option byte) off n v base,
  ew E n = Z_to_bv 64 v -> bv_unsigned (ew E 9%nat) = base ->
  rdword (aview SEGS (w_H W) mem) (base + off) = Some v ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 8 (SOff n 0))).
Proof.
intros W E mem off n v base Hn Hb Hr.
apply (chunk_ok_val SEGS E (mrestrict (w_H W) mem) base off 8%N (SOff n 0) v).
- cbn [sv_denot]. rewrite Hn, Z.add_0_r. apply Z_to_bv_bv_unsigned.
- change (8 * Z.of_N 8) with 64. exact (gs_rdword_range (w_H W) mem _ v Hr).
- cbn [Z.of_N]; lia.
- exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Hr).
Qed.

(* A byte of the frame on the side stack, as a chunk of the frame's region. *)
Lemma gs_fb_chunk : forall (W : world SEGS) (E : env) (mem : word -> option byte) off v base,
  aview SEGS (w_H W) mem (base + off) = Some v ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 1 (SLit v))).
Proof.
intros W E mem off v base Hr.
apply (chunk_ok_val SEGS E (mrestrict (w_H W) mem) base off 1%N (SLit v) v).
- reflexivity.
- change (8 * Z.of_N 1) with 8. change (2 ^ 8) with 256. exact (gs_byte_range (w_H W) mem _ v Hr).
- cbn [Z.of_N]; lia.
- exact (gs_val_mem_of_byte (w_H W) mem _ v Hr).
Qed.

(* The atoms and the region of the free segment: the spill slots it reads back.
   Atom 32 is the sweep block (slot 64), 33 the address of `raw` (slot 72), 34 the
   bytes of input left (slot 120) and 35 the shadow offset (slot 152). *)
Definition gsf_extra (s gRaw nl : Z) : list word := [w64 s; w64 gRaw; w64 nl; w64 SHADOW_OFF].
Definition gsf_regions : YP09.smem :=
  [YP09.mkRegion (Some 9%nat) 0 192 0 0
     [YP09.mkChunk 64 (CVal 8 (SOff 32 0)); YP09.mkChunk 72 (CVal 8 (SOff 33 0));
      YP09.mkChunk 120 (CVal 8 (SOff 34 0)); YP09.mkChunk 152 (CVal 8 (SOff 35 0))]].

Section c.
Variable B : asyms.
Variable MT : ameter_ops.

(* ---- what a call keeps ---- *)
(* The phase reads back the spill slots of the realigned machine frame and the words
   the prologue saved above it, the table, the caller's input, the frame on the side
   stack for frames and its 104 shadow bytes. A call writes none of them. *)
Definition gs_keep_at (cx : ecx) (fp t : Z) (a : Z) : Prop :=
  (c_sp1 cx <= a < 2 ^ 64) \/ (t <= a < t + 460) \/ (c_p cx <= a < c_p cx + c_n cx) \/
  (gF cx fp <= a < gF cx fp + fs_frame_bytes GE_CID) \/
  (gSH cx fp <= a < gSH cx fp + Z.of_nat GE_NSH).

Definition gs_keepW (cx : ecx) (fp t : Z) (W W' : world SEGS) (m m' : word -> option byte) : Prop :=
  forall a, gs_keep_at cx fp t a -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a.

Lemma gs_keepW_refl : forall cx fp t W m, gs_keepW cx fp t W W m m.
Proof. intros cx fp t W m a _. reflexivity. Qed.

Lemma gs_keepW_trans : forall cx fp t W1 W2 W3 m1 m2 m3,
  gs_keepW cx fp t W1 W2 m1 m2 -> gs_keepW cx fp t W2 W3 m2 m3 -> gs_keepW cx fp t W1 W3 m1 m3.
Proof. intros cx fp t W1 W2 W3 m1 m2 m3 H12 H23 a Ha. rewrite (H23 a Ha). exact (H12 a Ha). Qed.

(* ---- the facts a kept memory carries ---- *)

Lemma gs_keep_word : forall cx fp t W W' m m' a v,
  gs_keepW cx fp t W W' m m' ->
  (forall i, 0 <= i < 8 -> gs_keep_at cx fp t (a + i)) ->
  rdword (aview SEGS (w_H W) m) a = Some v ->
  rdword (aview SEGS (w_H W') m') a = Some v.
Proof.
intros cx fp t W W' m m' a v HK Hin Hr. unfold rdword in *.
rewrite (HK a ltac:(replace a with (a + 0) by lia; apply Hin; lia)).
rewrite (HK (a+1) ltac:(apply Hin; lia)). rewrite (HK (a+2) ltac:(apply Hin; lia)).
rewrite (HK (a+3) ltac:(apply Hin; lia)). rewrite (HK (a+4) ltac:(apply Hin; lia)).
rewrite (HK (a+5) ltac:(apply Hin; lia)). rewrite (HK (a+6) ltac:(apply Hin; lia)).
rewrite (HK (a+7) ltac:(apply Hin; lia)). exact Hr.
Qed.

Lemma gs_keep_slot : forall cx fp t W W' m m' off v,
  gs_keepW cx fp t W W' m m' -> 0 <= off -> off + 8 <= 2 ^ 63 ->
  c_sp1 cx + off + 8 <= 2 ^ 64 ->
  rdword (aview SEGS (w_H W) m) (c_sp1 cx + off) = Some v ->
  rdword (aview SEGS (w_H W') m') (c_sp1 cx + off) = Some v.
Proof.
intros cx fp t W W' m m' off v HK H0 H1 H2 Hr.
apply (gs_keep_word cx fp t W W' m m'); [exact HK | | exact Hr].
intros i Hi. left. unfold gs_keep_at. lia.
Qed.

Lemma gs_keep_fb : forall cx fp t W W' m m' off v,
  gs_keepW cx fp t W W' m m' -> 0 <= off < fs_frame_bytes GE_CID ->
  aview SEGS (w_H W) m (gF cx fp + off) = Some v ->
  aview SEGS (w_H W') m' (gF cx fp + off) = Some v.
Proof.
intros cx fp t W W' m m' off v HK Hoff Hr.
rewrite (HK (gF cx fp + off) ltac:(unfold gs_keep_at; right; right; right; left; lia)). exact Hr.
Qed.

Lemma gs_keep_garr : forall cx fp t W W' m m' a (l : list byte),
  gs_keepW cx fp t W W' m m' ->
  (forall j, (j < length l)%nat -> gs_keep_at cx fp t (a + Z.of_nat j)) ->
  garr8 SEGS (mrestrict (w_H W) m) a (map (fun b : byte => bv_unsigned b) l) ->
  garr8 SEGS (mrestrict (w_H W') m') a (map (fun b : byte => bv_unsigned b) l).
Proof.
intros cx fp t W W' m m' a l HK Hin HG j Hj.
rewrite length_map in Hj. destruct (HG j ltac:(rewrite length_map; exact Hj)) as [Hv Hr].
split; [|exact Hr].
intros k Hk. assert (k = 0%nat) as -> by lia. cbn [Z.of_nat]. rewrite Z.add_0_r.
specialize (Hv 0%nat ltac:(lia)). cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv.
rewrite (mbyte_of_aview SEGS (w_H W) (w_H W') m m' (a + Z.of_nat j) (HK (a + Z.of_nat j) (Hin j Hj))).
exact Hv.
Qed.

(* ---- the whole memory of a cut, carried ---- *)

Lemma gs_keep_gtab : forall cx fp ly3 S3 W W' ms ms' t T,
  gs_keepW cx fp t W W' (ms_mem ms) (ms_mem ms') ->
  gtab B cx ly3 S3 W ms t T -> gtab B cx ly3 S3 W' ms' t T.
Proof.
intros cx fp ly3 S3 W W' ms ms' t T HK (Hin & Ht & Hlen & HB).
split; [exact Hin|]. split; [exact Ht|]. split; [exact Hlen|].
intros i Hi H1 H2 H3. rewrite (HK (t + i) ltac:(unfold gs_keep_at; right; left; lia)). exact (HB i Hi H1 H2 H3).
Qed.

Lemma gs_keep_gfarr : forall cx fp t W W' ms ms' off (l : list byte),
  gs_keepW cx fp t W W' (ms_mem ms) (ms_mem ms') ->
  0 <= off -> off + Z.of_nat (length l) <= fs_frame_bytes GE_CID ->
  gfarr cx fp W ms off l -> gfarr cx fp W' ms' off l.
Proof.
intros cx fp t W W' ms ms' off l HK H0 H1 HG. unfold gfarr in *.
apply (gs_keep_garr cx fp t W W' (ms_mem ms) (ms_mem ms')); [exact HK | | exact HG].
intros j Hj. unfold gs_keep_at. right. right. right. left. lia.
Qed.

Lemma gs_keep_gslot : forall cx fp t W W' ms ms' off v,
  gs_keepW cx fp t W W' (ms_mem ms) (ms_mem ms') -> 0 <= off <= 184 ->
  c_sp1 cx + 192 <= 2 ^ 64 ->
  gslot cx W ms off v -> gslot cx W' ms' off v.
Proof.
intros cx fp t W W' ms ms' off v HK Hoff Hhi HG. unfold gslot in *.
apply (gs_keep_word cx fp t W W' (ms_mem ms) (ms_mem ms') (c_sp1 cx + off) v);
  [exact HK | | exact HG].
intros i Hi. left. unfold gs_keep_at. lia.
Qed.

Lemma gs_keep_gslots_late : forall cx fp t W W' ms ms',
  gs_keepW cx fp t W W' (ms_mem ms) (ms_mem ms') -> c_sp1 cx + 192 <= 2 ^ 64 ->
  gslots_late cx fp W ms -> gslots_late cx fp W' ms'.
Proof.
intros cx fp t W W' ms ms' HK Hhi (SMID & S8 & S32 & S40 & S72 & S80 & S104 & S112 & S128).
destruct SMID as (S16 & S24 & S48 & S56 & S136 & S144 & S152 & S176).
repeat split;
  solve [ apply (gs_keep_gslot cx fp t W W' ms ms'); [exact HK | lia | exact Hhi |];
          first [exact S8 | exact S16 | exact S24 | exact S32 | exact S40 | exact S48 | exact S56
                | exact S72 | exact S80 | exact S104 | exact S112 | exact S128 | exact S136
                | exact S144 | exact S152 | exact S176] ].
Qed.

Lemma gs_keep_body : forall cx fp t pc pc' W W' ms ms' sh,
  gs_keepW cx fp t W W' (ms_mem ms) (ms_mem ms') ->
  spZ (c_regs cx) + 8 <= 2 ^ 64 -> c_sp1 cx + 192 <= 2 ^ 64 -> c_sp1 cx <= spZ (c_regs cx) - 288 ->
  c_p cx + c_n cx <= 2 ^ 64 ->
  ms_pc_val ms' = w64 (BASE + pc') -> ms_resv ms' = None -> ms_svc_pending ms' = None ->
  ms_rom ms' = seg_rom SEGS -> ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  gregs cx ms' ->
  ge_body cx fp pc W ms sh -> ge_body cx fp pc' W' ms' sh.
Proof.
intros cx fp t pc pc' W W' ms ms' sh HK Hsp1 Hhi Hlo Hpn Hpc Hrv Hsvc Hrom Hfr Hfc HR
  (_ & _ & _ & _ & _ & _ & _ & HSAVED & HSH & HFL & HLEN & HINP).
split; [exact Hpc|]. split; [exact Hrv|]. split; [exact Hsvc|]. split; [exact Hrom|].
split; [exact Hfr|]. split; [exact Hfc|]. split; [exact HR|].
split.
{ destruct HSAVED as (HRA & HS). split.
  - apply (gs_keep_word cx fp t W W' (ms_mem ms) (ms_mem ms')); [exact HK | | exact HRA].
    intros i Hi. left. unfold gs_keep_at. lia.
  - intros j Hj. apply (gs_keep_word cx fp t W W' (ms_mem ms) (ms_mem ms')); [exact HK | | exact (HS j Hj)].
    intros i Hi. left. unfold gs_keep_at. lia. }
split.
{ intros i Hi. rewrite (HK (gSH cx fp + Z.of_nat i)
    ltac:(unfold gs_keep_at; right; right; right; right; rewrite HLEN in Hi; unfold GE_NSH in *; lia)).
  exact (HSH i Hi). }
split.
{ apply (gs_keep_word cx fp t W W' (ms_mem ms) (ms_mem ms')); [exact HK | | exact HFL].
  intros i Hi. unfold gs_keep_at. right. right. right. left.
  assert (Hfb : fs_frame_bytes GE_CID = 1024) by (vm_compute; reflexivity). lia. }
split; [exact HLEN|].
apply (gs_keep_garr cx fp t W W' (ms_mem ms) (ms_mem ms')); [exact HK | | exact HINP].
intros j Hj. unfold gs_keep_at. right. right. left.
unfold c_n. lia.
Qed.

(* ---- the geometry: every byte the phase keeps lies outside one block ---- *)

Definition gs_geo (cx : ecx) (fp t b0 n0 : Z) : Prop :=
  alloc_ceiling <= c_sp1 cx /\ c_sp1 cx + 192 <= 2 ^ 64 /\
  (t + 460 <= b0 \/ b0 + req_size n0 <= t) /\
  (0 < c_n cx -> c_p cx + req_size (c_n cx) <= b0 \/ b0 + req_size n0 <= c_p cx) /\
  (gF cx fp + fs_frame_bytes GE_CID <= b0 \/ b0 + req_size n0 <= gF cx fp) /\
  (gSH cx fp + Z.of_nat GE_NSH <= b0 \/ b0 + req_size n0 <= gSH cx fp).

(* The frame's shadow never meets a block: a block lies under the low shadow or over
   the high memory start, and the shadow of an address under the ceiling lies between. *)
Lemma gs_shadow_block : forall (b0 n0 F : Z),
  in_app b0 (req_size n0) -> 0 <= F -> F + fs_frame_bytes GE_CID <= alloc_ceiling ->
  shadow_of_addr SHADOW_OFF F + Z.of_nat GE_NSH <= b0 \/ b0 + req_size n0 <= shadow_of_addr SHADOW_OFF F.
Proof.
intros b0 n0 F Happ HF0 HF1.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hfb : fs_frame_bytes GE_CID = 1024) by (vm_compute; reflexivity).
assert (Hd0 : 0 <= F / 8) by (apply Z.div_pos; lia).
assert (Hd1 : F / 8 <= 17592184995840) by (apply Z.div_le_upper_bound; lia).
destruct Happ as (H1 & [H2 | (H2 & H3)]).
- right. unfold shadow_of_addr, SHADOW_OFF, kLowShadowBeg in *. lia.
- left. unfold shadow_of_addr, SHADOW_OFF, GE_NSH, kHighMemBeg in *. cbn [Z.of_nat]. lia.
Qed.

Lemma gs_geo_of : forall cx fp t b0 n0 ly3 S3 W3 m md3,
  AR_laws SEGS B -> AR SEGS B ly3 S3 W3 m md3 ->
  In (t, 460) (ablocks B ly3 S3) -> (t, 460) <> (b0, n0) ->
  (0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3) /\ (c_p cx, c_n cx) <> (b0, n0)) ->
  In (b0, n0) (ablocks B ly3 S3) -> In (GE_CID, fp) (YG01.frames S3) ->
  frame_addr ly3 GE_CID fp = gF cx fp ->
  alloc_ceiling <= c_sp1 cx -> c_sp1 cx + 192 <= 2 ^ 64 ->
  gs_geo cx fp t b0 n0.
Proof.
intros cx fp t b0 n0 ly3 S3 W3 m md3 LAWS HAR Ht Hnt Hp Hb Hfr EFA Hsp1 Hsp1hi.
pose proof (sep_blocks SEGS B LAWS ly3 S3 W3 m md3 t 460 b0 n0 HAR Ht Hb Hnt) as Dt.
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 m md3 b0 n0 GE_CID fp HAR Hb Hfr) as Df.
destruct (al_blocks _ _ LAWS ly3 S3 W3 m md3 b0 n0 HAR Hb) as (_ & _ & _ & Happ & _).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 m md3 GE_CID fp HAR Hfr) as (HF0 & HF1 & _).
rewrite EFA in Df, HF0, HF1.
unfold zdisjoint in Dt, Df. cbn [fst snd] in Dt, Df.
change (req_size 460) with 460 in Dt.
split; [exact Hsp1|]. split; [exact Hsp1hi|].
split; [lia|].
split.
{ intros Hn. destruct (Hp Hn) as (Hpin & Hpne).
  pose proof (sep_blocks SEGS B LAWS ly3 S3 W3 m md3 (c_p cx) (c_n cx) b0 n0 HAR Hpin Hb Hpne) as Dp.
  unfold zdisjoint in Dp. cbn [fst snd] in Dp. lia. }
split; [lia|].
unfold gSH. apply (gs_shadow_block b0 n0 (gF cx fp) Happ); lia.
Qed.

(* ---- the two shapes of "the call kept it" ---- *)

Lemma gs_keep_of_call : forall cx fp t b0 n0 ly3 S3 W3 m W2 mem2 (Ex : Z -> Prop),
  acall_kept SEGS B ly3 S3 W3 m W2 mem2 (c_sp1 cx - ASTACK) (c_sp1 cx) Ex ->
  (forall a, Ex a -> b0 <= a < b0 + req_size n0) ->
  In (t, 460) (ablocks B ly3 S3) -> (0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3)) ->
  YG01.frames S3 = [(GE_CID, fp)] -> frame_addr ly3 GE_CID fp = gF cx fp ->
  gs_geo cx fp t b0 n0 ->
  gs_keepW cx fp t W3 W2 m mem2.
Proof.
intros cx fp t b0 n0 ly3 S3 W3 m W2 mem2 Ex HK HEx Ht Hp Hfrs EFA GEO a Ha.
assert (Hfb : fs_frame_bytes GE_CID = 1024) by (vm_compute; reflexivity).
assert (Hnsh : Z.of_nat GE_NSH = 104) by (vm_compute; reflexivity).
assert (Hfb8 : fs_frame_bytes GE_CID / 8 = 128) by (vm_compute; reflexivity).
destruct HK as (K1 & K2 & _ & K4 & _ & _).
destruct GEO as (Hceil & Hhi & Dt & Dp & Df & Dsh).
pose proof (req_size_pos (c_n cx) ltac:(unfold c_n; lia)) as [Hrq1 Hrq2].
rewrite Hfb in Df. rewrite Hnsh in Dsh.
destruct Ha as [Hstk | [Htr | [Hpr | [Hfrr | Hshr]]]].
- apply K1; lia.
- replace a with (t + (a - t)) by lia.
  apply (K2 t 460); [exact Ht | change (req_size 460) with 460; lia |].
  intros HE. apply HEx in HE. lia.
- assert (Hn : 0 < c_n cx) by lia.
  replace a with (c_p cx + (a - c_p cx)) by lia.
  apply (K2 (c_p cx) (c_n cx)); [exact (Hp Hn) | lia |].
  intros HE. apply HEx in HE. specialize (Dp Hn). lia.
- rewrite Hfb in Hfrr. refine (K4 GE_CID fp a _ _ _).
  + rewrite Hfrs. left. reflexivity.
  + left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA, Hfb. lia.
  + intros HE. apply HEx in HE. lia.
- rewrite Hnsh in Hshr. refine (K4 GE_CID fp a _ _ _).
  + rewrite Hfrs. left. reflexivity.
  + right. unfold in_zr. cbn [fst snd]. rewrite EFA, Hfb8.
    unfold gSH, shadow_addr, shadow_of_addr in *. lia.
  + intros HE. apply HEx in HE. lia.
Qed.

Lemma gs_keep_of_journal : forall cx fp t b0 n0 ly3 S3 W3 m md3 ly2 S2 W2 mem2 md2 STK1 FP1 k1,
  ajournal SEGS B STK1 (c_sp1 cx) FP1 ly3 S3 W3 m md3 [] ly2 S2 W2 mem2 md2 k1 ->
  (forall a, inFP FP1 a -> b0 <= a < b0 + req_size n0) ->
  ablocks B ly2 S2 = ablocks B ly3 S3 ->
  In (t, 460) (ablocks B ly3 S3) -> (0 < c_n cx -> In (c_p cx, c_n cx) (ablocks B ly3 S3)) ->
  YG01.frames S3 = [(GE_CID, fp)] -> frame_addr ly3 GE_CID fp = gF cx fp ->
  gs_geo cx fp t b0 n0 ->
  gs_keepW cx fp t W3 W2 m mem2.
Proof.
intros cx fp t b0 n0 ly3 S3 W3 m md3 ly2 S2 W2 mem2 md2 STK1 FP1 k1 HJ HFP Eab Ht Hp Hfrs EFA GEO a Ha.
assert (Hfb : fs_frame_bytes GE_CID = 1024) by (vm_compute; reflexivity).
assert (Hnsh : Z.of_nat GE_NSH = 104) by (vm_compute; reflexivity).
assert (Hfb8 : fs_frame_bytes GE_CID / 8 = 128) by (vm_compute; reflexivity).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & J1 & J2 & _ & J4 & _).
destruct GEO as (Hceil & Hhi & Dt & Dp & Df & Dsh).
pose proof (req_size_pos (c_n cx) ltac:(unfold c_n; lia)) as [Hrq1 Hrq2].
rewrite Hfb in Df. rewrite Hnsh in Dsh.
destruct Ha as [Hstk | [Htr | [Hpr | [Hfrr | Hshr]]]].
- apply J1; lia.
- replace a with (t + (a - t)) by lia.
  apply (J2 t 460); [exact Ht | rewrite Eab; exact Ht | change (req_size 460) with 460; lia |].
  intros HE. apply HFP in HE. lia.
- assert (Hn : 0 < c_n cx) by lia.
  replace a with (c_p cx + (a - c_p cx)) by lia.
  apply (J2 (c_p cx) (c_n cx)); [exact (Hp Hn) | rewrite Eab; exact (Hp Hn) | lia |].
  intros HE. apply HFP in HE. specialize (Dp Hn). lia.
- rewrite Hfb in Hfrr. refine (J4 GE_CID fp a _ _ _).
  + rewrite Hfrs. left. reflexivity.
  + left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA, Hfb. lia.
  + intros HE. apply HFP in HE. lia.
- rewrite Hnsh in Hshr. refine (J4 GE_CID fp a _ _ _).
  + rewrite Hfrs. left. reflexivity.
  + right. unfold in_zr. cbn [fst snd]. rewrite EFA, Hfb8.
    unfold gSH, shadow_addr, shadow_of_addr in *. lia.
  + intros HE. apply HFP in HE. lia.
Qed.

(* ---- the blocks of this phase are distinct ---- *)

Lemma gs_block_once : forall ly S W mem md (x : Z * Z) l1 l2 l3,
  AR_laws SEGS B -> AR SEGS B ly S W mem md -> 0 <= snd x ->
  ablocks B ly S = l1 ++ x :: l2 ++ x :: l3 -> False.
Proof.
intros ly S W mem md x l1 l2 l3 LAWS HAR Hx E.
assert (Hin : In (fst x, snd x) (ablocks B ly S))
  by (rewrite E; apply in_or_app; right; left; destruct x; reflexivity).
destruct (al_blocks _ _ LAWS ly S W mem md (fst x) (snd x) HAR Hin) as (_ & _ & _ & _ & _ & Hpw & _).
rewrite E, map_app in Hpw. cbn [map] in Hpw. rewrite map_app in Hpw. cbn [map] in Hpw.
pose proof (pairwise_dup zdisjoint _ _ _ _ Hpw) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. pose proof (req_size_pos (snd x) Hx). lia.
Qed.

Lemma gs_blocks_tail : forall ly S W mem md (pre : list (Z * Z)) (x y : Z * Z),
  AR_laws SEGS B -> AR SEGS B ly S W mem md -> 0 <= snd y ->
  ablocks B ly S = pre ++ [x; y] -> ~ In y (pre ++ [x]).
Proof.
intros ly S W mem md pre x y LAWS HAR Hy E Hin.
apply in_app_iff in Hin as [Hin | Hin].
- apply in_split in Hin as (a & b & ->).
  apply (gs_block_once ly S W mem md y a (b ++ [x]) [] LAWS HAR Hy).
  rewrite E, <- !app_assoc. cbn [app]. reflexivity.
- cbn in Hin. destruct Hin as [Heq | []]. subst x.
  apply (gs_block_once ly S W mem md y pre [] [] LAWS HAR Hy). rewrite E. reflexivity.
Qed.

(* ---- the input's row count is a byte ---- *)

Lemma gs_rd8_range : forall pl pos, 0 <= fst (GrantSlotPlan.rd8 pl pos) < 256.
Proof.
intros pl pos. unfold GrantSlotPlan.rd8. destruct (pos <? length pl)%nat; cbn [fst]; [|lia].
unfold GrantSlotPlan.pbz. pose proof (bv_unsigned_in_range 8 (nth pos pl (Z_to_bv 8 0))) as R.
change (bv_modulus 8) with 256 in R. exact R.
Qed.

Lemma gs_rows_range : forall pl, 0 <= sw_rows pl < 256.
Proof.
intros pl. unfold sw_rows, GrantSlotPlan.h_rows, GrantSlotPlan.header.
destruct (GrantSlotPlan.rd16 pl 0) as [u p1].
destruct (GrantSlotPlan.rd8 pl p1) as [i p2].
pose proof (gs_rd8_range pl p2) as Hr.
destruct (GrantSlotPlan.rd8 pl p2) as [r p3]. cbn [fst] in Hr. cbn [GrantSlotPlan.h_rows]. exact Hr.
Qed.

Lemma gs_mbytes_range : forall pl, 0 <= sw_mbytes pl <= 8670.
Proof.
intros pl. pose proof (gs_rows_range pl) as Hr. unfold sw_mbytes.
destruct (0 <? sw_rows pl) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; lia.
Qed.

(* A register a call keeps, read at its own width. *)
Lemma gs_kept_reg : forall (regs regs' : bvmap 5 word) (r : bv 5),
  aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r.
Proof.
intros regs regs' r H Hc. pose proof (H (bv_unsigned r) Hc) as Hr.
rewrite Z_to_bv_bv_unsigned in Hr. exact Hr.
Qed.

(* ---- memory kept outside an arbitrary set of addresses ---- *)
(* A run that writes one window of the machine frame keeps every other byte; these
   read a fact of a cut over whatever set of addresses the writer leaves alone. *)
Lemma gs_word_out : forall (W W' : world SEGS) (m m' : word -> option byte) (P : Z -> Prop) a v,
  (forall x, P x -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
  (forall i, 0 <= i < 8 -> P (a + i)) ->
  rdword (aview SEGS (w_H W) m) a = Some v -> rdword (aview SEGS (w_H W') m') a = Some v.
Proof.
intros W W' m m' P a v HK Hin Hr. unfold rdword in *.
rewrite (HK a ltac:(replace a with (a + 0) by lia; apply Hin; lia)).
rewrite (HK (a+1) ltac:(apply Hin; lia)). rewrite (HK (a+2) ltac:(apply Hin; lia)).
rewrite (HK (a+3) ltac:(apply Hin; lia)). rewrite (HK (a+4) ltac:(apply Hin; lia)).
rewrite (HK (a+5) ltac:(apply Hin; lia)). rewrite (HK (a+6) ltac:(apply Hin; lia)).
rewrite (HK (a+7) ltac:(apply Hin; lia)). exact Hr.
Qed.

Lemma gs_byte_out : forall (W W' : world SEGS) (m m' : word -> option byte) (P : Z -> Prop) a v,
  (forall x, P x -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) -> P a ->
  aview SEGS (w_H W) m a = Some v -> aview SEGS (w_H W') m' a = Some v.
Proof. intros W W' m m' P a v HK Ha Hr. rewrite (HK a Ha). exact Hr. Qed.

Lemma gs_garr_out : forall (W W' : world SEGS) (m m' : word -> option byte) (P : Z -> Prop) a (l : list byte),
  (forall x, P x -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
  (forall j, (j < length l)%nat -> P (a + Z.of_nat j)) ->
  garr8 SEGS (mrestrict (w_H W) m) a (map (fun b : byte => bv_unsigned b) l) ->
  garr8 SEGS (mrestrict (w_H W') m') a (map (fun b : byte => bv_unsigned b) l).
Proof.
intros W W' m m' P a l HK Hin HG j Hj.
rewrite length_map in Hj. destruct (HG j ltac:(rewrite length_map; exact Hj)) as [Hv Hr].
split; [|exact Hr].
intros kk Hk. assert (kk = 0%nat) as -> by lia. cbn [Z.of_nat]. rewrite Z.add_0_r.
specialize (Hv 0%nat ltac:(lia)). cbn [Z.of_nat] in Hv. rewrite Z.add_0_r in Hv.
rewrite (mbyte_of_aview SEGS (w_H W) (w_H W') m m' (a + Z.of_nat j) (HK (a + Z.of_nat j) (Hin j Hj))).
exact Hv.
Qed.

(* A byte the view gives, as the engine's data byte. *)
Lemma gs_mbyte_byte : forall (H : word -> bool) (mem : word -> option byte) a v,
  aview SEGS H mem a = Some v -> 0 <= v < 256 ->
  mbyte SEGS (mrestrict H mem) a = Some (Z_to_bv 8 v).
Proof.
intros H mem a v Hx Hv. unfold aview in Hx.
destruct (mbyte SEGS (mrestrict H mem) a) as [b|] eqn:Hb; [|discriminate].
cbn in Hx. injection Hx as Hx. f_equal. rewrite <- Hx. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* What an admitted box's two bytes are: fuzz_grant's own `fits`. *)
Lemma gs_ok_range : forall pl, ok pl = true ->
  0 <= sw_base pl /\ 1 <= sw_in pl <= 40 /\ sw_base pl + sw_in pl <= 48.
Proof.
intros pl H. unfold ok, fits in H. unfold sw_base, sw_in.
rewrite !andb_true_iff in H. destruct H as (((A & C) & D) & F).
apply Z.leb_le in A. apply Z.leb_le in C. apply Z.leb_le in D. apply Z.leb_le in F. lia.
Qed.

(* The same for a run that writes one window of the machine frame: the caller says
   which addresses the run left alone, and the four objects of `ge_body` are in it. *)
Lemma gs_body_out : forall cx fp pc pc' (P : Z -> Prop) W W' (ms ms' : machine_state) sh,
  (forall x, P x -> aview SEGS (w_H W') (ms_mem ms') x = aview SEGS (w_H W) (ms_mem ms) x) ->
  (forall a, spZ (c_regs cx) - 112 <= a < spZ (c_regs cx) -> P a) ->
  (forall i, 0 <= i < Z.of_nat GE_NSH -> P (gSH cx fp + i)) ->
  (forall i, 0 <= i < fs_frame_bytes GE_CID -> P (gF cx fp + i)) ->
  (forall i, 0 <= i < c_n cx -> P (c_p cx + i)) ->
  ms_pc_val ms' = w64 (BASE + pc') -> ms_resv ms' = None -> ms_svc_pending ms' = None ->
  ms_rom ms' = seg_rom SEGS -> ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  gregs cx ms' ->
  ge_body cx fp pc W ms sh -> ge_body cx fp pc' W' ms' sh.
Proof.
intros cx fp pc pc' P W W' ms ms' sh HK Hstk Hsh Hfr Hinp Hpc Hrv Hsvc Hrom Hfrg Hfc HR
  (_ & _ & _ & _ & _ & _ & _ & HSAVED & HSH & HFL & HLEN & HINP).
assert (Hfb : fs_frame_bytes GE_CID = 1024) by (vm_compute; reflexivity).
split; [exact Hpc|]. split; [exact Hrv|]. split; [exact Hsvc|]. split; [exact Hrom|].
split; [exact Hfrg|]. split; [exact Hfc|]. split; [exact HR|].
split.
{ destruct HSAVED as (HRA & HS). split.
  - apply (gs_word_out W W' (ms_mem ms) (ms_mem ms') P); [exact HK | | exact HRA].
    intros i Hi. apply Hstk. lia.
  - intros j Hj. apply (gs_word_out W W' (ms_mem ms) (ms_mem ms') P); [exact HK | | exact (HS j Hj)].
    intros i Hi. apply Hstk. lia. }
split.
{ intros i Hi. rewrite (HK (gSH cx fp + Z.of_nat i) ltac:(apply Hsh; rewrite HLEN in Hi; unfold GE_NSH in *; lia)).
  exact (HSH i Hi). }
split.
{ apply (gs_word_out W W' (ms_mem ms) (ms_mem ms') P); [exact HK | | exact HFL].
  intros i Hi. replace (gF cx fp + 1016 + i) with (gF cx fp + (1016 + i)) by lia. apply Hfr. lia. }
split; [exact HLEN|].
apply (gs_garr_out W W' (ms_mem ms) (ms_mem ms') P); [exact HK | | exact HINP].
intros j Hj. apply Hinp. unfold c_n. lia.
Qed.


End c.
End b.
End a.
