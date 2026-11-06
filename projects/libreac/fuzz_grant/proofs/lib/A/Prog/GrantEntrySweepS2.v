(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySweepDefs), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v, proofs/cgif/cgif_file_fuzzer/lib/A/ACeg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySweepDefs.v, with its module names changed; 331 of its 364 lines of code are new or changed and 128 lines of the source are left out. *)
(* Segment 2 of the sweep phase: 0x80ef4 -> 0x81000, the inlined check_row loop
   (fuzz_grant.c:313-314, check_row at :94-113), by induction on the rows left.

   One turn of the loop, row j of the sweep at s + 34 * j, is walked on the
   position-abstract listing from 0x80ef4: the sum of the 32 bytes from offset 2
   (0x80f0c..0x80f30, unrolled by the engine), the four leading bytes and the low byte
   of the sum, each against a branch to the error path at 0x81a0c, then the loop test
   at 0x80fc4. The row's 34 bytes are data slot 0 of the environment, its address is
   atom 32, and the engine reads s + j * 34 (s in s5, j in a3) as atom 32 by an alias
   fact. The shadow bytes of the row are read through the shadow entry (atom 32, 0, 34),
   which the sweep block's own shadow gives. The branches to 0x81a0c are not taken
   because every row of the sweep is a `rowok` row of fuzz_grant's own model
   (SweepRowCheck.sweep_rows_ok, rowok_split). The loop writes no memory, so the
   memory, and with it every memory fact of the cut, is kept. *)
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
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YC5d YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaJournal GrantSyms GrantList GrantPa GrantPaLib GrantBase GrantRo GrantEntryDefs GrantEntrySweepDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import
HeadampModel GrantModel GrantSweepModel BuildSweepModel SweepRowCheck GrantSlotPlan.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require SlotNeeds_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ---- the symbolic state at 0x80ef4 ---- *)
(* The shadow offset is in s7 (x23): atom 23 is the shadow base. *)
Definition rw_Bx : sv := SOff 23 0.
Definition rw_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* The 34 bytes of the row are addressable. *)
Definition rw_SH : list shent := [mkSHE 32 0 34].
(* a1 = a3 * 34 + s5 = s + 34 * j is the row's address, atom 32. *)
Definition rw_alias : sv := SAlu ALU_ADD (SMd M_MUL (SOff 13 0) (SLit 34)) (SOff 21 0).
(* The row, read-only: its bytes are data slot 0. *)
Definition rw_region : YP09.region := YP09.mkRegion (Some 32%nat) 0 34 0 0 [YP09.mkChunk 0 (CData 0 0 34)].
Definition rw_facts : facts :=
  mkFacts [(23%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 4096 0x7fffff800000 0)] [] [(rw_alias, SOff 32 0)].
(* a4 and t2 hold s + 34 * j + 2, a5 holds 34; every other register is its own atom. *)
Definition rw_sr : list sv :=
  sr_set (sr_set (sr_set sr_atoms (Z_to_bv 5 7) (SOff 32 2)) (Z_to_bv 5 14) (SOff 32 2)) (Z_to_bv 5 15) (SLit 34).
Definition ss_rw : sstate := mkSS GPS_rowhd rw_sr [rw_region] None rw_facts.

(* The sum the loop at 0x80f0c..0x80f30 leaves in t3, and its value. *)
Fixpoint rw_sum (n : nat) : sv :=
  match n with O => SLit 0 | S n' => SAlu ALU_ADD (rw_sum n') (SData 0 (2 + Z.of_nat n') 1) end.
Fixpoint rw_zsum (RB : list byte) (n : nat) : Z :=
  match n with O => 0 | S n' => rw_zsum RB n' + bv_unsigned (nth (2 + n') RB (Z_to_bv 8 0)) end.

(* ---- list and value facts ---- *)
Lemma firstn1_skipn : forall {A} (l : list A) n b, nth_error l n = Some b -> firstn 1 (skipn n l) = [b].
Proof.
intros A l. induction l as [|x l IH]; intros n b H; destruct n as [|n]; cbn in H |- *; try discriminate.
- injection H as ->. reflexivity.
- apply IH. exact H.
Qed.

Lemma U_data1 : forall E i b, 0 <= i -> nth_error (ed E 0) (Z.to_nat i) = Some b -> U E (SData 0 i 1) = bv_unsigned b.
Proof.
intros E i b Hi Hb. unfold U. cbn [sv_denot]. unfold data_word.
change (N.to_nat 1) with 1%nat. rewrite (firstn1_skipn _ _ _ Hb), bytes_le_single.
apply unsigned_lit_small. pose proof (u8_range b). lia.
Qed.

Lemma rw_zsum_range : forall RB n, 0 <= rw_zsum RB n <= 255 * Z.of_nat n.
Proof.
intros RB n. induction n as [|n IH]; cbn [rw_zsum]; [lia|].
pose proof (u8_range (nth (2 + n) RB (Z_to_bv 8 0))). lia.
Qed.

Lemma U_rw_sum : forall E n, (forall k, (k < n)%nat -> (2 + k < length (ed E 0))%nat) -> (n <= 32)%nat ->
  U E (rw_sum n) = rw_zsum (ed E 0) n.
Proof.
intros E n. induction n as [|n IH]; intros Hl Hn.
- cbn [rw_sum rw_zsum]. rewrite U_SLit. reflexivity.
- cbn [rw_sum rw_zsum]. rewrite U_SAlu. cbn [zalu_raw].
  rewrite IH by first [lia | intros kk Hkk; apply Hl; lia].
  rewrite (U_data1 E (2 + Z.of_nat n) (nth (2 + n) (ed E 0) (Z_to_bv 8 0))).
  + pose proof (rw_zsum_range (ed E 0) n). pose proof (u8_range (nth (2 + n) (ed E 0) (Z_to_bv 8 0))).
    apply zcanon_id. unfold M64. lia.
  + lia.
  + replace (Z.to_nat (2 + Z.of_nat n)) with (2 + n)%nat by lia. apply nth_error_nth'. apply Hl. lia.
Qed.

Lemma rw_zsum_row : forall rest, length rest = 30%nat ->
  rw_zsum (Z_to_bv 8 205 :: Z_to_bv 8 234 :: Z_to_bv 8 4 :: Z_to_bv 8 3 :: rest) 32 =
  bsum (Z_to_bv 8 4 :: Z_to_bv 8 3 :: rest).
Proof.
intros rest H.
do 30 (destruct rest as [|? rest]; [discriminate H | cbn [length] in H; injection H as H]).
destruct rest; [|discriminate H].
unfold bsum. cbn [rw_zsum nth Nat.add map fold_right]. lia.
Qed.

Lemma land255 : forall x, Z.land x 255 = x mod 256.
Proof. intros x. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma nth_error_concat34 : forall (L : list (list byte)) j i,
  Forall (fun r => length r = 34%nat) L -> (j < length L)%nat -> (i < 34)%nat ->
  nth_error (concat L) (34 * j + i) = nth_error (nth j L []) i.
Proof.
induction L as [|r L IH]; intros j i HL Hj Hi; cbn [length] in Hj; [lia|].
inversion HL as [|r0 L0 Hr HL']; subst r0 L0.
cbn [concat]. destruct j as [|j].
- cbn [nth]. replace (34 * 0 + i)%nat with i by lia. apply nth_error_app1. lia.
- cbn [nth]. rewrite nth_error_app2 by lia. rewrite Hr.
  replace (34 * S j + i - 34)%nat with (34 * j + i)%nat by lia. apply IH; [exact HL' | lia | exact Hi].
Qed.

Lemma length_sweep_rows_ge : forall base w vals, 8 + 3 * Z.of_nat w <= Z.of_nat (length (sweep_rows base w vals)).
Proof.
intros base w vals. unfold sweep_rows. cbn [length]. rewrite length_app. cbn [length].
rewrite length_flat_rows, length_seq. unfold ga_rows. cbn [length]. lia.
Qed.

(* ---- the tactics of the walk ---- *)
(* After a run of the engine: the regions are read-only, so the memory is the one the
   walk started from. *)
Ltac rw_mem mem0 :=
  lazymatch goal with HF : frame_of _ ?rs ?m (ms_mem ?msn) |- _ =>
    let H := fresh "HM" in
    pose proof (frame_of_read_only _ rs m (ms_mem msn) ltac:(vm_compute; reflexivity) HF) as H;
    tryif constr_eq m mem0 then idtac else
      (lazymatch m with ms_mem ?o =>
         lazymatch goal with HMo : ms_mem o = mem0 |- _ => rewrite HMo in H; clear HMo end end)
  end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* A register of the state the walk stopped in. *)
Ltac rw_reg HS :=
  lazymatch goal with |- getr (ms_regs ?ms0) ?r = _ =>
    let R := fresh "R" in prreg HS r R; rewrite R; clear R end.
Ltac rw_close :=
  repeat match goal with H : ew ?E ?n = _ |- context [ew ?E ?n] => rewrite H end;
  first [ reflexivity | unfold w64; rewrite ?unsigned_lit_small by lia; f_equal; lia ].
Ltac rw_keep HS ER := cbn [ms_regs mkst]; rw_reg HS; apply ER; reflexivity.
Ltac rw_val HS := cbn [ms_regs mkst]; rw_reg HS; rw_close.
(* The branch at 0x80f58 / 0x80f74 / 0x80f90 / 0x80fac: byte k of the row is V. *)
Ltac rw_byte Hc k V EV ED :=
  rewrite branch_ne_U in Hc;
  rewrite (U_data1 _ k (Z_to_bv 8 V)) in Hc; [| lia | cbn [ed ewset]; rewrite ED; reflexivity];
  rewrite (U_atom _ _ V) in Hc; [| cbn [ew ewset Nat.eqb]; exact EV | lia];
  vm_compute in Hc; discriminate Hc.
(* The branch at 0x80fb4: the low byte of the sum of bytes 2..33 is 0. *)
Ltac rw_sum_abort Hc ED Hrest Hsum :=
  rewrite branch_ne_U in Hc;
  rewrite U_and_lit in Hc by lia;
  rewrite U_lit in Hc by lia;
  lazymatch type of Hc with context [U ?E0 ?X] =>
    replace (U E0 X) with (U E0 (rw_sum 32)) in Hc by reflexivity end;
  rewrite U_rw_sum in Hc; [| intros kk Hkk; cbn [ed ewset]; rewrite ED; cbn [length]; rewrite Hrest; lia | lia];
  cbn [ed ewset] in Hc; rewrite ED in Hc;
  rewrite rw_zsum_row in Hc by exact Hrest;
  rewrite land255, Hsum in Hc; vm_compute in Hc; discriminate Hc.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section b. Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

(* Byte i of row j of the sweep, from the sweep's bytes and fuzz_grant's row model. *)
Lemma rw_row_mem : forall (m : word -> option byte) s pl t j i,
  garr8 SEGS m s (map (fun b : byte => bv_unsigned b) (sw_bytes pl t)) ->
  (j < length (sweep_rows (sw_base pl) (Z.to_nat (sw_in pl)) (sw_vals pl t)))%nat -> 0 <= i < 34 ->
  mbyte SEGS m (s + 34 * Z.of_nat j + i) =
  Some (nth (Z.to_nat i) (nth j (sweep_rows (sw_base pl) (Z.to_nat (sw_in pl)) (sw_vals pl t)) []) (Z_to_bv 8 0)).
Proof.
intros m s pl t j i HSW Hj Hi.
set (rows := sweep_rows (sw_base pl) (Z.to_nat (sw_in pl)) (sw_vals pl t)) in *.
assert (HL : Forall (fun r => length r = 34%nat) rows) by (apply Forall_rowok_len, sweep_rows_ok).
assert (Hlr : length (nth j rows []) = 34%nat).
{ rewrite Forall_forall in HL. apply HL. apply nth_In. exact Hj. }
unfold sw_bytes in HSW. rewrite SWEEP_rows in HSW. fold rows in HSW.
pose proof (nth_error_concat34 rows j (Z.to_nat i) HL Hj ltac:(lia)) as Hq.
rewrite (nth_error_nth' (nth j rows []) (Z_to_bv 8 0)) in Hq by lia.
assert (Hq' : (34 * j + Z.to_nat i < length (concat rows))%nat) by (apply nth_error_Some; rewrite Hq; discriminate).
pose proof (garr8_mbyte SEGS m s _ (34 * j + Z.to_nat i) HSW ltac:(rewrite length_map; exact Hq')) as Hb.
rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) in Hb by (rewrite length_map; exact Hq').
rewrite map_nth in Hb.
rewrite (nth_error_nth _ _ _ Hq) in Hb.
rewrite Z_to_bv_bv_unsigned in Hb.
replace (s + 34 * Z.of_nat j + i) with (s + Z.of_nat (34 * j + Z.to_nat i)) by lia. exact Hb.
Qed.

(* What a cut keeps when the machine moves on without writing memory. *)
Lemma ge_body_step : forall (cx : ecx) fp pc pc' W (ms ms' : machine_state) sh,
  ge_body cx fp pc W ms sh -> ms_mem ms' = ms_mem ms -> ms_pc_val ms' = w64 (BASE + pc') ->
  ms_resv ms' = None -> ms_svc_pending ms' = None -> ms_rom ms' = seg_rom SEGS ->
  ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  getr (ms_regs ms') 2 = getr (ms_regs ms) 2 -> getr (ms_regs ms') 8 = getr (ms_regs ms) 8 ->
  getr (ms_regs ms') 9 = getr (ms_regs ms) 9 -> getr (ms_regs ms') 3 = getr (ms_regs ms) 3 ->
  getr (ms_regs ms') 4 = getr (ms_regs ms) 4 ->
  ge_body cx fp pc' W ms' sh.
Proof.
intros cx fp pc pc' W ms ms' sh (_ & _ & _ & _ & _ & _ & (G2 & G8 & G9 & G3 & G4) & HSV & HSH & HFL & HLEN & HIN)
  Hm Hpc Hrv Hsv Hrom Hfr Hfc R2 R8 R9 R3 R4.
unfold ge_body, gregs, gsaved, gshadow in *. rewrite Hm, R2, R8, R9, R3, R4.
exact (conj Hpc (conj Hrv (conj Hsv (conj Hrom (conj Hfr (conj Hfc (conj (conj G2 (conj G8 (conj G9 (conj G3 G4))))
  (conj HSV (conj HSH (conj HFL (conj HLEN HIN))))))))))).
Qed.

Lemma gsw_rows_step : forall (cx : ecx) W (ms ms' : machine_state) t s,
  gsw_rows cx W ms t s -> ms_mem ms' = ms_mem ms -> gsw_rows cx W ms' t s.
Proof. intros cx W ms ms' t s H Hm. unfold gsw_rows in *. rewrite Hm. exact H. Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

Lemma gsw_blk_step : forall (cx : ecx) fp ly S W (ms ms' : machine_state) t s,
  gsw_blk B cx fp ly S W ms t s -> ms_mem ms' = ms_mem ms -> getr (ms_regs ms') 20 = getr (ms_regs ms) 20 ->
  gsw_blk B cx fp ly S W ms' t s.
Proof.
intros cx fp ly S W ms ms' t s H Hm H20.
unfold gsw_blk, gtab, gfarr, gslots_late, gslots_mid, gslot, gfb in *. rewrite Hm, H20. exact H.
Qed.

(* The loop, by induction on the rows left (cgif lib/A/AC8c.v:47, tcbl_loop). *)
Lemma gsw_rows_loop : forall (POST : ecx -> world SEGS -> config -> Prop),
  ge_from B MT POST (GIS_rowex B MT) ->
  forall (m : nat) (cx : ecx) (fp k acc : Z) ly3 S3 W3 (ms3 : machine_state) md3,
  Z.to_nat (sw_n (c_pl cx) - bv_unsigned (getr (ms_regs ms3) 13)) = m ->
  ge_base B MT cx ->
  ajournal SEGS B GE_STK (spZ (c_regs cx)) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(GE_CID, fp)] ly3 S3 W3 (ms_mem ms3) md3 k ->
  YG01.frames S3 = [(GE_CID, fp)] ->
  mo_le MT (c_S cx) S3 acc ->
  GIS_rowhd B MT cx fp k acc ly3 S3 W3 ms3 md3 ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).
Proof.
intros POST NEXT m. induction m as [|m IH];
intros cx fp k acc ly3 S3 W3 ms3 md3 Hm Hbase HJ Hfr Hmo HGI;
destruct HGI as (t & s & j & HBODY & Hk & Hacc & HBLK & HROWS & Hj & R13 & R10 & R14 & R7 & R21 & R23 & R22 & R18
  & R15 & R16 & R17 & R5 & R6);
pose proof HBLK as (_ & Hin & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R20 & _ & _ & Hs0 & _);
pose proof HROWS as (Hok & Hwant & HSW);
pose proof (proj1 HJ) as HAR;
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (Hal16 & H4096 & Hceil & Happ & _ & _ & Hmax);
pose proof asan_consts as (C1 & _);
assert (Hn : sw_n (c_pl cx) = sw_want (c_pl cx)) by (unfold sw_n; rewrite (proj2 (Z.leb_le _ _) Hwant); reflexivity);
assert (Hmb : sw_mbytes (c_pl cx) = 34 * sw_rows (c_pl cx))
  by (unfold sw_mbytes; rewrite (proj2 (Z.ltb_lt 0 _)) by lia; reflexivity);
pose proof (req_size_pos (sw_mbytes (c_pl cx)) ltac:(lia)) as Hreq;
rewrite R13 in Hm; unfold w64 in Hm; rewrite unsigned_lit_small in Hm by lia.
{ lia. }
(* ---- the machine state the walk starts from ---- *)
pose proof HBODY as (Hpc & Hrv & Hsv & Hrom & Hfrg & Hfcsr & (G2 & G8 & G9 & G3 & G4) & _).
destruct ms3 as [regs3 fregs3 pc3 svc3 resv3 fcsr3 mem3 rom3].
cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *.
subst fregs3 pc3 svc3 resv3 fcsr3 rom3.
change (SRr SEGS W3 (mkCfg (mkst regs3 (Z_to_bv 64 (BASE + GPS_rowhd)) mem3 (seg_rom SEGS)) md3) (POST cx)).
(* ---- row j of the sweep, from fuzz_grant's model ---- *)
assert (Lj : (j < length (sweep_rows (sw_base (c_pl cx)) (Z.to_nat (sw_in (c_pl cx))) (sw_vals (c_pl cx) t)))%nat).
{ pose proof (length_sweep_rows_ge (sw_base (c_pl cx)) (Z.to_nat (sw_in (c_pl cx))) (sw_vals (c_pl cx) t)) as HL.
  assert (Hw : sw_want (c_pl cx) = 8 + 3 * sw_in (c_pl cx)) by reflexivity. lia. }
assert (HRok : rowok (nth j (sweep_rows (sw_base (c_pl cx)) (Z.to_nat (sw_in (c_pl cx))) (sw_vals (c_pl cx) t)) [])).
{ apply (proj1 (Forall_forall _ _) (sweep_rows_ok (sw_base (c_pl cx)) (Z.to_nat (sw_in (c_pl cx))) (sw_vals (c_pl cx) t))).
  apply nth_In. exact Lj. }
pose proof (fun i Hi => rw_row_mem _ s (c_pl cx) t j i HSW Lj Hi) as MEMB.
destruct (rowok_split _ HRok) as (rest & HRB & Hrest & Hsum). rewrite HRB in MEMB. clear HRok.
(* ---- the environment: the registers, the row's address (atom 32), its bytes (slot 0) ---- *)
remember (Eimg (edset (Ereg regs3 [w64 (s + 34 * Z.of_nat j)]) 0
  (Z_to_bv 8 205 :: Z_to_bv 8 234 :: Z_to_bv 8 4 :: Z_to_bv 8 3 :: rest))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (ER : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs3 r).
{ intros n r Hnr. subst E. pose proof (u5_range r). rewrite Eimg_low by (unfold A_TEXT; lia).
  exact (ew_Ereg_nat regs3 _ n r Hnr). }
assert (E32 : ew E 32 = w64 (s + 34 * Z.of_nat j)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity).
assert (ED : ed E 0 = Z_to_bv 8 205 :: Z_to_bv 8 234 :: Z_to_bv 8 4 :: Z_to_bv 8 3 :: rest) by (subst E; reflexivity).
clear HE.
assert (E2 : ew E 2 = w64 (c_sp1 cx)) by (transitivity (getr regs3 2); [apply ER; reflexivity | exact G2]).
assert (E8 : ew E 8 = w64 (spZ (c_regs cx))) by (transitivity (getr regs3 8); [apply ER; reflexivity | exact G8]).
assert (E9 : ew E 9 = w64 (c_sp1 cx)) by (transitivity (getr regs3 9); [apply ER; reflexivity | exact G9]).
assert (E3 : ew E 3 = getr (c_regs cx) 3) by (transitivity (getr regs3 3); [apply ER; reflexivity | exact G3]).
assert (E4 : ew E 4 = getr (c_regs cx) 4) by (transitivity (getr regs3 4); [apply ER; reflexivity | exact G4]).
assert (E10 : ew E 10 = w64 (sw_n (c_pl cx))) by (transitivity (getr regs3 10); [apply ER; reflexivity | exact R10]).
assert (E13 : ew E 13 = w64 (Z.of_nat j)) by (transitivity (getr regs3 13); [apply ER; reflexivity | exact R13]).
assert (E21 : ew E 21 = w64 s) by (transitivity (getr regs3 21); [apply ER; reflexivity | exact R21]).
assert (E23 : ew E 23 = w64 SHADOW_OFF) by (transitivity (getr regs3 23); [apply ER; reflexivity | exact R23]).
assert (E22 : ew E 22 = w64 (gSH cx fp)) by (transitivity (getr regs3 22); [apply ER; reflexivity | exact R22]).
assert (E18 : ew E 18 = w64 (gF cx fp + GO_A)) by (transitivity (getr regs3 18); [apply ER; reflexivity | exact R18]).
assert (E16 : ew E 16 = w64 205) by (transitivity (getr regs3 16); [apply ER; reflexivity | exact R16]).
assert (E17 : ew E 17 = w64 234) by (transitivity (getr regs3 17); [apply ER; reflexivity | exact R17]).
assert (E5 : ew E 5 = w64 4) by (transitivity (getr regs3 5); [apply ER; reflexivity | exact R5]).
assert (E6 : ew E 6 = w64 3) by (transitivity (getr regs3 6); [apply ER; reflexivity | exact R6]).
assert (E20 : ew E 20 = w64 t) by (transitivity (getr regs3 20); [apply ER; reflexivity | exact R20]).
(* ---- the symbolic state and the shadow entry of the row ---- *)
assert (HS : st_ok_pi SEGS VAL E ss_rw (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + GPS_rowhd)) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_rw. apply pa_entry_st_ok_full.
  - apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
    repeat (destruct Hr as [<-|Hr];
      [ match goal with |- _ = sv_denot ?E0 (sr_get ?sr ?r0) =>
          let v := eval vm_compute in (sr_get sr r0) in change (sr_get sr r0) with v end;
        first [ rewrite getr_zero; reflexivity
              | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; symmetry; apply ER; reflexivity
              | cbn [sv_denot]; exact R15
              | cbn [sv_denot]; rewrite E32; unfold w64; rewrite unsigned_lit_small by lia;
                transitivity (w64 (s + 34 * Z.of_nat j + 2)); [first [exact R7 | exact R14] | unfold w64; f_equal; lia] ]
      | ]).
    destruct Hr.
  - vm_compute. reflexivity.
  - unfold rw_region. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E32. unfold w64. rewrite unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    intros i Hi. cbn [c_len YP09.c_val YP09.c_off cv_len] in Hi |- *.
    exists (nth (Z.to_nat i) (Z_to_bv 8 205 :: Z_to_bv 8 234 :: Z_to_bv 8 4 :: Z_to_bv 8 3 :: rest) (Z_to_bv 8 0)).
    cbn [cbyte]. rewrite ED. split.
    + rewrite Z.add_0_l. apply nth_error_nth'. cbn [length]. lia.
    + rewrite Z.add_0_r. exact (MEMB i Hi).
  - split; exact I.
  - split; [|split; [exact I|]].
    + cbn [rw_facts f_atoms atoms_ok]. split; [|split; [|exact I]]; unfold afact_ok; cbn [af_lo af_hi af_al2];
      [rewrite E23 | rewrite E32]; unfold w64; rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia);
      rewrite Z.pow_0_r, Z.mod_1_r; unfold SHADOW_OFF; lia.
    + cbn [rw_facts f_alias alias_ok]. split; [|exact I]. apply U_inj. unfold rw_alias.
      rewrite U_SAlu, U_SMd. cbn [zalu_raw zmd_raw].
      rewrite (U_atom E 13 (Z.of_nat j)) by first [exact E13 | lia].
      rewrite (U_lit E 34) by lia.
      rewrite (U_atom E 21 s) by first [exact E21 | lia].
      rewrite (U_atom E 32 (s + 34 * Z.of_nat j)) by first [exact E32 | lia].
      rewrite (zcanon_id (Z.of_nat j * 34)) by (unfold M64; lia).
      rewrite zcanon_id by (unfold M64; lia). lia. }
assert (SHOK : sh_ok SEGS rw_Bx rw_SH E (mrestrict (w_H W3) mem3)).
{ unfold sh_ok, rw_SH. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H W3) mem3 E rw_Bx 32 (s + 34 * Z.of_nat j) 34 (s + 34 * Z.of_nat j) 0 34).
  - eapply (range_addressable_of_block SEGS B LAWS _ _ _ _ _ _ _ _ _ HAR Hin); lia.
  - unfold rw_Bx. apply U_atom; [exact E23 | unfold SHADOW_OFF; lia].
  - apply U_atom; [exact E32 | lia].
  - lia.
  - lia.
  - intros x Hx. revert Happ Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia. }
(* ---- the walk: the sum, then row[0] = 0xcd (0x80f58) ---- *)
paj_run_tok RUN HS HJ SHOK rw_Bspan; [awr_ok_tac |].
rw_mem mem3.
psrr_branch_tok RUN BR HS SHOK rw_Bspan; [rw_byte Hc 0 205 E16 ED | clear Hc].
(* row[1] = 0xea (0x80f74) *)
paj_run_tok RUN HS HJ SHOK rw_Bspan; [awr_ok_tac |].
rw_mem mem3.
psrr_branch_tok RUN BR HS SHOK rw_Bspan; [rw_byte Hc 1 234 E17 ED | clear Hc].
(* row[2] = 4 (0x80f90) *)
paj_run_tok RUN HS HJ SHOK rw_Bspan; [awr_ok_tac |].
rw_mem mem3.
psrr_branch_tok RUN BR HS SHOK rw_Bspan; [rw_byte Hc 2 4 E5 ED | clear Hc].
(* row[3] = 3 (0x80fac) *)
paj_run_tok RUN HS HJ SHOK rw_Bspan; [awr_ok_tac |].
rw_mem mem3.
psrr_branch_tok RUN BR HS SHOK rw_Bspan; [rw_byte Hc 3 3 E6 ED | clear Hc].
(* the low byte of the sum is 0 (0x80fb4) *)
paj_run_tok RUN HS HJ SHOK rw_Bspan; [awr_ok_tac |].
rw_mem mem3.
psrr_branch_tok RUN BR HS SHOK rw_Bspan; [rw_sum_abort Hc ED Hrest Hsum | clear Hc].
(* the loop test at 0x80fc4 *)
paj_run_tok RUN HS HJ SHOK rw_Bspan; [awr_ok_tac |].
rw_mem mem3.
psrr_branch_tok RUN BR HS SHOK rw_Bspan.
- (* j + 1 < n: back to the head with j + 1 rows checked *)
  rewrite branch_ne_U in Hc.
  rewrite (U_atom_off _ 13 (Z.of_nat j) 1) in Hc; [| cbn [ew ewset Nat.eqb]; exact E13 | lia | lia].
  rewrite (U_atom _ 10 (sw_n (c_pl cx))) in Hc; [| cbn [ew ewset Nat.eqb]; exact E10 | lia].
  apply negb_true_iff, Z.eqb_neq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK rw_Bspan GPS_rowhd; [awr_ok_tac |].
  rw_mem mem3. pmkst HS.
  lazymatch goal with HM : ms_mem ?msf = mem3 |- _ => rewrite HM in HJ |- * end.
  apply (IH cx fp k acc ly3 S3 W3).
  + cbn [ms_regs mkst].
    lazymatch type of HS with context [restrict _ ?msf] =>
      assert (X : getr (ms_regs msf) 13 = w64 (Z.of_nat (S j))) by rw_val HS; rewrite X end.
    unfold w64. rewrite unsigned_lit_small by lia. lia.
  + exact Hbase.
  + exact HJ.
  + exact Hfr.
  + exact Hmo.
  + unfold GIS_rowhd. exists t, s, (S j).
    split; [eapply ge_body_step; [exact HBODY | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | reflexivity | reflexivity | rw_keep HS ER | rw_keep HS ER | rw_keep HS ER | rw_keep HS ER | rw_keep HS ER] |].
    split; [exact Hk|]. split; [exact Hacc|].
    split; [eapply gsw_blk_step; [exact HBLK | reflexivity | rw_keep HS ER] |].
    split; [eapply gsw_rows_step; [exact HROWS | reflexivity] |].
    split; [lia|].
    repeat (split; [rw_val HS|]). rw_val HS.
- (* j + 1 = n: on to 0x81000, every row checked *)
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK rw_Bspan GPS_rowex; [awr_ok_tac |].
  rw_mem mem3. pmkst HS.
  lazymatch goal with HM : ms_mem ?msf = mem3 |- _ => rewrite HM in HJ |- * end.
  apply (NEXT cx fp k acc ly3 S3 W3); [exact Hbase | exact HJ | exact Hfr | exact Hmo |].
  unfold GIS_rowex. exists t, s.
  split; [eapply ge_body_step; [exact HBODY | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | reflexivity | reflexivity | rw_keep HS ER | rw_keep HS ER | rw_keep HS ER | rw_keep HS ER | rw_keep HS ER] |].
  split; [exact Hk|]. split; [exact Hacc|].
  split; [eapply gsw_blk_step; [exact HBLK | reflexivity | rw_keep HS ER] |].
  split; [eapply gsw_rows_step; [exact HROWS | reflexivity] |].
  repeat (split; [rw_val HS|]). rw_val HS.
Qed.

End c.
End b.
End a.

Lemma gsw_seg_rows : forall {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}
  {PI : PAImg grant_listing} (B : asyms) (MT : ameter_ops), @SEG_rows fx rc SK PI B MT.
Proof.
intros fx rc SK PI B MT RT NEXT. destruct RT as (LAWS & _).
intros cx fp k acc ly3 S3 W3 ms3 md3 Hbase HJ Hfr Hmo HGI.
exact (gsw_rows_loop B MT LAWS (ge_post B MT) NEXT _ cx fp k acc ly3 S3 W3 ms3 md3 eq_refl Hbase HJ Hfr Hmo HGI).
Qed.
