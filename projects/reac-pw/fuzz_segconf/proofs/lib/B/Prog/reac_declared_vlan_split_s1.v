(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the walk of reac_box_catalogue on fuzz_segconf.asan-ubsan (image B, pin sha256
   c3796c0b38f3, twin 80e82127e8ca; entry 0x8a8a0, 84 bytes, 21 instructions, a 16-byte frame, no side-stack
   frame): reac_box_catalogue_contract of lib/B/Prog/reac_box_catalogue_c.v (image B's copy of the image-A owner's FINAL
   text at 6f783602b5e3) at image B's numbers, in plugin-hostd/fuzz_command's lib/A/Prog form (afn_pre at the
   entry, SRr of apost_base at the return, over `Context {PI : PAImg seg_listing}` of image B's listing,
   lib/B/Prog/SegPa.v).
   ADAPTATION (relocation + one trap) of lib/A/Prog/reac_box_catalogueA.v (the image-A m_file-family lane, commit
   434ade288123, both arms): the same entry seeds, token runs and return steps over image B's listing modules and
   B's kit copies. The UBSan alignment check is read from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_catalogue.v
   at origin/ossv/recipes 3abc3740de97 (the same image-B code but 4 pc-relative words; caller-journal form, not
   copied), whose token run decides it the same way.
   Image B's code differs from image A's by two instructions: `andi a1,a0,7` (0x8a8ac) and `bnez a1,0x8a8ec`
   (0x8a8b0) to `unimp` (0x8a8ec), the UBSan alignment check of the 8-byte store through c.
   UBSan trap branch (one): 0x8a8b0 `bnez a1` -> unimp 0x8a8ec. Not taken: the c <> 0 run's entry seed carries the
   fact (10%nat, mkAF 4096 (2 ^ 47 - 8) 3) on a0 (rbc_facts: c is 2^3-aligned, from the contract premise
   c mod 8 = 0, seeded by rbc_entry), so the token executor (paj_run_tok, its branch step under facts_ok) computes
   a1 = c & 7 = 0 and decides the branch not taken; the trap instruction is never executed. The c = 0 run leaves at
   the beqz 0x8a8a8 (a0 pinned to 0) before the check.
   c <> 0: the instrumented check of the 8-byte cell (a load of the shadow byte at (c >> 3) + the shadow base, lbu
   0x8a8c8, and a compare, bnez 0x8a8cc) reads 0, because the contract's sa_addr gives the cell addressable; so the
   error path (the call of errpath_store8 at 0x8a8f0) is not reached; the sd at 0x8a8d4 writes 11 as 8 bytes. In
   both arms a0 = fuzz_catalogue (auipc/addi 0x8a8d8-0x8a8dc, 0xa20a0). The shadow base is the word the GOT cell
   as_got_shadow B holds (image B 0xa3210, the ld at 0x8a8b8, listing object 0; its target
   __asan_shadow_memory_dynamic_address 0xac7b8, listing object 12): the walk takes both from PALib (pal_got_shadow,
   pal_cell), a listing fact, not a contract premise.
   Positional names checked against image B's own listing (lib/B/Prog/SegAddr.v seg_objs, SegList.v) by address and
   anchor symbol (twin nm): A_OBJ 0 = 0xa3210 (the .got word the ld at 0x8a8b8 reads), A_OBJ 12 = 0xac7b8
   (__asan_shadow_memory_dynamic_address), A_OBJ 77 = RBC_CAT_OBJ = 0xa20a0 (fuzz_catalogue; SegList.v
   `PAddHi (10%bv : reg) (10%bv : reg) 123 (A_OBJ 77) 0x0` at 0x8a8dc), AF_reac_box_catalogue = 0x5ae0 =
   0x8a8a0 - seg_text 0x84dc0, atom 32 = the first extra env word (the shadow base SB, rbc_extra): 5 checked, 0
   pointing elsewhere.
   Image B's numbers of the statement: the entry BASE + AF_reac_box_catalogue; STK_reac_box_catalogue = 16 (the
   contract's STK comment: its frame, 0x8a8a0 addi sp,sp,-16 released at 0x8a8e4; the unimp at 0x8a8ec and the jal
   at 0x8a8f0 are the dead trap and error arms; no callee); cat = catA = 0xa20a0. Both are lib/B/Prog/SegInstB.v's
   definitions (SegInstA's names at image B): SegInstB.STK_reac_box_catalogue and SegInstB.catA, tied to this walk
   by the lemmas STK_reac_box_catalogue_B (the value 16) and catA_B (listing object 77 of B's seg_objs). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 324 of its 370 lines of code are new or changed and 407 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_declared_vlan_split_sl.v; 317 of its 402 lines of code are new or changed and 285 lines of the source are left out. *)
(* reac_declared_vlan_split on fuzz_segconf image B (fuzz_segconf.asan-ubsan): the point K1 (0x8a278, listing offset
   0x54b8), after the strrchr wrapper; a0 = r, the wrapper's answer (0, or the address of the last dot). Written for
   image B (image A's walk had no K1 file at commit ceb7e39832b2).
     0x8a278 `mv s4,a0`; 0x8a27c `li a0,0`; 0x8a280 `beqz s4` -> KR 0x8a324: no dot, vlan_split = None (vs_none_dot);
     0x8a284 `beq s4,s2` -> KR: the dot is the segment's first byte, di = 0 (vs_none_first);
     0x8a288 `li a0,-1`; 0x8a28c `beq s4,a0` -> the UBSan trap `unimp` 0x8a3d8: never taken, dot <= 2^47 - 2;
     0x8a290-0x8a2a0 the instrumented check C1 of the load1 of dot + 1 (slow path 0x8a3dc-0x8a3e0, error path
       0x8a3e4): dot + 1 lies in the segment's addressable range [segment, segment + length s + 1);
     0x8a2a4 `lbu a5,0(a0)` (dot[1], the entry's byte); 0x8a2a8 `beqz a5` -> 0x8a320 (`li a0,0`, KR): the tail is
       empty (vs_none_empty);
     0x8a2ac `addi a1,s4,2`; 0x8a2b0 `li a2,9`; 0x8a2b4 `li a3,-1`; 0x8a2b8 `mv a4,a0`; the loop head KL, pass 0. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0p YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaDenot PaSB PaLibG PaLibH PaLibF PaCallRun PaCall.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_split_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_split_lem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_split_k reac_declared_vlan_split_d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import reac_declared_vlan_split_r reac_declared_vlan_split_h.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the byte dot[1] the load at 0x8a2a4 reads: one byte at offset 1 from s4 = dot (atom 10), as atom 40 *)
Definition vs1_b_r : YP09.region := YP09.mkRegion (Some 10%nat) 1 2 0 0 [YP09.mkChunk 1 (CVal 1 (SOff 40 0))].
(* the shadow base s6 = SB (atom 22) and its span, as _s6.v's *)
Definition vs1_Bx : sv := SOff 22 0.
Definition vs1_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).

Lemma vs1_nth_app0 : forall (l : list Z) i, nth i (l ++ [0]) 0 = nth i l 0.
Proof.
intros l i. destruct (Nat.lt_ge_cases i (length l)) as [H|H].
- apply app_nth1. exact H.
- rewrite app_nth2 by exact H. rewrite (nth_overflow l) by exact H.
  destruct (i - length l)%nat as [|k]; [reflexivity|]. cbn [nth]. destruct k; reflexivity.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Lemma vs1_aview_byte : forall segs H mem a v, aview segs H mem a = Some v -> 0 <= v < 256.
Proof using.
intros segs H mem a v E. unfold aview in E.
destruct (mbyte segs (mrestrict H mem) a) as [b|]; [|discriminate]. cbn in E. injection E as <-.
pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. exact R.
Qed.
Lemma vs1_mbyte_of_aview : forall segs H mem a z, aview segs H mem a = Some z -> 0 <= z < 256 ->
  mbyte segs (mrestrict H mem) a = Some (Z_to_bv 8 z).
Proof using.
intros segs H mem a z Ha Hz. unfold aview in Ha. destruct (mbyte segs (mrestrict H mem) a) as [b|] eqn:Hb; [|discriminate].
cbn in Ha. injection Ha as <-. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma vs1_U_den : forall (E : env) v z, U E v = z -> 0 <= z < 2 ^ 64 -> sv_denot E v = Z_to_bv 64 z.
Proof using. intros E v z Hu Hz. unfold U in Hu. rewrite <- Hu. symmetry. apply Z_to_bv_bv_unsigned. Qed.
(* a run over regions without a write window leaves every memory cell as it was *)
Lemma vs1_frame_nowin : forall E rs (m m' : word -> option byte),
  frame_of E rs m m' -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> forall x, m' x = m x.
Proof using.
intros E rs m m' Hf Hw x. apply Hf. intros (r & Hr & Ha).
pose proof (proj1 (forallb_forall _ _) Hw r Hr) as H. apply Z.leb_le in H. lia.
Qed.

Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Lemma vs1_view_eq : forall H (m m' : word -> option byte), (forall x, m' x = m x) ->
  forall a, aview SEGS H m' a = aview SEGS H m a.
Proof using. intros H m m' Hm a. unfold aview, mbyte, mrestrict. cbv beta. rewrite Hm. reflexivity. Qed.
(* one byte b at a, as the region's chunk asks it *)
Lemma vs1_val_mem1 : forall m a b, 0 <= b < 256 -> mbyte SEGS m a = Some (Z_to_bv 8 b) -> val_mem SEGS m a 1 b.
Proof using.
intros m a b Hb Hm k Hk. assert (k = 0%nat) by lia. subst k.
change (a + Z.of_nat 0) with (a + 0). rewrite Z.add_0_r, Hm. do 2 f_equal.
lazymatch goal with |- b = ?f b ?w ?k =>
  change (f b w k) with (Z.shiftr (b mod 2 ^ (8 * Z.of_nat w)) (8 * Z.of_nat k) mod 256) end.
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite (Z.mod_small b 256) by lia. symmetry. apply Z.mod_small. lia.
Qed.
(* the shape the engine leaves an inline check's obligation in *)
Lemma vs1_obl_rd : forall E (W : world SEGS) m bx x a n, U E bx = SHADOW_OFF -> U E x = a ->
  range_addressable (aview SEGS (w_H W) m) SHADOW_OFF a n ->
  range_addressable (rd_of SEGS (mrestrict (w_H W) m)) (U E bx) (U E x) n.
Proof using. intros E W m bx x a n Hb Hx Hr. rewrite Hb, Hx. exact Hr. Qed.

Section e.
Variable B : asyms.
Variables gotw guard : Z.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* where an object of sa_loc lies: in [4096, alloc_ceiling), below every real-stack window (a heap block, a
   side-stack frame, or image bytes) *)
Lemma vs1_loc_low : forall ly S W mem md q n, AR SEGS B ly S W mem md ->
  sa_loc SEGS B ly S q n -> 0 < n -> 4096 <= q /\ q + n <= alloc_ceiling.
Proof using.
intros ly S W mem md q n HAR HL Hn.
pose proof (pa_img_range (L := seg_listing)) as HIMG. pose proof asan_consts as (C1 & _).
destruct HL as [(b & m & Hb & H1 & H2) | [(cid & pos & Hf & _ & H1 & H2) | HM]].
- destruct (al_blocks _ _ LAWS ly S W mem md b m HAR Hb) as (_ & B0 & B1 & B2 & _ & _ & Bm).
  pose proof (req_size_pos m ltac:(lia)) as [Q1 Q2]. lia.
- destruct (frames_bounds SEGS B LAWS ly S W mem md cid pos HAR Hf) as (F0 & F1 & F2).
  destruct F2 as [F2a _]. lia.
- destruct (HM q ltac:(lia)) as (Hq & _ & _). destruct (HM (q + n - 1) ltac:(lia)) as (Hq' & _ & _).
  pose proof (HIMG _ Hq). pose proof (HIMG _ Hq'). unfold kImgEnd in *. lia.
Qed.

(* the segment's byte i (i <= length s, the NUL at length s) reads at a body state as at the entry *)
Lemma vs1_byte : forall e regs' mem' md' i,
  vs_entry B gotw guard e -> vs_ctx0 B e regs' mem' md' -> (i <= length (e_s e))%nat ->
  rdW (e_W e) mem' (e_seg e + Z.of_nat i) = Some (nth i (e_s e) 0).
Proof using.
intros e regs' mem' md' i HE HC Hi.
pose proof HE as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & HSP & _).
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HSP as (Hs0 & Hstr & Hlen & Hsadd & Hamr & Hsloc & _).
pose proof HC as (_ & _ & _ & HK & _).
pose proof asan_consts as (C1 & _).
destruct (vs1_loc_low _ _ _ _ _ _ _ HAR Hsloc ltac:(lia)) as [L0 L1].
rewrite (HK (e_seg e + Z.of_nat i)); [| lia | unfold e_sp; lia | exact (fun h => h)].
destruct Hstr as ((Hzs & _) & _). rewrite <- vs1_nth_app0. apply Hzs. rewrite length_app. cbn [length]. lia.
Qed.

(* the shadow of a range below 2^47 reads at a later state of the body as at the entry: its shadow bytes lie below
   alloc_ceiling, outside the stack window *)
Lemma vs1_ra : forall e regs' mem' md' (m : word -> option byte) q n,
  vs_entry B gotw guard e -> vs_ctx0 B e regs' mem' md' -> (forall x, m x = mem' x) ->
  0 <= q -> q + n <= 2 ^ 47 ->
  range_addressable (rdW (e_W e) (e_mem e)) SHADOW_OFF q n -> range_addressable (rdW (e_W e) m) SHADOW_OFF q n.
Proof using.
intros e regs' mem' md' m q n HE HC Hm Hq Hn HRA.
pose proof HE as (HPRE & _).
pose proof HPRE as (HAR & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HC as (_ & _ & _ & HK & _).
pose proof asan_consts as (C1 & _).
apply (range_addressable_agree (rdW (e_W e) (e_mem e))); [|exact HRA].
intros x Hx. rewrite (vs1_view_eq _ mem' m Hm).
assert (Hs : 0 <= SHADOW_OFF + x / 8 < alloc_ceiling).
{ assert (H1 : 0 <= x / 8) by (apply Z.div_pos; lia).
  assert (H2 : x / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
  change (2 ^ 47 / 8) with 17592186044416 in H2. unfold SHADOW_OFF. lia. }
unfold shadow_of_addr. apply HK; [lia | unfold e_sp; lia | exact (fun h => h)].
Qed.

(* the context of the body at a later state of a stretch that wrote no memory *)
Lemma vs1_ctx0_step : forall e regs' mem' md' regs'' mem'' md'',
  vs_ctx0 B e regs' mem' md' ->
  ajournal SEGS B VS_STK (e_sp e) (e_FP e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) []
    (e_ly e) (e_S e) (e_W e) mem'' md'' 0 ->
  vs_regs e regs'' -> (forall x, mem'' x = mem' x) -> vs_ctx0 B e regs'' mem'' md''.
Proof using.
intros e regs' mem' md' regs'' mem'' md'' (_ & _ & HSL & HK & HP) HJ HR Hm.
split; [exact HJ|]. split; [exact HR|]. split.
{ apply (vs_slots_kept (rdW (e_W e) mem')); [exact HSL|]. intros a _. apply vs1_view_eq. exact Hm. }
split.
- intros a Ha Hw Hn. rewrite (vs1_view_eq _ mem' mem'' Hm). exact (HK a Ha Hw Hn).
- intros a Ha. destruct (HP a Ha) as [H0 (bb & Hb)]. split; [exact H0|]. exists bb. rewrite Hm. exact Hb.
Qed.

(* the registers the body keeps, from a run that kept sp, gp, tp, s0 .. s3 and s6 .. s11 *)
Lemma vs1_regs : forall e (regs' regs'' : bvmap 5 word), vs_regs e regs' ->
  (forall k, k = 2 \/ k = 3 \/ k = 4 \/ k = 8 \/ k = 9 \/ k = 18 \/ k = 19 \/ 22 <= k <= 27 ->
   getr regs'' (Z_to_bv 5 k) = getr regs' (Z_to_bv 5 k)) -> vs_regs e regs''.
Proof using.
intros e regs' regs'' (Hsp & G3 & G4 & G8 & G9 & G18 & G19 & G22 & G27) HK.
split; [unfold spZ in *; change (getr regs'' 2) with (getr regs'' (Z_to_bv 5 2)); rewrite (HK 2 ltac:(lia)); exact Hsp|].
split; [change (getr regs'' 3) with (getr regs'' (Z_to_bv 5 3)); rewrite (HK 3 ltac:(lia)); exact G3|].
split; [change (getr regs'' 4) with (getr regs'' (Z_to_bv 5 4)); rewrite (HK 4 ltac:(lia)); exact G4|].
split; [change (getr regs'' 8) with (getr regs'' (Z_to_bv 5 8)); rewrite (HK 8 ltac:(lia)); exact G8|].
split; [change (getr regs'' 9) with (getr regs'' (Z_to_bv 5 9)); rewrite (HK 9 ltac:(lia)); exact G9|].
split; [change (getr regs'' 18) with (getr regs'' (Z_to_bv 5 18)); rewrite (HK 18 ltac:(lia)); exact G18|].
split; [change (getr regs'' 19) with (getr regs'' (Z_to_bv 5 19)); rewrite (HK 19 ltac:(lia)); exact G19|].
split; [change (getr regs'' 22) with (getr regs'' (Z_to_bv 5 22)); rewrite (HK 22 ltac:(lia)); exact G22|].
intros r Hr. rewrite (HK r ltac:(lia)). exact (G27 r Hr).
Qed.

(* an exit to the epilogue KR with a0 = 0 from a stretch that wrote no memory, where vlan_split answers None *)
Lemma vs1_exit : forall e regs' mem' md' (ms : machine_state) md1,
  vs_KR_stmt B gotw guard -> vs_entry B gotw guard e -> vs_ctx0 B e regs' mem' md' ->
  SegModel.vlan_split (e_s e) = None ->
  (forall k, k = 2 \/ k = 3 \/ k = 4 \/ k = 8 \/ k = 9 \/ k = 18 \/ k = 19 \/ 22 <= k <= 27 ->
   getr (ms_regs ms) (Z_to_bv 5 k) = getr regs' (Z_to_bv 5 k)) ->
  (forall x, ms_mem ms x = mem' x) ->
  getr (ms_regs ms) 10 = w64 0 ->
  ajournal SEGS B VS_STK (e_sp e) (e_FP e) (e_ly e) (e_S e) (e_W e) (e_mem e) (e_md e) []
    (e_ly e) (e_S e) (e_W e) (ms_mem ms) md1 0 ->
  vs_goal B e (e_W e) (vs_cfg VS_KR (ms_regs ms) (ms_mem ms) md1).
Proof using.
intros e regs' mem' md' ms md1 HKR HE HC Hvs HRg Hm H10 HJ.
pose proof HC as (_ & HR & HSL & _).
apply (vs_exit_KR B gotw guard HKR e (e_ly e) (e_S e) (e_W e) regs' mem' (ms_regs ms) (ms_mem ms) md1 0 HE HR HSL HJ).
- intros k Hk. apply HRg. lia.
- intros a _. apply vs1_view_eq. exact Hm.
- exact H10.
- intros regs'' md'' H10''. unfold vs_Q. rewrite Hvs. split; [exact H10''|]. split; [exact I|]. split.
  + apply (vs_kept_step _ _ _ mem').
    * apply (vs_kept_ctxW B e (fun _ => False) _ regs' mem' md' HC). intros a Ha. exact (False_ind _ Ha).
    * intros a _ _ _. apply vs1_view_eq. exact Hm.
  + split; [apply Permutation_refl|]. split; [reflexivity|]. exists (st_fs (e_S e)). destruct (e_S e); reflexivity.
Qed.

Ltac vs1_ew := repeat (rewrite ew_ewset_other by lia).
Ltac vs1_lit := apply bv_eq; cbn [sv_denot]; unfold w64; rewrite !Z_to_bv_unsigned; reflexivity.
(* chain the memory of the state after a run to mem' (no region of these runs has a write window) *)
Ltac vs1_mem HF Hm :=
  let Hn := fresh "Hn" in
  pose proof (vs1_frame_nowin _ _ _ _ HF ltac:(vm_compute; reflexivity)) as Hn;
  lazymatch type of Hn with forall x, ?a x = _ =>
  lazymatch type of Hm with forall x, _ = ?m0 x =>
    let H' := fresh "Hm" in
    assert (H' : forall x, a x = m0 x) by (intros x; rewrite Hn; apply Hm);
    clear Hn Hm HF; rename H' into Hm end end.
(* a register the stretch did not write is its atom *)
Ltac vs1_ratoms HS EV :=
  let k := fresh "k" in let Hk := fresh "Hk" in let Hcases := fresh "Hcases" in
  intros k Hk;
  assert (Hcases : k = 2 \/ k = 3 \/ k = 4 \/ k = 8 \/ k = 9 \/ k = 18 \/ k = 19 \/ k = 22 \/ k = 23 \/ k = 24 \/
    k = 25 \/ k = 26 \/ k = 27) by lia;
  clear Hk;
  repeat (destruct Hcases as [-> | Hcases]); try subst k;
  lazymatch goal with |- getr _ (Z_to_bv 5 ?kk) = _ =>
    let n := eval compute in (Z.to_nat kk) in
    eapply (vs_reg_atom _ _ _ _ _ n _ HS); [vs1_ew; apply EV; reflexivity | vm_compute; reflexivity] end.

Lemma vs_K1 : vs_KR_stmt B gotw guard -> vs_KL_stmt B gotw guard 0 -> vs_K1_stmt B gotw guard.
Proof using.
intros HKR HKL. unfold vs_K1_stmt. intros e regs' mem' md' r HE HC R10 Hr.
pose proof HE as (HPRE & HROD & H10 & B10 & H11 & B11 & H12 & H13 & B13 & HSP & Hnev).
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HC as (HJ & HR & HSL & HK & HPR).
pose proof HR as (Hsp & G3 & G4 & G8 & G9 & G18 & G19 & G22 & G27).
pose proof HSP as (Hs0 & Hstr & Hlen & Hsadd & Hamr & Hsloc & Hp0 & Hcap & Hpdst & Hpadd & Hpdisj & Hv0 & Hv2 & Hvdst & Hvadd & Hvdisj & Hssp).
pose proof Hsadd as (Sa0 & Sa63 & _ & Sra & _).
assert (HVS : VS_STK = 12352) by reflexivity.
assert (Hnul : SegModel.nulfree (e_s e)) by exact (proj2 (proj1 Hstr)).
destruct (vs1_loc_low _ _ _ _ _ _ _ HAR Hsloc ltac:(lia)) as [L0 L1].
unfold e_sp in *.
assert (Hm0 : forall x, mem' x = mem' x) by (intros x; reflexivity).
destruct Hr as [(Hr0 & Hd) | (di & Hd & Hrd)].
{ (* r = 0: the segment has no dot *)
  subst r.
  assert (Hvs : SegModel.vlan_split (e_s e) = None)
    by (rewrite (vs_code_eq _ Hnul Hlen); apply vs_none_dot; exact Hd).
  set (E := Eimg (Ereg regs' (vs_xs (e_regs e) ++ []))).
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EV : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs' r)
    by (intros n r0 Hn; subst E; apply vs_EE; exact Hn).
  assert (HS : st_ok_pi SEGS VAL E (vs_ssK VS_K1 [])
    (restrict (w_H (e_W e)) (mkst regs' (Z_to_bv 64 (BASE + VS_K1)) mem' (seg_rom SEGS)))).
  { apply vs_seedK; [ | lia | | exact G22 | exact I].
    - replace (spZ regs' + 64) with (spZ (e_regs e)) by lia. exact HSL.
    - rewrite Hsp. replace (spZ (e_regs e) - 64) with (spZ (e_regs e) + (-4) * 16) by lia.
      rewrite Z_mod_plus_full. exact Hal16. }
  clearbody E.
  assert (U10 : U E (SOff 10 0) = 0) by (apply U_atom; [rewrite (EV 10%nat 10%bv eq_refl); exact R10 | lia]).
  assert (SHOK0 : sh_ok SEGS vs1_Bx [] E (mrestrict (w_H (e_W e)) mem')) by (unfold sh_ok; apply Forall_nil).
  unfold vs_goal, vs_cfg.
  (* 0x8a278 `mv s4,a0`, 0x8a27c `li a0,0`, up to 0x8a280 `beqz s4` *)
  paj_run_tok RUN HS HJ SHOK0 vs1_Bspan.
  { vs_awr_ro. }
  vs1_mem HF Hm0. clear HFr HG.
  psrr_branch_tok RUN BR HS SHOK0 vs1_Bspan.
  - (* 0x8a280 `beqz s4` taken: return 0 *)
    paj_run_to_tok RUNTO HS HJ SHOK0 vs1_Bspan VS_KR.
    { vs_awr_ro. }
    vs1_mem HF Hm0. clear HFr HG.
    pmkst HS.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
      apply (vs1_exit e regs' mem' md' msx _ HKR HE HC Hvs) end.
    + vs1_ratoms HS EV.
    + exact Hm0.
    + vs_preg HS (10%bv : bv 5) F10. rewrite F10. reflexivity.
    + exact HJ.
  - (* not taken: s4 = r = 0 *)
    exfalso. rewrite branch_eq_U, U10 in Hc. rewrite U_lit in Hc by lia. cbn in Hc. discriminate Hc. }
(* the last dot at di: r = segment + di *)
subst r.
pose proof (vs_di_lt _ _ Hnul Hd) as Hdil.
set (b := nth (S di) (e_s e) 0).
assert (Rb : rdW (e_W e) mem' (e_seg e + Z.of_nat di + 1) = Some b).
{ replace (e_seg e + Z.of_nat di + 1) with (e_seg e + Z.of_nat (S di)) by lia.
  exact (vs1_byte e regs' mem' md' (S di) HE HC ltac:(lia)). }
pose proof (vs1_aview_byte _ _ _ _ _ Rb) as Hb.
set (E := Eimg (Ereg regs' (vs_xs (e_regs e) ++ [Z_to_bv 64 b]))).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EV : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs' r)
  by (intros n r0 Hn; subst E; apply vs_EE; exact Hn).
assert (E40 : ew E 40 = Z_to_bv 64 b) by (subst E; exact (vs_Ey regs' (e_regs e) [Z_to_bv 64 b] 0 ltac:(lia))).
assert (E10 : ew E 10 = w64 (e_seg e + Z.of_nat di)) by (rewrite (EV 10%nat 10%bv eq_refl); exact R10).
assert (E18 : ew E 18 = w64 (e_seg e)) by (rewrite (EV 18%nat 18%bv eq_refl); exact G18).
assert (E22 : ew E 22 = w64 SB) by (rewrite (EV 22%nat 22%bv eq_refl); exact G22).
assert (E10u : bv_unsigned (ew E 10) = e_seg e + Z.of_nat di) by (rewrite E10; unfold w64; apply unsigned_lit_small; lia).
assert (E40u : bv_unsigned (ew E 40) = b) by (rewrite E40; apply unsigned_lit_small; lia).
assert (E2u : bv_unsigned (ew E 2) = spZ (e_regs e) - 64) by (rewrite (EV 2%nat 2%bv eq_refl); exact Hsp).
(* atom 10 = dot in [4096, 2^47 - 2]: the segment lies in [4096, alloc_ceiling) (split_pre's sa_loc, vs1_loc_low)
   and di < length s (vs_di_lt). The bound below 2^47 also puts the shadow byte of dot + 1 in the span vs1_Bspan,
   which the run's instrumented check C1 needs. *)
assert (HS : st_ok_pi SEGS VAL E (vs_ssK VS_K1 [(10%nat, mkAF 4096 (2 ^ 47 - 2) 0); (40%nat, mkAF 0 255 0)])
  (restrict (w_H (e_W e)) (mkst regs' (Z_to_bv 64 (BASE + VS_K1)) mem' (seg_rom SEGS)))).
{ apply vs_seedK; [ | lia | | exact G22 | ].
  - replace (spZ regs' + 64) with (spZ (e_regs e)) by lia. exact HSL.
  - rewrite Hsp. replace (spZ (e_regs e) - 64) with (spZ (e_regs e) + (-4) * 16) by lia.
    rewrite Z_mod_plus_full. exact Hal16.
  - cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E. rewrite E10u, E40u.
    rewrite !Z.pow_0_r, !Z.mod_1_r. repeat split; first [exact I | lia]. }
clearbody E.
(* the byte dot[1] (the entry's: vs1_byte, from split_pre's sa_str) as a region of the state *)
assert (Rok : region_ok SEGS E (mrestrict (w_H (e_W e)) mem') vs1_b_r).
{ unfold region_ok, vs1_b_r. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E10u. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (e_seg e + Z.of_nat di) 1 1 (SOff 40 0) b);
    [apply vs1_U_den; [apply U_atom; [exact E40 | lia] | lia] | zside | zside |].
  apply vs1_val_mem1; [exact Hb|].
  apply vs1_mbyte_of_aview; [exact Rb | exact Hb]. }
lazymatch type of HS with st_ok_pi _ _ _ ?ss ?msx =>
assert (Rdj : all_disjoint E vs1_b_r (ss_mem ss));
[ cbn [ss_mem vs_ssK all_disjoint]; unfold extent_disjoint;
  cbn [vs1_b_r vs_slots_r YP09.r_base YP09.r_lo YP09.r_hi base_val];
  rewrite E10u, E2u; split; [lia | exact I]
| pose proof (st_ok_pi_add_region E ss msx vs1_b_r HS eq_refl Rok Rdj) as HS2; clear HS; rename HS2 into HS ] end.
assert (UB : U E vs1_Bx = SHADOW_OFF) by (unfold vs1_Bx; apply U_atom; [rewrite E22; reflexivity | unfold SHADOW_OFF; lia]).
assert (U10 : U E (SOff 10 0) = e_seg e + Z.of_nat di) by (apply U_atom; [exact E10 | lia]).
assert (U18 : U E (SOff 18 0) = e_seg e) by (apply U_atom; [exact E18 | lia]).
assert (SHOK0 : sh_ok SEGS vs1_Bx [] E (mrestrict (w_H (e_W e)) mem')) by (unfold sh_ok; apply Forall_nil).
unfold vs_goal, vs_cfg.
(* 0x8a278 `mv s4,a0`, 0x8a27c `li a0,0`; 0x8a280 `beqz s4` not taken, decided by the run from atom 10's seed
   fact (dot >= 4096); up to 0x8a284 `beq s4,s2` *)
paj_run_tok RUN HS HJ SHOK0 vs1_Bspan.
{ vs_awr_ro. }
vs1_mem HF Hm0. clear HFr HG.
psrr_branch_tok RUN BR HS SHOK0 vs1_Bspan.
- (* 0x8a284 `beq s4,s2` taken: the dot is the segment's first byte, di = 0: return 0 *)
  rewrite branch_eq_U, U10, U18 in Hc. apply Z.eqb_eq in Hc.
  assert (Hdi0 : di = 0%nat) by lia. rewrite Hdi0 in Hd.
  assert (Hvs : SegModel.vlan_split (e_s e) = None)
    by (rewrite (vs_code_eq _ Hnul Hlen); apply vs_none_first; exact Hd).
  paj_run_to_tok RUNTO HS HJ SHOK0 vs1_Bspan VS_KR.
  { vs_awr_ro. }
  vs1_mem HF Hm0. clear HFr HG.
  pmkst HS.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    apply (vs1_exit e regs' mem' md' msx _ HKR HE HC Hvs) end.
  + vs1_ratoms HS EV.
  + exact Hm0.
  + vs_preg HS (10%bv : bv 5) F10. rewrite F10. reflexivity.
  + exact HJ.
- (* 0x8a284 not taken: di <> 0 *)
  rewrite branch_eq_U, U10, U18 in Hc. apply Z.eqb_neq in Hc.
  assert (Hdi0 : di <> 0%nat) by (intros H0; apply Hc; rewrite H0; lia). clear Hc.
  (* 0x8a288 `li a0,-1`; 0x8a28c `beq s4,a0` -> unimp 0x8a3d8: refuted by the run itself: atom 10's seed fact
     dot <= 2^47 - 2 (from split_pre's sa_loc segment (length s + 1): segment + length s + 1 <= alloc_ceiling <
     2^47, vs1_loc_low; and vs_di_lt: di < length s) makes decide_cond2 answer "not taken" (dot <> 2^64 - 1).
     0x8a290-0x8a2a0 the instrumented check C1 of the load1 of dot + 1 (slow path 0x8a3dc, error path 0x8a3e4): its
     obligation is range_addressable [dot + 1, dot + 2), inside split_pre's sa_addr range [segment, segment +
     length s + 1) (dot + 1 = segment + di + 1 <= segment + length s), whose shadow the body has not written
     (vs1_ra: vs_ctx0 keeps every byte outside the stack window).
     0x8a2a4 `lbu a5,0(a0)` reads the region vs1_b_r; up to 0x8a2a8 `beqz a5` *)
  paj_run_tok RUN HS HJ SHOK0 vs1_Bspan.
  {
    lazymatch goal with |- range_addressable _ (U ?Ex ?bx) (U ?Ex ?x) ?n =>
      apply (vs1_obl_rd Ex (e_W e) _ bx x (e_seg e + Z.of_nat (S di)) n) end.
    - unfold vs1_Bx. apply U_atom; [vs1_ew; rewrite E22; reflexivity | unfold SHADOW_OFF; lia].
    - lazymatch goal with |- U ?Ex (SOff 10 ?c) = _ =>
        rewrite (U_atom_off Ex 10 (e_seg e + Z.of_nat di) c) by first [lia | (vs1_ew; exact E10)] end. lia.
    - apply (vs1_ra e regs' mem' md' _ _ _ HE HC Hm0); [lia | lia |].
      apply (range_addressable_sub _ _ (e_seg e) (Z.of_nat (length (e_s e)) + 1)); [exact Sra | lia | lia]. }
  { vs_awr_ro. }
  vs1_mem HF Hm0. clear HFr HG.
  psrr_branch_tok RUN BR HS SHOK0 vs1_Bspan.
  + (* 0x8a2a8 `beqz a5` taken: dot[1] is the NUL, the tail is empty: return 0 by 0x8a320 *)
    rewrite branch_eq_U, U_lit in Hc by lia.
    lazymatch type of Hc with context [U ?Ex (SOff 40 0)] =>
      rewrite (U_atom Ex 40 b) in Hc by first [lia | (vs1_ew; exact E40)] end.
    apply Z.eqb_eq in Hc.
    assert (Hend : skipn (S di) (e_s e) = []).
    { apply skipn_all2. destruct (Nat.lt_ge_cases (S di) (length (e_s e))) as [Hlt|Hge]; [|exact Hge].
      exfalso. apply Hnul. rewrite <- Hc. unfold b. apply nth_In. exact Hlt. }
    assert (Hvs : SegModel.vlan_split (e_s e) = None)
      by (rewrite (vs_code_eq _ Hnul Hlen); exact (vs_none_empty _ di Hd Hend)).
    paj_run_to_tok RUNTO HS HJ SHOK0 vs1_Bspan VS_KR.
    { vs_awr_ro. }
    vs1_mem HF Hm0. clear HFr HG.
    pmkst HS.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
      apply (vs1_exit e regs' mem' md' msx _ HKR HE HC Hvs) end.
    * vs1_ratoms HS EV.
    * exact Hm0.
    * vs_preg HS (10%bv : bv 5) F10. rewrite F10. reflexivity.
    * exact HJ.
  + (* 0x8a2a8 not taken: dot[1] <> 0; 0x8a2ac-0x8a2b8 set up the digit loop, KL with j = 0 *)
    rewrite branch_eq_U, U_lit in Hc by lia.
    lazymatch type of Hc with context [U ?Ex (SOff 40 0)] =>
      rewrite (U_atom Ex 40 b) in Hc by first [lia | (vs1_ew; exact E40)] end.
    apply Z.eqb_neq in Hc.
    assert (Hlt : (S di < length (e_s e))%nat).
    { destruct (Nat.lt_ge_cases (S di) (length (e_s e))) as [Hlt|Hge]; [exact Hlt|].
      exfalso. apply Hc. unfold b. apply nth_overflow. exact Hge. }
    paj_run_to_tok RUNTO HS HJ SHOK0 vs1_Bspan VS_KL.
    { vs_awr_ro. }
    vs1_mem HF Hm0. clear HFr HG.
    vs_preg HS (10%bv : bv 5) F10. vs_preg HS (11%bv : bv 5) F11. vs_preg HS (12%bv : bv 5) F12.
    vs_preg HS (13%bv : bv 5) F13. vs_preg HS (14%bv : bv 5) F14. vs_preg HS (15%bv : bv 5) F15.
    vs_preg HS (20%bv : bv 5) F20.
    pmkst HS.
    lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
      apply (HKL e (ms_regs msx) (ms_mem msx) _ di HE) end.
    * apply (vs1_ctx0_step e regs' mem' md' _ _ _ HC HJ); [|exact Hm0].
      apply (vs1_regs e regs'); [exact HR | vs1_ratoms HS EV].
    * exact Hd.
    * exact Hdi0.
    * rewrite Nat.add_0_r. exact Hlt.
    * reflexivity.
    * rewrite F10. apply vs1_U_den; [|lia].
      rewrite (U_atom_off _ 10 (e_seg e + Z.of_nat di) 1) by first [lia | (vs1_ew; exact E10)]. lia.
    * rewrite F11. apply vs1_U_den; [|lia].
      rewrite (U_atom_off _ 10 (e_seg e + Z.of_nat di) 2) by first [lia | (vs1_ew; exact E10)]. lia.
    * rewrite F12. vs1_lit.
    * rewrite F13. vs1_lit.
    * rewrite F14. apply vs1_U_den; [|lia].
      rewrite (U_atom_off _ 10 (e_seg e + Z.of_nat di) 1) by first [lia | (vs1_ew; exact E10)]. lia.
    * rewrite Nat.add_0_r. change (nth (S di) (e_s e) 0) with b. rewrite F15. apply vs1_U_den; [|lia].
      apply U_atom; [vs1_ew; exact E40 | lia].
    * rewrite F20. apply vs1_U_den; [|lia]. apply U_atom; [vs1_ew; exact E10 | lia].
Qed.
End e.
End f.
End d.
