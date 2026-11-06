(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of proofs/reac-pw/fuzz_role/lib/A/RPgX01.v at 9bffaa83ff88
   [Apache-2.0] (rx_reg_atom / rx_reg_ext / rx_ew_reg / rx_st_region / rx_chunk_zero / rx_flag0_of, the saved-slot
   chunk list rx_sv_chunks, the numeral tactics z5 / z5g and the flag-store tactic rx_run_flag, which passes
   aj_flag_store its sixteen journal arguments) and of proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018
   [Apache-2.0] (the shape of a `ret` leaf into a callee post), for reac-pw/fuzz_rate's image A: the walk is
   check_csv's release and epilogue, the side-stack class is 2 instead of 3, and the post is RtPgCSpec.rt_cpost_o,
   whose owned-set conjunct is discharged from the cut's layout, chunk and frame equalities. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCcsvS3.v, with its module names changed; 662 of its 701 lines of code are new or changed and 287 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgEnt0HdB.v at 49b53fe65a85 for reac-pw/fuzz_rate's image A: module paths changed (images.Asan in place of lib/A/Img0, the RtPg files in place of the RPg files); the pcs, the registers (the shadow base s4 = x20, the cursor s9 = x25, what is left after the kind byte s8 = x24, in.n in the register s10 = x26, &ch in s6 = x22, the `v / 10` multiplier in t2 = x7, the token base s2 = x18) and the code of the six blocks are rate's (rate writes no real-frame cell in the head: the real frame is a read-only region holding [R+0x90] and [R+0x98]; the a5 test of the reads is on the register); the AR laws come from the kernel theorem AR_laws_ok in place of a Section hypothesis; kept_run is RtPgW7bBase.w7_kept_run. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgEnt0HdB.v at 21da95a5fcd3 for image B (fuzz_rate.asan-ubsan): image B's pcs and code (seven blocks: the trap tests of the two reads before their checks, the cursor cell R+0x128 the head writes, the ch stores after the reads), registers (the row base s3 = x19, the token base s4 = x20, the kind byte's address s10 = x26, what is left t1 = x6 / s6 = x22, c in a3 = x13, p in s9 = x25, &ch in s2 = x18 from the cell R+0xe0, the digit loop's 4 / 10 / 9 in t0 / t2 / t3), the class-4 frame (1024 bytes, 128 shadow bytes, R+0x220 <= S); the token runs write nothing and the cell's store is in a plain run, whose real-frame region is writable at [R+0x128, R+0x130); RtPgW7bBase is lib/AU/RtPgW7bBaseB.v (w7b_post, w7b_post_of_run, w7b_kept_run, w7b_field, w7b_region_nth), with lib/AU/RtPgStepsB.v's regs_kept_of_st_ok, st_ok_pin_lit, st_ok_pin_sv, rtsb_wx, rtsb_segs_low and same_io_wvb; names hd_ -> hdb_, rt7_ -> rt7b_, rtm_ -> rtmb_. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, same loaded bytes): the block lemmas of the
   head of ent_build's case 0 (pod.h:224-236), from D0 = 0x81460 and D0E = 0x814d0 to the two arms DIG = 0x8152c and
   ODD = 0x81de0 (lib/AU/RtPgEnt0DefB.v). Proves no function (kind: segment lemma).

   THE SPLIT. A run that stores (the scope stores of t and ch, the cursor cell R+0x128) is a plain engine run with
   the frame's shadow row and the cell writable; a run that passes an instrumented check (the two reads of the
   input cursor) is a token run (lib/Reusable/YCbn.v) with no writable region. The UBSan trap test before each read
   (`addi; bltu a6,_,+8; j 0x83098`, a6 = 1) is decided by the engine inside the token run, from the closed numeral
   bounds of the kind byte's address (atom 26). So the head is seven blocks, each from a fixed pc to a fixed pc in
   the shape RtPgW7bBaseB.w7b_post (the journal at the block's start state, the I/O state, the registers outside clob, every
   byte outside the write set, presence kept, and a relation of the result):
     hdb_T1  0x81460 -> 0x81494  plain: the twelve t stores (shadow F + 4 .. 15 := 0), `beqz s6` not taken (s6 >= 1)
     hdb_T0  0x81460 -> 0x8152c  plain, s6 = 0: the t stores, `beqz s6` taken to 0x81d58 (s10 := s2, j 0x81500),
                                 0x81500 t1 := 0, s9 := 0, a3 := 0, the three ch stores (F + 20 .. 22),
                                 R+0x128 := s10, s2 := [R+0xe0], t0 := 4, t2 := 10, t3 := 9, falls into DIG
     hdb_TE  0x814d0 -> 0x8152c  plain: the t stores, then as hdb_T0 from 0x81500
     hdb_K1  0x81494 -> 0x814c0  token, one byte left (t1 = 2): the trap test (0x81498), the check of the cursor
                                 (slow block 0x82270), a3 := c, a0 := s10 + 2, `bne t1, 2` not taken
     hdb_K2  0x81494 -> 0x81db8  token, two bytes or more (t1 >= 3): the same read, `bne` taken to 0x81d90, the
                                 trap test (0x81d94), the check of the second byte (slow block 0x82314), s9 := p,
                                 s10 += 3, t1 -= 3
     hdb_C1  0x814c0 -> DIG / ODD  plain: R+0x128 := a0, t1 := 0, s9 := 0, j 0x81dbc, the three ch stores,
                                 s2 := [R+0xe0], t0 / t2 / t3, `bgeu 199, a3`: c < 200 to DIG, c >= 200 to ODD
     hdb_C2  0x81db8 -> DIG / ODD  plain: R+0x128 := s10, then as hdb_C1 from 0x81dbc
   THE ENGINE STATES. Atom 19 = s3 = shadow_addr F bases the row's two regions, t's twelve bytes [4, 16) and ch's
   three [20, 23), each its own write window; atom 9 = s1 = R bases the real frame's two cells, [R+0xe0, R+0xe8)
   read-only (F + 0xa0, env slot 32) and [R+0x128, R+0x130) writable; atom 26 = s10, the kind byte's address, bases
   the input bytes c (slot 32) and p (slot 33), read-only, and s2 is seated as s10 + 1. The token runs use the
   shadow base s4 itself (RtPgMemB.RTMB_B_Bx = SOff 20 0) and leave one obligation per input read:
   range_addressable of that byte. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05 YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgImgB RtPgMemB RtPgSegB RtPgStepsB RtPgEnt0DefB.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgW7bBaseB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments; an abbreviation, so every statement names the image module's own term *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ======================================== the pcs ======================================== *)
Definition HDB_D : Z := 0x81460.     (* RtPgSegB.RSB_D0 *)
Definition HDB_D0E : Z := 0x814d0.   (* RtPgSegB.RSB_D0E *)
Definition HDB_K : Z := 0x81494.     (* the trap test of the first read of the cursor *)
Definition HDB_C1 : Z := 0x814c0.    (* no byte for p: the cursor cell := s10 + 2 *)
Definition HDB_C2 : Z := 0x81db8.    (* p read: the cursor cell := s10 *)

(* ======================================== the engine states ======================================== *)
Definition hdb_rT : YP09.region := YP09.mkRegion (Some 19%nat) 4 16 4 16 [].
Definition hdb_rCh : YP09.region := YP09.mkRegion (Some 19%nat) 20 23 20 23 [].
Definition hdb_rRe : YP09.region :=
YP09.mkRegion (Some 9%nat) 0xe0 0xe8 0 0 [YP09.mkChunk 0xe0 (CVal 8 (SOff 32 0))].
Definition hdb_rRc : YP09.region := YP09.mkRegion (Some 9%nat) 0x128 0x130 0x128 0x130 [].
Definition hdb_rIn1 : YP09.region := YP09.mkRegion (Some 26%nat) 1 2 0 0 [YP09.mkChunk 1 (CVal 1 (SOff 32 0))].
Definition hdb_rIn2 : YP09.region :=
YP09.mkRegion (Some 26%nat) 1 3 0 0 [YP09.mkChunk 1 (CVal 1 (SOff 32 0)); YP09.mkChunk 2 (CVal 1 (SOff 33 0))].
(* closed numerals only (RtPgStepsB.rtsb_t1_facts): the shadow base, and the kind byte's address below
   2^47 - 3 (one byte read) or 2^47 - 4 (two bytes read) *)
Definition hdb_fK1 : list (nat * afact) :=
[(20%nat, mkAF 2147450880 2147450880 0); (26%nat, mkAF 0 140737488355325 0)].
Definition hdb_fK2 : list (nat * afact) :=
[(6%nat, mkAF 3 140737488355328 0); (20%nat, mkAF 2147450880 2147450880 0); (26%nat, mkAF 0 140737488355324 0)].

Definition ss_T1 : sstate :=
mkSS HDB_D sr_atoms [hdb_rT] None (mkFacts [(22%nat, mkAF 1 9223372036854775808 0)] [] []).
Definition ss_K1 : sstate := mkSS HDB_K sr_atoms [hdb_rIn1] None (mkFacts hdb_fK1 [] []).
Definition ss_K2 : sstate := mkSS HDB_K sr_atoms [hdb_rIn2] None (mkFacts hdb_fK2 [] []).
Definition ss_C (pc : Z) (odd : bool) : sstate :=
mkSS pc sr_atoms [hdb_rCh; hdb_rRe; hdb_rRc] None
  (mkFacts [(13%nat, if odd then mkAF 200 255 0 else mkAF 0 199 0)] [] []).

(* ======================================== the write sets ======================================== *)
Definition hdb_wT (F : Z) : Z -> Prop := fun a => shadow_addr F + 4 <= a < shadow_addr F + 16.
Definition hdb_wCh (F : Z) : Z -> Prop := fun a => shadow_addr F + 20 <= a < shadow_addr F + 23.
Definition hdb_wCell (R : Z) : Z -> Prop := fun a => R + 0x128 <= a < R + 0x130.
Definition hdb_wChC (F R : Z) : Z -> Prop := fun a => hdb_wCh F a \/ hdb_wCell R a.
Definition hdb_wTC (F R : Z) : Z -> Prop := fun a => hdb_wT F a \/ hdb_wCh F a \/ hdb_wCell R a.
(* the token runs write nothing *)
Definition hdb_wNone : Z -> Prop := fun _ => False.

(* the registers the blocks write, and the ones a block pins at its start (s6 = 0 in hdb_T0; s2 = s10 + 1, t1 and
   a6 = 1 in the token runs) *)
Definition hdb_clobT0 : list (bv 5) := [5; 6; 7; 13; 18; 22; 25; 26; 28]%bv.
Definition hdb_clobTE : list (bv 5) := [5; 6; 7; 13; 18; 25; 28]%bv.
Definition hdb_clobK : list (bv 5) := [6; 10; 11; 12; 13; 16; 18; 25; 26]%bv.
Definition hdb_clobC1 : list (bv 5) := [5; 6; 7; 11; 18; 25; 28]%bv.
Definition hdb_clobC2 : list (bv 5) := [5; 7; 11; 18; 28]%bv.

Lemma hdb_sF : forall F, 4096 <= F -> F + 1024 <= 2 ^ 47 ->
0x7fff8000 + 512 <= shadow_addr F /\ shadow_addr F + 128 <= 0x7fff8000 + 2 ^ 44.
Proof.
intros F H0 H1. unfold shadow_addr, SHADOW_OFF.
assert (512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (F / 8 <= 2 ^ 44 - 128) by (apply Z.div_le_upper_bound; lia).
lia.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* the row's bytes j .. j + n - 1 hold 0 *)
Definition hdb_zero (W : world rsegs) (mem : word -> option byte) (F j n : Z) : Prop :=
forall i, j <= i < j + n -> aview rsegs (w_H W) mem (shadow_addr F + i) = Some 0.

(* ======================================== engine helpers ======================================== *)
Lemma hdb_val_at : forall E ss H ms i n lo hi wlo whi cs b off (w : N) e v a (wn : nat),
st_ok rsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
bv_unsigned (ew E n) = b -> In (YP09.mkChunk off (CVal w e)) cs ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 -> a = b + off -> wn = N.to_nat w ->
val_mem rsegs (mrestrict H (ms_mem ms)) a wn v.
Proof.
intros E ss H ms i n lo hi wlo whi cs b off w e v a wn HS Hi Hb Hc He Hv Hw -> ->.
exact (w7b_field E _ n b cs lo hi wlo whi off w e v (w7b_region_nth E ss (restrict H ms) i _ HS Hi) Hb Hc He Hv Hw).
Qed.
Lemma hdb_denot_off : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof. intros E n v c H Hv Hc. rewrite denot_lit_U, (U_atom_off E n v c H Hv Hc). reflexivity. Qed.
Lemma hdb_denot_ext8 : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 256 ->
sv_denot E (SExt false 8 (SOff n 0)) = Z_to_bv 64 v.
Proof.
intros E n v H Hv. rewrite denot_lit_U, U_SExt, (U_atom E n v H ltac:(lia)).
change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia. unfold zcanon, M64. rewrite Z.mod_small by lia.
reflexivity.
Qed.
Lemma hdb_ew_reg : forall regs ex n (r : bv 5) v, Z.of_nat n = bv_unsigned r -> getr regs r = w64 v ->
ew (Ereg regs ex) n = Z_to_bv 64 v.
Proof. intros regs ex n r v Hn H. rewrite (ew_Ereg_nat regs ex n r Hn), H. reflexivity. Qed.
Lemma hdb_unsigned : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E n) = v.
Proof. intros E n v H Hv. rewrite H. apply unsigned_lit_small. exact Hv. Qed.
Lemma hdb_aview0 : forall H mem x, val_mem rsegs (mrestrict H mem) x (N.to_nat 1) 0 -> aview rsegs H mem x = Some 0.
Proof. intros H mem x V. apply (rtmb_val1_aview rsegs H mem x 0); [exact V | lia]. Qed.

(* a register of the final state *)
Ltac hdb_reg HS r :=
lazymatch type of HS with st_ok _ _ ?ssf _ =>
  rewrite (st_ok_restrict_reg rsegs _ _ ssf _ r HS);
  let e := eval vm_compute in (sr_get (ss_regs ssf) r) in change (sr_get (ss_regs ssf) r) with e end.
(* a chunk of region i of the final state at offset off; leaves the base, the value, its range *)
Ltac hdb_chunk HS i off :=
lazymatch type of HS with st_ok _ _ ?ssf _ =>
  let r := eval vm_compute in (nth_error (ss_mem ssf) i) in
  lazymatch r with Some (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi ?cs) =>
    eapply (hdb_val_at _ ssf _ _ i n lo hi wlo whi cs _ off);
    [exact HS | vm_compute; reflexivity | | cbn [In]; repeat (first [left; reflexivity | right]) | | | cbn; lia | | ] end end.
(* every byte j .. j + n - 1 of region i (based at the row, EB : its base) holds the 0 a scope store wrote *)
Ltac hdb_zero_tac HS i EB :=
let k := fresh "k" in let Hk := fresh "Hk" in
intros k Hk; apply hdb_aview0;
lazymatch type of Hk with ?a <= k < ?b =>
  let b' := eval vm_compute in b in
  let Hk0 := fresh "Hk" in assert (Hk0 : a <= k < b') by lia; clear Hk;
  let rec go Hc :=
    first
    [ exfalso; lia
    | lazymatch type of Hc with ?x <= k < ?y =>
        let Hne := fresh "Hne" in
        destruct (Z.eq_dec k x) as [->|Hne];
        [ hdb_chunk HS i x; [exact EB | reflexivity | cbn; lia | reflexivity | reflexivity]
        | let x' := eval vm_compute in (x + 1) in
          let Hc' := fresh "Hk" in assert (Hc' : x' <= k < y) by lia; clear Hc Hne; go Hc' ] end ]
  in go Hk0 end.

Section d.
Variable B : asyms.

(* the context every block runs in: the journal, the real frame R inside its stack window (RtPgImgB hi_rsz = 0x220),
   F = the class-4 side-stack frame (4, pos) the harness holds *)
Definition hdb_ctx (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z)
(lyc : alayout) (Sc : astate) (W : world rsegs) (memc : word -> option byte) (mdc : Model) (R F pos : Z) : Prop :=
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
R mod 16 = 0 /\ R + 0x220 <= sp0 /\ sp0 - STK <= R - T_SEG_STK /\
In (4, pos) own /\ F = frame_addr lyc 4 pos.

Lemma hdb_frame : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos,
hdb_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
F mod 32 = 0 /\ 4096 <= F /\ F + 1024 <= alloc_ceiling /\ alloc_ceiling + T_SEG_STK <= R /\
2 ^ 46 <= R /\ R + 0x220 <= 2 ^ 47 /\ T_SEG_STK = 16384 /\
(forall i, 0 <= i < 128 -> apresent (w_H W) memc (shadow_addr F + i)) /\
(forall a, shadow_addr F <= a < shadow_addr F + 128 ->
 awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) /\
(forall a, R <= a < R + 0x220 ->
 apresent (w_H W) memc a /\ awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos (HJ & HR16 & HRhi & HRlo & Hown & EF).
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (C1 & _).
assert (Has : T_SEG_STK = 16384) by reflexivity.
assert (Hin4 : In (4, pos) (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (HF32 & _ & _ & HFsh).
destruct (frames_bounds rsegs B LAWS lyc Sc W memc mdc 4 pos HAR Hin4) as (HF4096 & HFceil & _).
rewrite <- EF in HF32, HFsh, HF4096, HFceil. change (fs_frame_bytes 4) with 1024 in HFsh, HFceil.
change (1024 / 8) with 128 in HFsh.
split; [exact HF32|]. split; [exact HF4096|]. split; [exact HFceil|].
split; [lia|]. split; [lia|]. split; [lia|]. split; [exact Has|].
split; [intros i Hi; exact (proj1 (HFsh i Hi))|].
split.
- intros a Ha. right. right. right. exists 4, pos. split; [exact Hown|]. right.
  unfold in_zr. cbn [fst snd]. rewrite <- EF. change (fs_frame_bytes 4 / 8) with 128. lia.
- intros a Ha. split; [apply Hpres; lia | left; lia].
Qed.

(* ---- the leaf of a run: the journal, the I/O state and presence from the run ---- *)
Ltac hdb_leaf HS HJ :=
eapply (w7b_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | apply same_io_wvb | | | eassumption | ].
(* the frame condition of a run: in_wrange of its start regions lies in Wr; fin closes one region's case *)
Ltac hdb_kept HFr Wr fin :=
let a := fresh "a" in let Ha := fresh "Ha" in let Hz := fresh "Hz" in
intros a Ha Hz;
refine (w7b_kept_run Wr _ _ _ _ _ _ (fun a _ _ => eq_refl) HFr _ a Ha Hz);
let x := fresh "x" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros x (r & Hin & Hr);
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
repeat (destruct Hin as [<-|Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; fin Hr | ]);
destruct Hin.
Ltac hdb_fr Hctx :=
destruct (hdb_frame _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hctx)
  as (HF32 & HF0 & HFc & HRc & HR0 & HR1 & Has & HFsh & AF & AS).
Ltac hdb_awr :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end.
(* the write rights of the four regions of the plain runs that store the cell: t, ch (the frame's shadow) and
   the cell (the stack window); a read-only region needs none *)
Ltac hdb_awr_tac U19 U9 AF AS :=
hdb_awr;
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn; lia|]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 19%nat); [reflexivity | exact U19 | cbn [YP09.r_wlo YP09.r_whi];
    let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply AF; lia |]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat); [reflexivity | exact U9 | cbn [YP09.r_wlo YP09.r_whi];
    let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; exact (proj2 (AS a ltac:(lia))) |] ].

(* ======================================== hdb_T1: 0x81460 -> 0x81494 ======================================== *)
Definition hdb_T1_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos n : Z),
hdb_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 19 = w64 (shadow_addr F) -> getr regs 22 = w64 n -> 1 <= n < 2 ^ 63 ->
SRr rsegs W (cfg_at rsegs HDB_D regs memc mdc)
(w7b_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k HDB_K regs memc mdc [] (hdb_wT F)
 (fun _ mem2 => hdb_zero W mem2 F 4 12)).

Lemma hdb_T1 : hdb_T1_stmt.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos n Hctx H19 H22 Hn.
pose proof (AR_laws_ok rsegs B) as LAWS.
hdb_fr Hctx.
pose proof Hctx as (HJ & HR16 & HRhi & HRlo & _).
pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsegs.
pose proof asan_consts as (C1 & _).
destruct (hdb_sF F ltac:(lia) ltac:(lia)) as [SF0 SF1].
assert (E19 : bv_unsigned (ew (Ereg regs []) 19) = shadow_addr F).
{ apply hdb_unsigned; [exact (hdb_ew_reg regs [] 19 19%bv _ eq_refl H19) | unfold SHADOW_OFF in *; lia]. }
assert (E22 : bv_unsigned (ew (Ereg regs []) 22) = n).
{ apply hdb_unsigned; [exact (hdb_ew_reg regs [] 22 22%bv _ eq_refl H22) | lia]. }
assert (HS : st_ok rsegs (Ereg regs []) ss_T1 (restrict (w_H W) (mkst regs (Z_to_bv 64 HDB_D) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (rtmb_rw_region rsegs _ _ _ 19%nat (shadow_addr F)); [exact E19 | lia | lia | | constructor].
    intros o Ho. apply HFsh. lia.
  - cbn. tauto.
  - split; [|split; exact I]. cbn [ss_T1 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E22. rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia. }
unfold cfg_at. change (w64 HDB_D) with (Z_to_bv 64 HDB_D).
aj_run_to rt7b_tbl_ok HS HJ HDB_K.
- cbn [ss_mem ss_T1].
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 19%nat (shadow_addr F)); [reflexivity | exact E19 | | apply awr_ok_nil].
  cbn [hdb_rT YP09.r_wlo YP09.r_whi]. intros a Ha. apply AF. lia.
- hdb_leaf HS HJ.
  + eapply (regs_kept_of_st_ok rsegs _ _ ms regs [] (w_H W) _ HS); [apply env_agree_refl | vm_compute; reflexivity].
  + intros a Ha Hz.
    refine (w7b_kept_run (hdb_wT F) _ _ (w_H W) memc memc (ms_mem ms) (fun a _ _ => eq_refl) HFr _ a Ha Hz).
    intros x (r & Hin & Hr). cbn [ss_mem ss_T1 In] in Hin. destruct Hin as [<-|[]].
    cbn [hdb_rT YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite E19 in Hr. unfold hdb_wT. lia.
  + hdb_zero_tac HS 0%nat E19.
Qed.

(* ================================ hdb_T0 / hdb_TE: to DIG with nothing read ================================ *)
(* the registers DIG asks besides the cut's (rt7b_cut_DIG), with c = p = 0 and nothing left *)
Definition hdb_Z_R (F : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 5 = w64 4 /\ getr regs2 7 = w64 10 /\ getr regs2 28 = w64 9 /\ getr regs2 6 = w64 0 /\
getr regs2 25 = w64 0 /\ getr regs2 13 = w64 0 /\ getr regs2 18 = w64 (F + 0xa0).
(* t and ch in scope, and the cursor cell *)
Definition hdb_Z_mem (W : world rsegs) (mem2 : word -> option byte) (F R cur : Z) : Prop :=
hdb_zero W mem2 F 4 12 /\ hdb_zero W mem2 F 20 3 /\
val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x128) 8 cur.

Definition hdb_T0_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos cur : Z),
hdb_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 9 = w64 R -> getr regs 19 = w64 (shadow_addr F) -> getr regs 22 = w64 0 -> getr regs 18 = w64 cur ->
0 <= cur < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe0) 8 (F + 0xa0) ->
SRr rsegs W (cfg_at rsegs HDB_D regs memc mdc)
(w7b_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k RT7B_DIG regs memc mdc hdb_clobT0 (hdb_wTC F R)
 (fun regs2 mem2 => hdb_Z_R F regs2 /\ getr regs2 26 = w64 cur /\ hdb_Z_mem W mem2 F R cur)).
Definition hdb_TE_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos cur : Z),
hdb_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 9 = w64 R -> getr regs 19 = w64 (shadow_addr F) -> getr regs 26 = w64 cur -> 0 <= cur < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe0) 8 (F + 0xa0) ->
SRr rsegs W (cfg_at rsegs HDB_D0E regs memc mdc)
(w7b_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k RT7B_DIG regs memc mdc hdb_clobTE (hdb_wTC F R)
 (fun regs2 mem2 => hdb_Z_R F regs2 /\ hdb_Z_mem W mem2 F R cur)).

(* the real frame's cell the head reads, read-only, F + 0xa0 in slot 32 *)
Lemma hdb_rRe_ok : forall E (W : world rsegs) memc R F,
bv_unsigned (ew E 9) = R -> ew E 32 = Z_to_bv 64 (F + 0xa0) -> 2 ^ 46 <= R -> R + 0x220 <= 2 ^ 47 ->
0 <= F + 0xa0 < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe0) 8 (F + 0xa0) ->
region_ok rsegs E (mrestrict (w_H W) memc) hdb_rRe.
Proof.
intros E W memc R F U9 X32 HR0 HR1 HFr He0.
apply (rtmb_ro_region rsegs _ _ _ 9%nat R); [exact U9 | lia | lia |].
constructor; [|constructor].
apply (chunk_ok_val rsegs _ _ R 0xe0 8 (SOff 32 0) (F + 0xa0));
  [apply rtsb_den_atom; [exact X32 | lia] | change (8 * Z.of_N 8) with 64; lia | cbn; lia | exact He0].
Qed.
(* the cursor cell, writable and present *)
Lemma hdb_rRc_ok : forall E (W : world rsegs) memc R,
bv_unsigned (ew E 9) = R -> 2 ^ 46 <= R -> R + 0x220 <= 2 ^ 47 ->
(forall a, R <= a < R + 0x220 -> apresent (w_H W) memc a) ->
region_ok rsegs E (mrestrict (w_H W) memc) hdb_rRc.
Proof.
intros E W memc R U9 HR0 HR1 HP.
apply (rtmb_rw_region rsegs _ _ _ 9%nat R); [exact U9 | lia | lia | | constructor].
intros o Ho. apply HP. lia.
Qed.

(* the entry state of both: the row's two regions and the real frame's cells, F + 0xa0 in slot 32 *)
Lemma hdb_entry_Z : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) R F pos pc,
hdb_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 9 = w64 R -> getr regs 19 = w64 (shadow_addr F) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe0) 8 (F + 0xa0) ->
st_ok rsegs (Ereg regs [Z_to_bv 64 (F + 0xa0)])
  (mkSS pc sr_atoms [hdb_rT; hdb_rCh; hdb_rRe; hdb_rRc] None (mkFacts [] [] []))
(restrict (w_H W) (mkst regs (Z_to_bv 64 pc) memc (seg_rom rsegs))).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos pc Hctx H9 H19 He0.
hdb_fr Hctx. pose proof Hctx as (HJ & HR16 & HRhi & HRlo & _).
pose proof asan_consts as (C1 & _).
destruct (hdb_sF F ltac:(lia) ltac:(lia)) as [SF0 SF1].
set (ex := [Z_to_bv 64 (F + 0xa0)]).
assert (U19 : bv_unsigned (ew (Ereg regs ex) 19) = shadow_addr F).
{ apply hdb_unsigned; [exact (hdb_ew_reg regs ex 19 19%bv _ eq_refl H19) | unfold SHADOW_OFF in *; lia]. }
assert (U9 : bv_unsigned (ew (Ereg regs ex) 9) = R).
{ apply hdb_unsigned; [exact (hdb_ew_reg regs ex 9 9%bv _ eq_refl H9) | lia]. }
assert (X32 : ew (Ereg regs ex) 32 = Z_to_bv 64 (F + 0xa0)) by exact (ew_Ereg_extra regs ex 0).
rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
  + apply (rtmb_rw_region rsegs _ _ _ 19%nat (shadow_addr F)); [exact U19 | lia | lia | | constructor].
    intros o Ho. apply HFsh. lia.
  + apply (rtmb_rw_region rsegs _ _ _ 19%nat (shadow_addr F)); [exact U19 | lia | lia | | constructor].
    intros o Ho. apply HFsh. lia.
  + exact (hdb_rRe_ok _ W memc R F U9 X32 HR0 HR1 ltac:(lia) He0).
  + exact (hdb_rRc_ok _ W memc R U9 HR0 HR1 (fun a Ha => proj1 (AS a Ha))).
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
  cbn [hdb_rT hdb_rCh hdb_rRe hdb_rRc YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U19, U9.
  repeat split; first [left; lia | right; lia | exact I].
- split; [exact I | split; exact I].
Qed.

Lemma hdb_T0 : hdb_T0_stmt.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur Hctx H9 H19 H22 H18 Hcur He0.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (hdb_entry_Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HDB_D Hctx H9 H19 He0) as HS0.
hdb_fr Hctx. pose proof Hctx as (HJ & HR16 & HRhi & HRlo & _).
pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsegs.
pose proof asan_consts as (C1 & _).
destruct (hdb_sF F ltac:(lia) ltac:(lia)) as [SF0 SF1].
set (ex := [Z_to_bv 64 (F + 0xa0)]) in HS0.
assert (U19 : bv_unsigned (ew (Ereg regs ex) 19) = shadow_addr F).
{ apply hdb_unsigned; [exact (hdb_ew_reg regs ex 19 19%bv _ eq_refl H19) | unfold SHADOW_OFF in *; lia]. }
assert (U9 : bv_unsigned (ew (Ereg regs ex) 9) = R).
{ apply hdb_unsigned; [exact (hdb_ew_reg regs ex 9 9%bv _ eq_refl H9) | lia]. }
assert (X32 : ew (Ereg regs ex) 32 = Z_to_bv 64 (F + 0xa0)) by exact (ew_Ereg_extra regs ex 0).
assert (X18 : ew (Ereg regs ex) 18 = Z_to_bv 64 cur) by exact (hdb_ew_reg regs ex 18 18%bv _ eq_refl H18).
pose proof (st_ok_pin_lit rsegs _ _ _ (22%bv : bv 5) 0 HS0 eq_refl H22) as HS. clear HS0.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
unfold cfg_at. change (w64 HDB_D) with (Z_to_bv 64 HDB_D).
aj_run_to rt7b_tbl_ok HS HJ RT7B_DIG.
- hdb_awr_tac U19 U9 AF AS.
- hdb_leaf HS HJ.
  + eapply (regs_kept_of_st_ok rsegs _ _ ms regs ex (w_H W) _ HS); [apply env_agree_refl | vm_compute; reflexivity].
  + hdb_kept HFr (hdb_wTC F R) ltac:(fun H => rewrite ?U19, ?U9 in H; cbv [hdb_wTC hdb_wT hdb_wCh hdb_wCell]; lia).
  + cbv beta. split; [|split].
    * unfold hdb_Z_R. split; [|split; [|split; [|split; [|split; [|split]]]]].
      -- hdb_reg HS (5%bv : bv 5). reflexivity.
      -- hdb_reg HS (7%bv : bv 5). reflexivity.
      -- hdb_reg HS (28%bv : bv 5). reflexivity.
      -- hdb_reg HS (6%bv : bv 5). reflexivity.
      -- hdb_reg HS (25%bv : bv 5). reflexivity.
      -- hdb_reg HS (13%bv : bv 5). reflexivity.
      -- hdb_reg HS (18%bv : bv 5). apply rtsb_den_atom; [exact X32 | lia].
    * hdb_reg HS (26%bv : bv 5). apply rtsb_den_atom; [exact X18 | lia].
    * split; [|split].
      -- hdb_zero_tac HS 0%nat U19.
      -- hdb_zero_tac HS 1%nat U19.
      -- hdb_chunk HS 3%nat 0x128; [exact U9 | apply rtsb_den_atom; [exact X18 | lia] | cbn; lia | reflexivity | reflexivity].
Qed.

Lemma hdb_TE : hdb_TE_stmt.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur Hctx H9 H19 H26 Hcur He0.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (hdb_entry_Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HDB_D0E Hctx H9 H19 He0) as HS.
hdb_fr Hctx. pose proof Hctx as (HJ & HR16 & HRhi & HRlo & _).
pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsegs.
pose proof asan_consts as (C1 & _).
destruct (hdb_sF F ltac:(lia) ltac:(lia)) as [SF0 SF1].
set (ex := [Z_to_bv 64 (F + 0xa0)]) in HS.
assert (U19 : bv_unsigned (ew (Ereg regs ex) 19) = shadow_addr F).
{ apply hdb_unsigned; [exact (hdb_ew_reg regs ex 19 19%bv _ eq_refl H19) | unfold SHADOW_OFF in *; lia]. }
assert (U9 : bv_unsigned (ew (Ereg regs ex) 9) = R).
{ apply hdb_unsigned; [exact (hdb_ew_reg regs ex 9 9%bv _ eq_refl H9) | lia]. }
assert (X32 : ew (Ereg regs ex) 32 = Z_to_bv 64 (F + 0xa0)) by exact (ew_Ereg_extra regs ex 0).
assert (X26 : ew (Ereg regs ex) 26 = Z_to_bv 64 cur) by exact (hdb_ew_reg regs ex 26 26%bv _ eq_refl H26).
unfold cfg_at. change (w64 HDB_D0E) with (Z_to_bv 64 HDB_D0E).
aj_run_to rt7b_tbl_ok HS HJ RT7B_DIG.
- hdb_awr_tac U19 U9 AF AS.
- hdb_leaf HS HJ.
  + eapply (regs_kept_of_st_ok rsegs _ _ ms regs ex (w_H W) _ HS); [apply env_agree_refl | vm_compute; reflexivity].
  + hdb_kept HFr (hdb_wTC F R) ltac:(fun H => rewrite ?U19, ?U9 in H; cbv [hdb_wTC hdb_wT hdb_wCh hdb_wCell]; lia).
  + cbv beta. split.
    * unfold hdb_Z_R. split; [|split; [|split; [|split; [|split; [|split]]]]].
      -- hdb_reg HS (5%bv : bv 5). reflexivity.
      -- hdb_reg HS (7%bv : bv 5). reflexivity.
      -- hdb_reg HS (28%bv : bv 5). reflexivity.
      -- hdb_reg HS (6%bv : bv 5). reflexivity.
      -- hdb_reg HS (25%bv : bv 5). reflexivity.
      -- hdb_reg HS (13%bv : bv 5). reflexivity.
      -- hdb_reg HS (18%bv : bv 5). apply rtsb_den_atom; [exact X32 | lia].
    * split; [|split].
      -- hdb_zero_tac HS 0%nat U19.
      -- hdb_zero_tac HS 1%nat U19.
      -- hdb_chunk HS 3%nat 0x128; [exact U9 | apply rtsb_den_atom; [exact X26 | lia] | cbn; lia | reflexivity | reflexivity].
Qed.

(* ================================ hdb_C1 / hdb_C2: the cell, the ch stores and the arm test ================================ *)
Definition hdb_C_R (F : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 18 = w64 (F + 0xa0) /\ getr regs2 5 = w64 4 /\ getr regs2 7 = w64 10 /\ getr regs2 28 = w64 9.
Definition hdb_C1_stmt : Prop :=
forall (odd : bool) STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos c v : Z),
hdb_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 9 = w64 R -> getr regs 19 = w64 (shadow_addr F) -> getr regs 10 = w64 v -> getr regs 13 = w64 c ->
(if odd then 200 <= c < 256 else 0 <= c < 200) -> 0 <= v < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe0) 8 (F + 0xa0) ->
SRr rsegs W (cfg_at rsegs HDB_C1 regs memc mdc)
(w7b_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k (if odd then RT7B_ODD else RT7B_DIG) regs memc mdc hdb_clobC1
 (hdb_wChC F R)
 (fun regs2 mem2 => hdb_C_R F regs2 /\ getr regs2 6 = w64 0 /\ getr regs2 25 = w64 0 /\
    hdb_zero W mem2 F 20 3 /\ val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x128) 8 v)).
Definition hdb_C2_stmt : Prop :=
forall (odd : bool) STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos c v : Z),
hdb_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 9 = w64 R -> getr regs 19 = w64 (shadow_addr F) -> getr regs 26 = w64 v -> getr regs 13 = w64 c ->
(if odd then 200 <= c < 256 else 0 <= c < 200) -> 0 <= v < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe0) 8 (F + 0xa0) ->
SRr rsegs W (cfg_at rsegs HDB_C2 regs memc mdc)
(w7b_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k (if odd then RT7B_ODD else RT7B_DIG) regs memc mdc hdb_clobC2
 (hdb_wChC F R)
 (fun regs2 mem2 => hdb_C_R F regs2 /\
    hdb_zero W mem2 F 20 3 /\ val_mem rsegs (mrestrict (w_H W) mem2) (R + 0x128) 8 v)).

(* the entry state of both: ch's region and the real frame's cells, F + 0xa0 in slot 32, the fact on c *)
Lemma hdb_entry_C : forall (odd : bool) STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word)
  R F pos c pc,
hdb_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 9 = w64 R -> getr regs 19 = w64 (shadow_addr F) -> getr regs 13 = w64 c ->
(if odd then 200 <= c < 256 else 0 <= c < 200) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xe0) 8 (F + 0xa0) ->
st_ok rsegs (Ereg regs [Z_to_bv 64 (F + 0xa0)]) (ss_C pc odd)
(restrict (w_H W) (mkst regs (Z_to_bv 64 pc) memc (seg_rom rsegs))).
Proof.
intros odd STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c pc Hctx H9 H19 H13 Hc He0.
hdb_fr Hctx. pose proof Hctx as (HJ & HR16 & HRhi & HRlo & _).
pose proof asan_consts as (C1 & _).
assert (Hc8 : 0 <= c < 256) by (destruct odd; cbv iota in Hc; lia).
destruct (hdb_sF F ltac:(lia) ltac:(lia)) as [SF0 SF1].
set (ex := [Z_to_bv 64 (F + 0xa0)]).
assert (U19 : bv_unsigned (ew (Ereg regs ex) 19) = shadow_addr F).
{ apply hdb_unsigned; [exact (hdb_ew_reg regs ex 19 19%bv _ eq_refl H19) | unfold SHADOW_OFF in *; lia]. }
assert (U9 : bv_unsigned (ew (Ereg regs ex) 9) = R).
{ apply hdb_unsigned; [exact (hdb_ew_reg regs ex 9 9%bv _ eq_refl H9) | lia]. }
assert (U13 : bv_unsigned (ew (Ereg regs ex) 13) = c).
{ apply hdb_unsigned; [exact (hdb_ew_reg regs ex 13 13%bv _ eq_refl H13) | lia]. }
assert (X32 : ew (Ereg regs ex) 32 = Z_to_bv 64 (F + 0xa0)) by exact (ew_Ereg_extra regs ex 0).
rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
  + apply (rtmb_rw_region rsegs _ _ _ 19%nat (shadow_addr F)); [exact U19 | lia | lia | | constructor].
    intros o Ho. apply HFsh. lia.
  + exact (hdb_rRe_ok _ W memc R F U9 X32 HR0 HR1 ltac:(lia) He0).
  + exact (hdb_rRc_ok _ W memc R U9 HR0 HR1 (fun a Ha => proj1 (AS a Ha))).
- cbn [pairwise_disjoint all_disjoint ss_C ss_mem]. unfold extent_disjoint.
  cbn [hdb_rCh hdb_rRe hdb_rRc YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U19, U9.
  repeat split; first [left; lia | right; lia | exact I].
- split; [|split; exact I]. cbn [ss_C ss_facts f_atoms atoms_ok]. split; [|exact I].
  unfold afact_ok. rewrite U13. destruct odd; cbn [af_lo af_hi af_al2]; cbv iota in Hc; rewrite Z.pow_0_r, Z.mod_1_r;
  repeat split; lia.
Qed.

Lemma hdb_C1 : hdb_C1_stmt.
Proof.
intros odd STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c v Hctx H9 H19 H10 H13 Hc Hv He0.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (hdb_entry_C odd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HDB_C1 Hctx H9 H19 H13 Hc He0) as HS.
hdb_fr Hctx. pose proof Hctx as (HJ & HR16 & HRhi & HRlo & _).
pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsegs.
pose proof asan_consts as (C1 & _).
destruct (hdb_sF F ltac:(lia) ltac:(lia)) as [SF0 SF1].
set (ex := [Z_to_bv 64 (F + 0xa0)]) in HS.
assert (U19 : bv_unsigned (ew (Ereg regs ex) 19) = shadow_addr F).
{ apply hdb_unsigned; [exact (hdb_ew_reg regs ex 19 19%bv _ eq_refl H19) | unfold SHADOW_OFF in *; lia]. }
assert (U9 : bv_unsigned (ew (Ereg regs ex) 9) = R).
{ apply hdb_unsigned; [exact (hdb_ew_reg regs ex 9 9%bv _ eq_refl H9) | lia]. }
assert (X32 : ew (Ereg regs ex) 32 = Z_to_bv 64 (F + 0xa0)) by exact (ew_Ereg_extra regs ex 0).
assert (X10 : ew (Ereg regs ex) 10 = Z_to_bv 64 v) by exact (hdb_ew_reg regs ex 10 10%bv _ eq_refl H10).
unfold cfg_at. change (w64 HDB_C1) with (Z_to_bv 64 HDB_C1).
destruct odd; cbv iota.
- aj_run_to rt7b_tbl_ok HS HJ RT7B_ODD.
  + hdb_awr_tac U19 U9 AF AS.
  + hdb_leaf HS HJ.
    * eapply (regs_kept_of_st_ok rsegs _ _ ms regs ex (w_H W) _ HS); [apply env_agree_refl | vm_compute; reflexivity].
    * hdb_kept HFr (hdb_wChC F R) ltac:(fun H => rewrite ?U19, ?U9 in H; cbv [hdb_wChC hdb_wCh hdb_wCell]; lia).
    * cbv beta. split; [|split; [|split; [|split]]].
      -- unfold hdb_C_R. split; [|split; [|split]].
         ++ hdb_reg HS (18%bv : bv 5). apply rtsb_den_atom; [exact X32 | lia].
         ++ hdb_reg HS (5%bv : bv 5). reflexivity.
         ++ hdb_reg HS (7%bv : bv 5). reflexivity.
         ++ hdb_reg HS (28%bv : bv 5). reflexivity.
      -- hdb_reg HS (6%bv : bv 5). reflexivity.
      -- hdb_reg HS (25%bv : bv 5). reflexivity.
      -- hdb_zero_tac HS 0%nat U19.
      -- hdb_chunk HS 2%nat 0x128; [exact U9 | apply rtsb_den_atom; [exact X10 | lia] | cbn; lia | reflexivity | reflexivity].
- aj_run_to rt7b_tbl_ok HS HJ RT7B_DIG.
  + hdb_awr_tac U19 U9 AF AS.
  + hdb_leaf HS HJ.
    * eapply (regs_kept_of_st_ok rsegs _ _ ms regs ex (w_H W) _ HS); [apply env_agree_refl | vm_compute; reflexivity].
    * hdb_kept HFr (hdb_wChC F R) ltac:(fun H => rewrite ?U19, ?U9 in H; cbv [hdb_wChC hdb_wCh hdb_wCell]; lia).
    * cbv beta. split; [|split; [|split; [|split]]].
      -- unfold hdb_C_R. split; [|split; [|split]].
         ++ hdb_reg HS (18%bv : bv 5). apply rtsb_den_atom; [exact X32 | lia].
         ++ hdb_reg HS (5%bv : bv 5). reflexivity.
         ++ hdb_reg HS (7%bv : bv 5). reflexivity.
         ++ hdb_reg HS (28%bv : bv 5). reflexivity.
      -- hdb_reg HS (6%bv : bv 5). reflexivity.
      -- hdb_reg HS (25%bv : bv 5). reflexivity.
      -- hdb_zero_tac HS 0%nat U19.
      -- hdb_chunk HS 2%nat 0x128; [exact U9 | apply rtsb_den_atom; [exact X10 | lia] | cbn; lia | reflexivity | reflexivity].
Qed.

Lemma hdb_C2 : hdb_C2_stmt.
Proof.
intros odd STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c v Hctx H9 H19 H26 H13 Hc Hv He0.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (hdb_entry_C odd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HDB_C2 Hctx H9 H19 H13 Hc He0) as HS.
hdb_fr Hctx. pose proof Hctx as (HJ & HR16 & HRhi & HRlo & _).
pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsegs.
pose proof asan_consts as (C1 & _).
destruct (hdb_sF F ltac:(lia) ltac:(lia)) as [SF0 SF1].
set (ex := [Z_to_bv 64 (F + 0xa0)]) in HS.
assert (U19 : bv_unsigned (ew (Ereg regs ex) 19) = shadow_addr F).
{ apply hdb_unsigned; [exact (hdb_ew_reg regs ex 19 19%bv _ eq_refl H19) | unfold SHADOW_OFF in *; lia]. }
assert (U9 : bv_unsigned (ew (Ereg regs ex) 9) = R).
{ apply hdb_unsigned; [exact (hdb_ew_reg regs ex 9 9%bv _ eq_refl H9) | lia]. }
assert (X32 : ew (Ereg regs ex) 32 = Z_to_bv 64 (F + 0xa0)) by exact (ew_Ereg_extra regs ex 0).
assert (X26 : ew (Ereg regs ex) 26 = Z_to_bv 64 v) by exact (hdb_ew_reg regs ex 26 26%bv _ eq_refl H26).
unfold cfg_at. change (w64 HDB_C2) with (Z_to_bv 64 HDB_C2).
destruct odd; cbv iota.
- aj_run_to rt7b_tbl_ok HS HJ RT7B_ODD.
  + hdb_awr_tac U19 U9 AF AS.
  + hdb_leaf HS HJ.
    * eapply (regs_kept_of_st_ok rsegs _ _ ms regs ex (w_H W) _ HS); [apply env_agree_refl | vm_compute; reflexivity].
    * hdb_kept HFr (hdb_wChC F R) ltac:(fun H => rewrite ?U19, ?U9 in H; cbv [hdb_wChC hdb_wCh hdb_wCell]; lia).
    * cbv beta. split; [|split].
      -- unfold hdb_C_R. split; [|split; [|split]].
         ++ hdb_reg HS (18%bv : bv 5). apply rtsb_den_atom; [exact X32 | lia].
         ++ hdb_reg HS (5%bv : bv 5). reflexivity.
         ++ hdb_reg HS (7%bv : bv 5). reflexivity.
         ++ hdb_reg HS (28%bv : bv 5). reflexivity.
      -- hdb_zero_tac HS 0%nat U19.
      -- hdb_chunk HS 2%nat 0x128; [exact U9 | apply rtsb_den_atom; [exact X26 | lia] | cbn; lia | reflexivity | reflexivity].
- aj_run_to rt7b_tbl_ok HS HJ RT7B_DIG.
  + hdb_awr_tac U19 U9 AF AS.
  + hdb_leaf HS HJ.
    * eapply (regs_kept_of_st_ok rsegs _ _ ms regs ex (w_H W) _ HS); [apply env_agree_refl | vm_compute; reflexivity].
    * hdb_kept HFr (hdb_wChC F R) ltac:(fun H => rewrite ?U19, ?U9 in H; cbv [hdb_wChC hdb_wCh hdb_wCell]; lia).
    * cbv beta. split; [|split].
      -- unfold hdb_C_R. split; [|split; [|split]].
         ++ hdb_reg HS (18%bv : bv 5). apply rtsb_den_atom; [exact X32 | lia].
         ++ hdb_reg HS (5%bv : bv 5). reflexivity.
         ++ hdb_reg HS (7%bv : bv 5). reflexivity.
         ++ hdb_reg HS (28%bv : bv 5). reflexivity.
      -- hdb_zero_tac HS 0%nat U19.
      -- hdb_chunk HS 2%nat 0x128; [exact U9 | apply rtsb_den_atom; [exact X26 | lia] | cbn; lia | reflexivity | reflexivity].
Qed.

(* ================================ hdb_K1 / hdb_K2: the reads of c and p ================================ *)
Definition hdb_K1_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos cur c : Z),
hdb_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 20 = w64 SHADOW_OFF -> getr regs 26 = w64 (cur - 1) -> getr regs 18 = w64 cur ->
getr regs 6 = w64 2 -> getr regs 16 = w64 1 ->
1 <= cur -> cur + 1 <= 2 ^ 47 - 1 ->
val_mem rsegs (mrestrict (w_H W) memc) cur 1 c -> 0 <= c < 256 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF cur 1 ->
SRr rsegs W (cfg_at rsegs HDB_K regs memc mdc)
(w7b_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k HDB_C1 regs memc mdc hdb_clobK hdb_wNone
 (fun regs2 _ => getr regs2 13 = w64 c /\ getr regs2 10 = w64 (cur + 1))).
Definition hdb_K2_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos cur n c p : Z),
hdb_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 20 = w64 SHADOW_OFF -> getr regs 26 = w64 (cur - 1) -> getr regs 18 = w64 cur ->
getr regs 6 = w64 (n + 1) -> getr regs 16 = w64 1 -> 2 <= n -> n + 1 <= 2 ^ 47 ->
1 <= cur -> cur + 2 <= 2 ^ 47 - 1 ->
val_mem rsegs (mrestrict (w_H W) memc) cur 1 c -> 0 <= c < 256 ->
val_mem rsegs (mrestrict (w_H W) memc) (cur + 1) 1 p -> 0 <= p < 256 ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF cur 2 ->
SRr rsegs W (cfg_at rsegs HDB_K regs memc mdc)
(w7b_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k HDB_C2 regs memc mdc hdb_clobK hdb_wNone
 (fun regs2 _ => getr regs2 13 = w64 c /\ getr regs2 25 = w64 p /\ getr regs2 26 = w64 (cur + 2) /\
    getr regs2 6 = w64 (n - 2))).

Lemma hdb_K1 : hdb_K1_stmt.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur c Hctx H20 H26 H18 H6 H16 Hc0 Hc1
  Hcv Hc HRA.
pose proof (AR_laws_ok rsegs B) as LAWS.
hdb_fr Hctx. pose proof Hctx as (HJ & HR16 & HRhi & HRlo & _).
pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsegs.
pose proof asan_consts as (C1 & _).
set (ex := [Z_to_bv 64 c]).
assert (X26 : ew (Ereg regs ex) 26 = Z_to_bv 64 (cur - 1)) by exact (hdb_ew_reg regs ex 26 26%bv _ eq_refl H26).
assert (X20 : ew (Ereg regs ex) 20 = Z_to_bv 64 SHADOW_OFF) by exact (hdb_ew_reg regs ex 20 20%bv _ eq_refl H20).
assert (X32 : ew (Ereg regs ex) 32 = Z_to_bv 64 c) by exact (ew_Ereg_extra regs ex 0).
assert (U26 : bv_unsigned (ew (Ereg regs ex) 26) = cur - 1) by (apply hdb_unsigned; [exact X26 | lia]).
assert (U20 : bv_unsigned (ew (Ereg regs ex) 20) = SHADOW_OFF)
  by (apply hdb_unsigned; [exact X20 | unfold SHADOW_OFF; lia]).
assert (HS0 : st_ok rsegs (Ereg regs ex) ss_K1
  (restrict (w_H W) (mkst regs (Z_to_bv 64 HDB_K) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (rtmb_ro_region rsegs _ _ _ 26%nat (cur - 1)); [exact U26 | lia | lia |].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs _ _ (cur - 1) 1 1 (SOff 32 0) c);
      [apply rtsb_den_atom; [exact X32 | lia] | cbn; lia | cbn; lia |].
    replace (cur - 1 + 1) with cur by lia. exact Hcv.
  - cbn. tauto.
  - split; [|split; exact I]. cbn [ss_K1 hdb_fK1 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U20, U26. unfold SHADOW_OFF. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat split; lia. }
pose proof (st_ok_pin_sv rsegs _ _ _ (18%bv : bv 5) (SOff 26 1) HS0 eq_refl
  ltac:(rewrite (hdb_denot_off _ 26 (cur - 1) 1 X26 ltac:(lia) ltac:(lia)); replace (cur - 1 + 1) with cur by lia;
        symmetry; exact H18)) as HS1.
clear HS0. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_K1] in HS1.
pose proof (st_ok_pin_lit rsegs _ _ _ (6%bv : bv 5) 2 HS1 eq_refl H6) as HS2.
clear HS1. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2.
pose proof (st_ok_pin_lit rsegs _ _ _ (16%bv : bv 5) 1 HS2 eq_refl H16) as HS.
clear HS2. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
assert (SHOK : sh_ok rsegs RTMB_B_Bx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs ex) (Ereg regs ex)) by apply env_agree_refl.
assert (HA33 : env_agree 33 (Ereg regs ex) (Ereg regs ex)) by apply env_agree_refl.
unfold cfg_at. change (w64 HDB_K) with (Z_to_bv 64 HDB_K).
aj_run_to_tok rt7b_tbl_ok HS HJ SHOK RTMB_B_span HDB_C1.
- (* the shadow check of c's byte *)
  cbn [ms_mem mkst]. unfold RTMB_B_Bx.
  rewrite (U_atom _ 20 SHADOW_OFF X20 ltac:(unfold SHADOW_OFF; lia)), (U_atom_off _ 26 (cur - 1) 1 X26 ltac:(lia) ltac:(lia)).
  replace (cur - 1 + 1) with cur by lia. exact HRA.
- hdb_awr.
  apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil].
- lazymatch type of HS with st_ok _ ?E' _ _ =>
    assert (HA : env_agree 33 (Ereg regs ex) E') by env_agree_chain HA33 end.
  destruct HA as [HA _].
  hdb_leaf HS HJ.
  + eapply (regs_kept_of_st_ok rsegs _ _ ms regs ex (w_H W) _ HS); [env_agree_chain HAE | vm_compute; reflexivity].
  + hdb_kept HFr hdb_wNone ltac:(fun H => exfalso; lia).
  + cbv beta. split.
    * hdb_reg HS (13%bv : bv 5). apply hdb_denot_ext8; [rewrite HA by lia; exact X32 | lia].
    * hdb_reg HS (10%bv : bv 5).
      rewrite (hdb_denot_off _ 26 (cur - 1) 2 ltac:(rewrite HA by lia; exact X26) ltac:(lia) ltac:(lia)).
      unfold w64. f_equal. lia.
Qed.

Lemma hdb_K2 : hdb_K2_stmt.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur n c p Hctx H20 H26 H18 H6 H16 Hn0 Hn1
  Hc0 Hc1 Hcv Hc Hpv Hp HRA.
pose proof (AR_laws_ok rsegs B) as LAWS.
hdb_fr Hctx. pose proof Hctx as (HJ & HR16 & HRhi & HRlo & _).
pose proof rtsb_wx as Hwx. pose proof rtsb_segs_low as Hsegs.
pose proof asan_consts as (C1 & _).
set (ex := [Z_to_bv 64 c; Z_to_bv 64 p]).
assert (X26 : ew (Ereg regs ex) 26 = Z_to_bv 64 (cur - 1)) by exact (hdb_ew_reg regs ex 26 26%bv _ eq_refl H26).
assert (X20 : ew (Ereg regs ex) 20 = Z_to_bv 64 SHADOW_OFF) by exact (hdb_ew_reg regs ex 20 20%bv _ eq_refl H20).
assert (X6 : ew (Ereg regs ex) 6 = Z_to_bv 64 (n + 1)) by exact (hdb_ew_reg regs ex 6 6%bv _ eq_refl H6).
assert (X32 : ew (Ereg regs ex) 32 = Z_to_bv 64 c) by exact (ew_Ereg_extra regs ex 0).
assert (X33 : ew (Ereg regs ex) 33 = Z_to_bv 64 p) by exact (ew_Ereg_extra regs ex 1).
assert (U26 : bv_unsigned (ew (Ereg regs ex) 26) = cur - 1) by (apply hdb_unsigned; [exact X26 | lia]).
assert (U6 : bv_unsigned (ew (Ereg regs ex) 6) = n + 1) by (apply hdb_unsigned; [exact X6 | lia]).
assert (U20 : bv_unsigned (ew (Ereg regs ex) 20) = SHADOW_OFF)
  by (apply hdb_unsigned; [exact X20 | unfold SHADOW_OFF; lia]).
assert (HS0 : st_ok rsegs (Ereg regs ex) ss_K2
  (restrict (w_H W) (mkst regs (Z_to_bv 64 HDB_K) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (rtmb_ro_region rsegs _ _ _ 26%nat (cur - 1)); [exact U26 | lia | lia |].
    constructor; [|constructor; [|constructor]].
    + apply (chunk_ok_val rsegs _ _ (cur - 1) 1 1 (SOff 32 0) c);
        [apply rtsb_den_atom; [exact X32 | lia] | cbn; lia | cbn; lia |].
      replace (cur - 1 + 1) with cur by lia. exact Hcv.
    + apply (chunk_ok_val rsegs _ _ (cur - 1) 2 1 (SOff 33 0) p);
        [apply rtsb_den_atom; [exact X33 | lia] | cbn; lia | cbn; lia |].
      replace (cur - 1 + 2) with (cur + 1) by lia. exact Hpv.
  - cbn. tauto.
  - split; [|split; exact I]. cbn [ss_K2 hdb_fK2 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U6, U20, U26. unfold SHADOW_OFF. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat split; lia. }
pose proof (st_ok_pin_sv rsegs _ _ _ (18%bv : bv 5) (SOff 26 1) HS0 eq_refl
  ltac:(rewrite (hdb_denot_off _ 26 (cur - 1) 1 X26 ltac:(lia) ltac:(lia)); replace (cur - 1 + 1) with cur by lia;
        symmetry; exact H18)) as HS1.
clear HS0. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts ss_K2] in HS1.
pose proof (st_ok_pin_lit rsegs _ _ _ (16%bv : bv 5) 1 HS1 eq_refl H16) as HS.
clear HS1. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS.
assert (SHOK : sh_ok rsegs RTMB_B_Bx [] (Ereg regs ex) (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 (Ereg regs ex) (Ereg regs ex)) by apply env_agree_refl.
assert (HA34 : env_agree 34 (Ereg regs ex) (Ereg regs ex)) by apply env_agree_refl.
unfold cfg_at. change (w64 HDB_K) with (Z_to_bv 64 HDB_K).
aj_run_to_tok rt7b_tbl_ok HS HJ SHOK RTMB_B_span HDB_C2.
1-2: (* the shadow checks of the two bytes *)
  cbn [ms_mem mkst]; unfold RTMB_B_Bx;
  lazymatch goal with |- range_addressable _ _ (U _ (SOff 26 ?j)) _ =>
    rewrite (U_atom _ 20 SHADOW_OFF X20 ltac:(unfold SHADOW_OFF; lia)),
      (U_atom_off _ 26 (cur - 1) j X26 ltac:(lia) ltac:(lia));
    replace (cur - 1 + j) with (cur + (j - 1)) by lia;
    refine (rtmb_in_ra _ _ cur 2 (j - 1) HRA _); lia end.
- hdb_awr.
  apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil].
- lazymatch type of HS with st_ok _ ?E' _ _ =>
    assert (HA : env_agree 34 (Ereg regs ex) E') by env_agree_chain HA34 end.
  destruct HA as [HA _].
  hdb_leaf HS HJ.
  + eapply (regs_kept_of_st_ok rsegs _ _ ms regs ex (w_H W) _ HS); [env_agree_chain HAE | vm_compute; reflexivity].
  + hdb_kept HFr hdb_wNone ltac:(fun H => exfalso; lia).
  + cbv beta. split; [|split; [|split]].
    * hdb_reg HS (13%bv : bv 5). apply hdb_denot_ext8; [rewrite HA by lia; exact X32 | lia].
    * hdb_reg HS (25%bv : bv 5). apply hdb_denot_ext8; [rewrite HA by lia; exact X33 | lia].
    * hdb_reg HS (26%bv : bv 5).
      rewrite (hdb_denot_off _ 26 (cur - 1) 3 ltac:(rewrite HA by lia; exact X26) ltac:(lia) ltac:(lia)).
      unfold w64. f_equal. lia.
    * hdb_reg HS (6%bv : bv 5).
      rewrite (hdb_denot_off _ 6 (n + 1) (-3) ltac:(rewrite HA by lia; exact X6) ltac:(lia) ltac:(lia)).
      unfold w64. f_equal. lia.
Qed.

End d.
End b.

Print Assumptions hdb_T1.
Print Assumptions hdb_T0.
Print Assumptions hdb_TE.
Print Assumptions hdb_C1.
Print Assumptions hdb_C2.
Print Assumptions hdb_K1.
Print Assumptions hdb_K2.
