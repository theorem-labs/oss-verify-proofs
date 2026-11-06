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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 824 of its 867 lines of code are new or changed and 410 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a10b_b.v, with its module paths and module names changed; 567 of its 617 lines of code are new or changed and 817 lines of the source are left out. *)
(* Segment A4 of the walk of reac_segconf_parse_file on reac-pw/fuzz_segconf's ASan image A
   (fuzz_segconf.asan 0x87a78): from the cut DONE (0x88bb8, lib/A/Prog/pf_pieces.v PF_DONE) to the return
   (0x88c64). It proves pf_pieces.v's S_A4, that is H_DONE at every FP state: from INV_DONE the walk reaches
   PF_POSTr v cf, the contract's post with the final record cf.

   The code (dis/reac_segconf_parse_file.fuzz_segconf.asan.s; 54 instructions over 0x88bb8-0x88c68 and the cold
   0x88c90-0x88cb8), in three runs:
     RUN A  0x88bb8-0x88c10, the PLAIN executor (the run writes shadow bytes, so a token run is not allowed:
       maps/pa-walk-map.md section 2.3, YCbn.v cells_safe_b):
         0x88bb8 ld a0,0x60(s1)      the shadow OFFSET of &c->n, (c + RC_N) / 8, put in slot 0x60 at 0x87d6c
         0x88bbc add s6,a0,s6        s6 = SHADOW_OFF (pf_fi) + that = shadow_addr (c + RC_N)
         0x88bc0 lb a0,0(s6)         check #40's shadow byte, which is 0 (a4_shadow_zero below)
         0x88bc4 bnez a0,0x88c90     not taken; the slow block 0x88c90-0x88ca4 is not run
         0x88bc8 ld a0,0x80(s1)      &c->n            0x88bcc lw s2,0(a0)   s2 = c->n = length (rc_seg cf)
         0x88bd0 addi a0,zero,-8     0x88bd4 sb a0,4(s11)  0x88bd8 sb a0,5(s11)   cur_name out of scope (0xf8)
         0x88bdc ld s7,0x68(s1)      F, the class-5 frame       0x88be0 j 0x88bf8
         0x88bf8 ld a0,0x88(s1)      F again (slot 0x88)
         0x88bfc-0x88c04 sd 0x45e0360e,0(s7)   the retired-frame word at F[0]
         0x88c08 beqz a0,0x88c18     not taken (F >= 4096, the frame's bound), so the INLINE release
                                     0x88c18-0x88c20 (meta_fill_00) is dead
         0x88c0c addi a1,zero,0x480  0x88c10 jal frame_release_5
     THE CALL  __asan_stack_free_5 (pa_sigma SS___asan_stack_free_5) on this call's own newest frame, by
       pf_a4_k.v's aj_stack_free_cls_atS over the hypothesis ASF5 (RtStack.astack_free_cls_realizes .. 5).
     RUN C  0x88c14-0x88c64, the plain executor: `j 0x88c24`, a0 = s2, sp = s0 - 0x140, the 13 saved registers
       reloaded from sp0 - 8 - 8 j, `addi sp,sp,0x140`, `ret`.
   Dead code of the segment, as the lane's notes (not in the tree) record: 0x88be4-0x88bf4 (check #41, the
   text-NULL return: the `j 0x88bf8` at 0x88be0 jumps over it), 0x88c18-0x88c20 (the inline release), the stub
   0x88ca8-0x88cb8, and the slow block of check #40 (0x88c90-0x88ca4), which the zero shadow byte decides.

   Check #40 (the only check of the segment that is reached) needs the shadow byte of the granule of &c->n to be
   0. reader_pre's sa_addr rd c SEG_C_SIZE gives it: the granule's LAST byte c + RC_N + 7 has x mod 8 = 7, and
   range_addressable's saddr_ok leaves only s = 0 for such a byte (a4_shadow_zero).

   The form is the released image-A walk form (origin/ossv/recipes 501c0d516c69, plugin-hostd/fuzz_command's
   lib/A/Prog/check_round_trip.v crt_epi at :5003, the one released walk whose side-stack frame is released by a
   CALL). The post is apost_base, lifted to the statement's apost_baseF by PaFx.v apost_baseF_of_base (this
   segment reaches no printf wrapper, so the FP state is the ambient one).

   Section hypotheses (pf_pieces.v's list for A4, plus the model laws the release needs):
     ASF5 : RtStack.astack_free_cls_realizes at pa_sigma SS___asan_stack_free_5, class 5, at every FP state
     ML   : model_laws (as_universe B)        (aj_stack_free_cls_atS's ml_stack_free; check_round_trip.v:164)
   pf_pieces.v's list (:681-682) also names astack_free_law and frame_flag_lawP for A4: they are the laws of the
   INLINE release (0x88c18-0x88c20), which is dead here, so this proof does not take them (the contract's own
   note N1, reac_segconf_parse_file_c.v:97-100, says the same). ML is discharged at the pinned image by
   SegRecRest.seg_model_laws (listing stage 2), as fuzz_command's closing files discharge it by
   CmdRecRest.cmd_model_laws. No SSPX, VRO or ROMV: the segment re-establishes no pf_obj and calls no refuse.

   Segment A4's proof, 2026-10-30. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegSyms SegList SegPa SegPaLib PaLibF PaLibG
PaLibH PaSB PaDenot PaCall PaCallRun PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegGlob SegObj SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtStack.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import pf_pieces pf_a4_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require pf_a5_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ===================== 0. the pcs of the segment, as listing offsets ===================== *)
(* the return of the frame_release_5 call, 0x88c14 *)
Definition PF_RET4 : Z := AF_reac_segconf_parse_file + 0x119c.

(* ===================== 1. the record's n field, through a reader ===================== *)
(* The four little-endian bytes seg_spec.u32_enc fixes (its le4 of Z_to_bv 64 v). The shape of these lemmas is
   the cross_check walk's lib/A/Prog/cross_check_f.v (ccf_le .. sa_rconf_n); they are restated here because that
   file belongs to another walk and this walk must not Require it. *)
Fixpoint a4_le (n : nat) (z : Z) : list byte :=
  match n with O => [] | S n' => Z_to_bv 8 z :: a4_le n' (Z.shiftr z 8) end.
Lemma a4_nth_le : forall n z k, (k < n)%nat -> nth k (a4_le n z) ZB0 = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
induction n as [|n IH]; intros z k Hk; [lia|].
cbn [a4_le]. destruct k as [|k].
- cbn [nth]. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
- cbn [nth]. rewrite IH by lia. f_equal. rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.
Lemma a4_u32_enc_le : forall v f, seg_spec.u32_enc v f -> 0 <= v < 2 ^ 32 /\ f = a4_le 4 v.
Proof.
intros v f [Hv Hf]. split; [exact Hv|]. rewrite Hf.
transitivity (a4_le 4 (bv_unsigned (Z_to_bv 64 v))); [reflexivity|]. rewrite unsigned_lit_small by lia. reflexivity.
Qed.
Lemma a4_u32_byte : forall v k, 0 <= v < 2 ^ 32 -> (k < 4)%nat ->
  bv_unsigned (nth k (a4_le 4 v) ZB0) = le_byte v 4 k.
Proof.
intros v k Hv Hk. rewrite a4_nth_le by exact Hk. rewrite Z_to_bv_unsigned. unfold le_byte, bv_wrap.
change (bv_modulus 8) with 256. change (8 * Z.of_nat 4) with 32.
rewrite (Z.mod_small v (2 ^ 32)) by lia. reflexivity.
Qed.
Lemma a4_nth_firstn : forall {A} (l : list A) n i d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
intros A l n; revert l; induction n as [|n IH]; intros l i d Hi; [lia|].
destruct l as [|x l]; [destruct i; reflexivity|].
destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.
Lemma a4_nth_fld : forall (bs : list byte) off n i d, (i < n)%nat ->
  nth i (seg_spec.fld off n bs) d = nth (off + i) bs d.
Proof. intros bs off n i d Hi. unfold seg_spec.fld. rewrite a4_nth_firstn by exact Hi. apply PaArt.nth_skipn_add. Qed.
(* c->n = the number of entries, as the four bytes at c + RC_N *)
Lemma a4_rconf_n : forall (rd : reader) c rcs, sa_rconf rd c rcs ->
  sa_val rd (c + seg_spec.RC_N) 4 (Z.of_nat (length (rc_seg rcs))) /\ (length (rc_seg rcs) <= 32)%nat.
Proof.
intros rd c rcs (bs & Hb & Henc). pose proof Henc as (Hl & H32 & _ & Hn & _).
split; [|exact H32].
apply a4_u32_enc_le in Hn. destruct Hn as [Hv Hf].
intros k Hk.
assert (Hi : (Z.to_nat seg_spec.RC_N + k < length bs)%nat)
  by (unfold seg_spec.SEG_C_SIZE in Hl; unfold seg_spec.RC_N; lia).
replace (c + seg_spec.RC_N + Z.of_nat k) with (c + Z.of_nat (Z.to_nat seg_spec.RC_N + k))
  by (unfold seg_spec.RC_N; lia).
rewrite (Hb _ Hi). f_equal.
unfold seg_spec.fldz in Hf.
rewrite <- (a4_nth_fld bs (Z.to_nat seg_spec.RC_N) (Z.to_nat 4) k ZB0 ltac:(cbn; lia)).
rewrite Hf. apply a4_u32_byte; [lia | exact Hk].
Qed.

(* ===================== 2. the shadow byte of &c->n ===================== *)
(* A granule whose last byte is addressable has shadow byte 0: saddr_ok x s with x mod 8 = 7 leaves only s = 0. *)
Lemma a4_shadow_zero : forall (rd : reader) c, sa_addr rd c seg_spec.SEG_C_SIZE -> c mod 8 = 0 ->
  rd (SHADOW_OFF + (c + seg_spec.RC_N) / 8) = Some 0.
Proof.
intros rd c (_ & _ & _ & HRA & _) Hc.
assert (Hy : (c + seg_spec.RC_N) mod 8 = 0).
{ unfold seg_spec.RC_N. rewrite Zplus_mod, Hc. reflexivity. }
pose proof (Z.div_mod (c + seg_spec.RC_N) 8 ltac:(lia)) as D.
destruct (HRA (c + seg_spec.RC_N + 7)) as (s & Hs & Hok);
  [unfold seg_spec.RC_N, seg_spec.SEG_C_SIZE in *; lia|].
assert (E : shadow_of_addr SHADOW_OFF (c + seg_spec.RC_N + 7) = SHADOW_OFF + (c + seg_spec.RC_N) / 8).
{ unfold shadow_of_addr. f_equal.
  replace (c + seg_spec.RC_N + 7) with (8 * ((c + seg_spec.RC_N) / 8) + 7) by lia.
  rewrite Z.mul_comm, Z.div_add_l by lia. change (7 / 8) with 0. lia. }
rewrite E in Hs.
assert (Hm : (c + seg_spec.RC_N + 7) mod 8 = 7).
{ replace (c + seg_spec.RC_N + 7) with (7 + ((c + seg_spec.RC_N) / 8) * 8) by lia.
  rewrite Z.mod_add by lia. reflexivity. }
destruct Hok as [-> | (H1 & H2)]; [exact Hs | exfalso; lia].
Qed.

(* ===================== 3. where a shadow cell of a low object lies ===================== *)
(* the bound check_round_trip.v's crt_epi proves for its frame's shadow (its HSH1, :5012-5015) *)
Lemma a4_shadow_bounds : forall x, 0 <= x <= 0x7fffff800000 ->
  SHADOW_OFF <= SHADOW_OFF + x / 8 /\ SHADOW_OFF + x / 8 + 300 < kHighMemBeg.
Proof.
intros x Hx.
assert (D1 : 0 <= x / 8) by (apply Z.div_pos; lia).
assert (D2 : x / 8 <= 17592184995840) by (apply Z.div_le_upper_bound; lia).
unfold SHADOW_OFF, kHighMemBeg. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).

(* a 4-byte or 8-byte cell of a reader, as the symbolic state's chunks want it *)
Lemma a4_val_of_sa : forall (H : word -> bool) (m : word -> option byte) a n v,
  sa_val (aview SEGS H m) a n v -> val_mem SEGS (mrestrict H m) a n v.
Proof.
intros H m a n v Hv k Hk.
destruct (aview_byte SEGS H m (a + Z.of_nat k) _ (Hv k Hk)) as (b & Hb & Hbv & _).
rewrite Hb. f_equal. change (YO0f.le_byte v n k) with (YG0f.le_byte v n k).
rewrite Hbv. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
End f.
End d.

(* ===================== 4. the symbolic states of the two runs ===================== *)
(* RUN A, seeded at DONE. The atoms above the 32 registers: 32 = c, 33 = c->n, 34 = (c + RC_N) / 8 (the shadow
   OFFSET of &c->n, which slot 0x60 holds), 35 = F. s6 is pinned to the literal shadow base SB, so the address
   `add s6,a0,s6` of check #40 normalizes to SOff 34 SB and the plain executor reads it from a4_band. *)
Definition a4_slots : YP09.region := YP09.mkRegion (Some 9%nat) 0x60 0x90 0x60 0x60
  [YP09.mkChunk 0x60 (CVal 8 (SOff 34 0)); YP09.mkChunk 0x68 (CVal 8 (SOff 35 0));
   YP09.mkChunk 0x80 (CVal 8 (SOff 32 seg_spec.RC_N)); YP09.mkChunk 0x88 (CVal 8 (SOff 35 0))].
Definition a4_cn : YP09.region := YP09.mkRegion (Some 32%nat) seg_spec.RC_N (seg_spec.RC_N + 4)
  seg_spec.RC_N seg_spec.RC_N [YP09.mkChunk seg_spec.RC_N (CVal 4 (SOff 33 0))].
Definition a4_band : YP09.region := YP09.mkRegion (Some 34%nat) SB (SB + 1) SB SB
  [YP09.mkChunk SB (CVal 1 (SLit 0))].
Definition a4_fh : YP09.region := YP09.mkRegion (Some 35%nat) 0 8 0 8 [].
Definition a4_fsh : YP09.region := YP09.mkRegion (Some 27%nat) 4 6 4 6 [].
Definition a4_facts : facts := mkFacts [(33%nat, mkAF 0 32 0); (35%nat, PTR 5)] [] [].
Definition ss_a4_0 : sstate := mkSS PF_DONE sr_atoms [a4_slots; a4_cn; a4_band; a4_fh; a4_fsh] None a4_facts.
(* RUN C, seeded at the return of the release call: the 13 saved slots at sp0 - 8 - 8 j, read-only, their values
   the atoms 32 + j (the entry's ra, s0, s1, s2 .. s11, in slot order: pf_pieces.v PF_SAVED) *)
Definition a4_stk : YP09.region := YP09.mkRegion (Some 8%nat) (-104) 0 0 0
  (map (fun j => YP09.mkChunk (-8 - 8 * Z.of_nat j) (CVal 8 (SOff (32 + j) 0))) (seq 0 13)).
Definition ss_a4c : sstate := mkSS PF_RET4 sr_atoms [a4_stk] None (mkFacts [] [] []).
(* every byte the segment may write: the frame's first word (the retired-frame word), the frame's shadow (the
   two cur_name cells inline, the whole 256 cells by the release entry), the frame's flag byte, and the release
   entry's own stack window *)
Definition a4_Wr (Fa SHa s1a FLa a : Z) : Prop :=
  (Fa <= a < Fa + 8) \/ (SHa <= a < SHa + 256) \/ a = FLa \/ (s1a - YG0d.ESTACK <= a < s1a).

(* read a register of a run's state, as check_round_trip.v's crt_rreg (:713-722) *)
Ltac a4_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let val := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with val
 | st_ok ?sg ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_restrict_reg sg Hh E ss ms r HS);
  let val := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with val
 end end.
Ltac a4_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?x] =>
    let val := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with val end; lia.

Section g. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
(* the release entry (pf_pieces.v's hypothesis list for A4), at every FP state *)
Hypothesis ASF5 : forall fx0 : YK11.FPState,
  @astack_free_cls_realizes fx0 rc SEGS B (SIG SS___asan_stack_free_5) 5.
(* the model laws, which aj_stack_free_cls_atS's ml_stack_free needs (check_round_trip.v:164) *)
Hypothesis ML : model_laws (as_universe B).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

Lemma a4_reg_bv : forall (rr : bvmap 5 word) (k : Z) (r : bv 5) val,
  bv_unsigned r = k -> getr rr (Z_to_bv 5 k) = val -> getr rr r = val.
Proof. intros rr k r val Hr H. subst k. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma a4_sl : forall (rd : reader) b L o val, pf_sl rd b L -> In (o, val) L -> rdword rd (b + o) = Some val.
Proof. intros rd b L o val H Hin. exact (proj1 (Forall_forall _ _) H (o, val) Hin). Qed.
Lemma a4_den_atom0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.
Lemma a4_den_off : forall E n v k, bv_unsigned (ew E n) = v -> sv_denot E (SOff n k) = Z_to_bv 64 (v + k).
Proof. intros E n v k H. cbn [sv_denot]. rewrite H. reflexivity. Qed.

Section h. Context {fx : YK11.FPState}.

Lemma a4_done : H_DONE B.
Proof.
unfold H_DONE. intros v pos lyc Sc Wc rX memc mdc cf HINV.
destruct HINV as (HCX & HFI & HOBJ & HRC & HSL & HFSH & HRG).
destruct HCX as (HPRE & HROD & H10 & Hc64 & H11 & Ht64 & H12 & Hlp64 & HFE & HROOM & HEV).
destruct HFE as (fe & HPREC).
destruct HFI as (HJ & Ely & HSfs & HPERM & HSAV & HFLG & HFRM & HRGF).
destruct HOBJ as (_ & _ & _ & HCADDR & HCHEAP & _ & _ & _ & _).
subst lyc.
pose proof HPREC as ((Hc0 & Hc16 & _) & _).
(* fe is the FP state of the contract's premise; drop it so that the FP state of every seed below is the
   ambient fx (FPState is a class: a second one in scope is picked by instance resolution) *)
clear HPREC fe.
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : YG0d.ESTACK = 4096) by reflexivity.
assert (HSOFF : SHADOW_OFF = 2147450880) by reflexivity.
assert (HKLSB : kLowShadowBeg = 2147446784) by reflexivity.
assert (HSB : SB = 2147450880) by reflexivity.
assert (Hsp0e : pf_sp0 v = spZ (p_regs v)) by reflexivity.
assert (HFe : pf_F v pos = frame_addr (p_ly v) 5 pos) by reflexivity.
assert (HFLe : pf_FL v pos = flag_addr (p_ly v) 5 pos) by reflexivity.
assert (HSHe : pf_SH v pos = shadow_addr (frame_addr (p_ly v) 5 pos)) by reflexivity.
rewrite <- Hsp0e in Hal16.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & F1 & F2 & F3 & F4 & Hgone & Hpres &
  Hstatic & F5 & HQTc).
assert (EFB : fs_frame_bytes 5 = 2048) by (vm_compute; reflexivity).
assert (Hin5 : In (5, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS (p_ly v) Sc Wc memc mdc 5 pos HAR Hin5) as (HF1 & HF2 & HF3).
destruct (al_frames _ _ LAWS (p_ly v) Sc Wc memc mdc 5 pos HAR Hin5) as (HFal & _ & HFpres & HFspres).
destruct (al_flag _ _ LAWS (p_ly v) Sc Wc memc mdc 5 pos HAR Hin5) as (HFLpres & HFLown & HFLapp & HFLlt).
rewrite EFB in HF2, HF3, HFpres, HFspres.
destruct HCHEAP as (bb & mm & Hbin & Hble & Hbhi).
destruct (al_blocks _ _ LAWS (p_ly v) Sc Wc memc mdc bb mm HAR Hbin)
  as (Hb16 & Hb4096 & Hbceil & Hbapp & Hbpo & _ & Hbm).
pose proof (req_size_pos mm (proj1 Hbm)) as (Hrq1 & Hrq2).
pose proof (sep_block_frame SEGS B LAWS (p_ly v) Sc Wc memc mdc bb mm 5 pos HAR Hbin Hin5) as Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite EFB in Hsep.
destruct (a4_rconf_n (rdW Wc memc) (p_c v) cf HRC) as (HNVAL & HN32).
assert (Hc8 : p_c v mod 8 = 0).
{ pose proof (Z.div_mod (p_c v) 16 ltac:(lia)) as D16. rewrite Hc16 in D16.
  replace (p_c v) with ((2 * (p_c v / 16)) * 8) by lia. apply Z_mod_mult. }
pose proof (a4_shadow_zero (rdW Wc memc) (p_c v) HCADDR Hc8) as HSH0.
(* ---------- the cut's registers and slots ---------- *)
assert (R2 : getr rX 2%bv = w64 (pf_s1 v))
  by (apply (a4_reg_bv _ 2); [reflexivity | apply (pf_a5_k.a5_rg_get rX _ _ _ HRGF); cbn [In]; tauto]).
assert (R3 : getr rX 3%bv = w64 (as_gp B))
  by (apply (a4_reg_bv _ 3); [reflexivity | apply (pf_a5_k.a5_rg_get rX _ _ _ HRGF); cbn [In]; tauto]).
assert (R4 : getr rX 4%bv = w64 (as_tp B))
  by (apply (a4_reg_bv _ 4); [reflexivity | apply (pf_a5_k.a5_rg_get rX _ _ _ HRGF); cbn [In]; tauto]).
assert (R8 : getr rX 8%bv = w64 (pf_sp0 v))
  by (apply (a4_reg_bv _ 8); [reflexivity | apply (pf_a5_k.a5_rg_get rX _ _ _ HRGF); cbn [In]; tauto]).
assert (R9 : getr rX 9%bv = w64 (pf_s1 v))
  by (apply (a4_reg_bv _ 9); [reflexivity | apply (pf_a5_k.a5_rg_get rX _ _ _ HRGF); cbn [In]; tauto]).
assert (R22 : getr rX 22%bv = w64 SHADOW_OFF)
  by (apply (a4_reg_bv _ 22); [reflexivity | apply (pf_a5_k.a5_rg_get rX _ _ _ HRGF); cbn [In]; tauto]).
assert (R27 : getr rX 27%bv = w64 (pf_SH v pos))
  by (apply (a4_reg_bv _ 27); [reflexivity | apply (pf_a5_k.a5_rg_get rX _ _ _ HRG); cbn [In]; tauto]).
assert (S60 : rdword (rdW Wc memc) (pf_s1 v + 0x60) = Some ((p_c v + seg_spec.RC_N) / 8))
  by (apply (a4_sl _ _ _ _ _ HSL); cbn [In]; tauto).
assert (S68 : rdword (rdW Wc memc) (pf_s1 v + 0x68) = Some (pf_F v pos))
  by (apply (a4_sl _ _ _ _ _ HSL); cbn [In]; tauto).
assert (S80 : rdword (rdW Wc memc) (pf_s1 v + 0x80) = Some (p_c v + seg_spec.RC_N))
  by (apply (a4_sl _ _ _ _ _ HSL); cbn [In]; tauto).
assert (S88 : rdword (rdW Wc memc) (pf_s1 v + 0x88) = Some (pf_F v pos))
  by (apply (a4_sl _ _ _ _ _ HSL); cbn [In]; tauto).
(* ---------- the numbers the regions, the keeps and the call need ---------- *)
assert (HSTKlo : 12624 <= STK_reac_segconf_parse_file).
{ unfold STK_reac_segconf_parse_file.
  pose proof (Z.le_max_r STK_refuse (3 * YG0d.ESTACK)). lia. }
assert (Hs1a : pf_s1 v <= pf_sp0 v - 320 /\ pf_sp0 v - 352 < pf_s1 v /\ pf_s1 v mod 32 = 0).
{ unfold pf_s1. pose proof (Z.mod_pos_bound (pf_sp0 v - 0x140) 32 ltac:(lia)) as Hm.
  split; [lia|]. split; [lia|].
  replace (pf_sp0 v - 0x140 - (pf_sp0 v - 0x140) mod 32) with ((pf_sp0 v - 0x140) / 32 * 32)
    by (pose proof (Z.div_mod (pf_sp0 v - 0x140) 32 ltac:(lia)); lia).
  apply Z_mod_mult. }
destruct Hs1a as (Hs1le & Hs1gt & Hs1m32).
assert (Hs1hi : alloc_ceiling + 12272 <= pf_s1 v) by (lia).
assert (HFlo : 4096 <= pf_F v pos) by exact HF1.
assert (HFhi : pf_F v pos + 2048 <= alloc_ceiling) by exact HF2.
assert (HSHdef : pf_SH v pos = SHADOW_OFF + pf_F v pos / 8) by reflexivity.
destruct (a4_shadow_bounds (pf_F v pos) ltac:(lia)) as (HSHlo & HSHhi).
rewrite <- HSHdef in HSHlo, HSHhi.
assert (HCSZ : p_c v + seg_spec.SEG_C_SIZE <= bb + req_size mm) by lia.
destruct (a4_shadow_bounds (p_c v + seg_spec.RC_N) ltac:(unfold seg_spec.RC_N, seg_spec.SEG_C_SIZE in *; lia))
  as (HBlo & HBhi).
unfold in_app in Hbapp, HF3. destruct Hbapp as (Hbapp0 & Hbapp1). destruct HF3 as (HF3a & HF3b).
unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hbapp1, HF3b.
(* the division facts for the two shadow offsets *)
pose proof (Z.div_mod (pf_F v pos) 8 ltac:(lia)) as DF.
pose proof (Z.mod_pos_bound (pf_F v pos) 8 ltac:(lia)) as DFm.
pose proof (Z.div_mod (p_c v + seg_spec.RC_N) 8 ltac:(lia)) as DC.
pose proof (Z.mod_pos_bound (p_c v + seg_spec.RC_N) 8 ltac:(lia)) as DCm.
assert (HdivF : (p_c v + seg_spec.RC_N) / 8 <= pf_F v pos / 8 \/
                pf_F v pos / 8 + 256 <= (p_c v + seg_spec.RC_N) / 8).
{ destruct Hsep as [Hd | Hd].
  - left. apply Z.div_le_mono; [lia | unfold seg_spec.RC_N, seg_spec.SEG_C_SIZE in *; lia].
  - right.
    assert (Hle : pf_F v pos + 256 * 8 <= p_c v + seg_spec.RC_N) by (unfold seg_spec.RC_N in *; lia).
    apply (Z.le_trans _ ((pf_F v pos + 256 * 8) / 8)).
    + rewrite Z.div_add by lia. lia.
    + apply Z.div_le_mono; lia. }
(* ---------- the writes of the segment are apart from the block, the saved slots and the frame ---------- *)
assert (APART : forall a,
  (p_c v <= a < p_c v + seg_spec.SEG_C_SIZE) \/ (pf_sp0 v - 104 <= a < pf_sp0 v) \/
  (pf_F v pos + 8 <= a < pf_F v pos + 2048) ->
  ~ a4_Wr (pf_F v pos) (pf_SH v pos) (pf_s1 v) (pf_FL v pos) a).
{ intros a Ha HW. unfold a4_Wr in HW.
  destruct Ha as [Ha | [Ha | Ha]].
  - destruct HW as [HW | [HW | [HW | HW]]].
    + destruct Hsep as [Hd | Hd]; unfold seg_spec.SEG_C_SIZE in *; lia.
    + destruct Hbapp1 as [Hd | Hd]; unfold seg_spec.SEG_C_SIZE in *; lia.
    + destruct (Hbpo a ltac:(lia)) as (_ & Hno). rewrite HW in Hno. exact (Hno HFLown).
    + unfold seg_spec.SEG_C_SIZE in *; lia.
  - destruct HW as [HW | [HW | [HW | HW]]]; [lia | lia | | lia].
    rewrite HW in Ha. lia.
  - destruct HW as [HW | [HW | [HW | HW]]].
    + lia.
    + destruct HF3b as [Hd | Hd]; lia.
    + destruct (HFpres a ltac:(lia)) as (_ & Hno). rewrite HW in Hno. exact (Hno HFLown).
    + lia. }
(* ---------- the environment of RUN A ---------- *)
pose proof (Eimg_env (Ereg rX [w64 (p_c v); w64 (Z.of_nat (length (rc_seg cf)));
  w64 ((p_c v + seg_spec.RC_N) / 8); w64 (pf_F v pos)])) as HEI.
set (Ex := [w64 (p_c v); w64 (Z.of_nat (length (rc_seg cf))); w64 ((p_c v + seg_spec.RC_N) / 8);
  w64 (pf_F v pos)]) in HEI |- *.
set (EA := Eimg (Ereg rX Ex)) in HEI |- *.
assert (EW9 : ew EA 9 = w64 (pf_s1 v)).
{ unfold EA. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat rX Ex 9%nat 9%bv eq_refl). exact R9. }
assert (EW2 : ew EA 2 = w64 (pf_s1 v)).
{ unfold EA. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat rX Ex 2%nat 2%bv eq_refl). exact R2. }
assert (EW27 : ew EA 27 = w64 (pf_SH v pos)).
{ unfold EA. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat rX Ex 27%nat 27%bv eq_refl). exact R27. }
assert (EW22 : ew EA 22 = w64 SHADOW_OFF).
{ unfold EA. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat rX Ex 22%nat 22%bv eq_refl). exact R22. }
assert (EW32 : ew EA 32 = w64 (p_c v))
  by (unfold EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX Ex 0)).
assert (EW33 : ew EA 33 = w64 (Z.of_nat (length (rc_seg cf))))
  by (unfold EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX Ex 1)).
assert (EW34 : ew EA 34 = w64 ((p_c v + seg_spec.RC_N) / 8))
  by (unfold EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX Ex 2)).
assert (EW35 : ew EA 35 = w64 (pf_F v pos))
  by (unfold EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX Ex 3)).
assert (BVS : forall n val, bv_unsigned (ew EA n) = val -> base_val EA (Some n) = val)
  by (intros n val Hn; exact Hn).
assert (U9 : bv_unsigned (ew EA 9) = pf_s1 v) by (rewrite EW9; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew EA 27) = pf_SH v pos) by (rewrite EW27; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew EA 32) = p_c v) by (rewrite EW32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew EA 33) = Z.of_nat (length (rc_seg cf)))
  by (rewrite EW33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew EA 34) = (p_c v + seg_spec.RC_N) / 8)
  by (rewrite EW34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew EA 35) = pf_F v pos) by (rewrite EW35; apply unsigned_lit_small; lia).
(* ---------- the seed of RUN A ---------- *)
assert (HS0 : st_ok_pi SEGS VAL EA ss_a4_0
  (restrict (w_H Wc) (@mkst fx rX (Z_to_bv 64 (BASE + PF_DONE)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_a4_0. apply pa_entry_st_ok_full.
  - unfold EA. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons;
      [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]]].
    + (* the slots *)
      unfold a4_slots, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons;
        [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_cons; [| apply Forall_nil]]]].
      * apply (chunk_ok_val SEGS EA _ _ _ 8%N _ ((p_c v + seg_spec.RC_N) / 8));
          [ rewrite a4_den_atom0, EW34; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia
          | exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ S60) ].
      * apply (chunk_ok_val SEGS EA _ _ _ 8%N _ (pf_F v pos));
          [ rewrite a4_den_atom0, EW35; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia
          | exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ S68) ].
      * apply (chunk_ok_val SEGS EA _ _ _ 8%N _ (p_c v + seg_spec.RC_N));
          [ rewrite (a4_den_off EA 32 (p_c v) seg_spec.RC_N U32); reflexivity
          | change (8 * Z.of_N 8) with 64; unfold seg_spec.RC_N, seg_spec.SEG_C_SIZE in *; lia | lia
          | exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ S80) ].
      * apply (chunk_ok_val SEGS EA _ _ _ 8%N _ (pf_F v pos));
          [ rewrite a4_den_atom0, EW35; reflexivity
          | change (8 * Z.of_N 8) with 64; lia | lia
          | exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ S88) ].
    + (* c->n *)
      unfold a4_cn, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U32.
      split; [unfold seg_spec.RC_N; lia|].
      split; [unfold seg_spec.RC_N, seg_spec.SEG_C_SIZE in *; lia|].
      split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS EA _ _ _ 4%N _ (Z.of_nat (length (rc_seg cf))));
        [ rewrite a4_den_atom0, EW33; reflexivity
        | change (8 * Z.of_N 4) with 32; lia | lia
        | exact (a4_val_of_sa (w_H Wc) memc _ 4%nat _ HNVAL) ].
    + (* the shadow byte of &c->n *)
      unfold a4_band, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U34.
      split; [unfold SB; lia|]. split; [unfold SB, SHADOW_OFF in *; lia|].
      split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val SEGS EA _ _ _ 1%N _ 0);
        [ reflexivity | change (8 * Z.of_N 1) with 8; lia | lia |].
      apply (a4_val_of_sa (w_H Wc) memc _ 1%nat 0).
      intros kk Hkk. assert (Ek : kk = 0%nat) by lia. subst kk.
      change (le_byte 0 1 0) with 0. rewrite Z.add_0_r.
      replace ((p_c v + seg_spec.RC_N) / 8 + SB) with (SHADOW_OFF + (p_c v + seg_spec.RC_N) / 8)
        by (unfold SB, SHADOW_OFF; lia).
      exact HSH0.
    + (* the frame's first word *)
      unfold a4_fh, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U35.
      split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFpres (pf_F v pos + o) ltac:(lia))).
    + (* the two cur_name shadow cells *)
      unfold a4_fsh, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U27.
      split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS).
      replace (pf_SH v pos + o) with (shadow_addr (frame_addr (p_ly v) 5 pos) + o) by reflexivity.
      exact (proj1 (HFspres o ltac:(change (2048 / 8) with 256; lia))).
  - (* the regions are pairwise disjoint *)
    assert (BA9 : base_val EA (YP09.r_base a4_slots) = pf_s1 v) by exact U9.
    assert (BA32 : base_val EA (YP09.r_base a4_cn) = p_c v) by exact U32.
    assert (BA34 : base_val EA (YP09.r_base a4_band) = (p_c v + seg_spec.RC_N) / 8) by exact U34.
    assert (BA35 : base_val EA (YP09.r_base a4_fh) = pf_F v pos) by exact U35.
    assert (BA27 : base_val EA (YP09.r_base a4_fsh) = pf_SH v pos) by exact U27.
    assert (LH : YP09.r_lo a4_slots = 0x60 /\ YP09.r_hi a4_slots = 0x90 /\
                 YP09.r_lo a4_cn = seg_spec.RC_N /\ YP09.r_hi a4_cn = seg_spec.RC_N + 4 /\
                 YP09.r_lo a4_band = SB /\ YP09.r_hi a4_band = SB + 1 /\
                 YP09.r_lo a4_fh = 0 /\ YP09.r_hi a4_fh = 8 /\
                 YP09.r_lo a4_fsh = 4 /\ YP09.r_hi a4_fsh = 6)
      by (repeat split; reflexivity).
    destruct LH as (LS & HS' & LC & HC & LB & HB & LF & HF & LZ & HZ).
    cbn [pairwise_disjoint all_disjoint].
    unfold SB, seg_spec.RC_N, seg_spec.SEG_C_SIZE, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *.
    repeat split; unfold extent_disjoint;
      rewrite ?BA9, ?BA32, ?BA34, ?BA35, ?BA27, ?LS, ?HS', ?LC, ?HC, ?LB, ?HB, ?LF, ?HF, ?LZ, ?HZ.
    + right; lia.
    + right; lia.
    + right; lia.
    + right; lia.
    + destruct Hbapp1 as [Hd | Hd]; [left; lia | right; lia].
    + destruct Hsep as [Hd | Hd]; [left; lia | right; lia].
    + destruct Hbapp1 as [Hd | Hd]; [left; lia | right; lia].
    + destruct HF3b as [Hd | Hd]; [right; lia | left; lia].
    + destruct HdivF as [Hd | Hd]; [left; lia | right; lia].
    + destruct HF3b as [Hd | Hd]; [left; lia | right; lia].
  - (* the atom facts *)
    split; [|split; exact I]. cbn [f_atoms a4_facts atoms_ok].
    split; [|split; [|exact I]].
    + unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U33, Z.pow_0_r, Z.mod_1_r.
      repeat split; lia.
    + unfold afact_ok, PTR. cbn [af_lo af_hi af_al2]. rewrite U35. repeat split; try lia. exact HFal. }
(* s6 is the literal shadow base, so the executor reads check #40's byte from the band region *)
assert (HS : st_ok_pi SEGS VAL EA
  (mkSS PF_DONE (sr_set sr_atoms 22%bv (SLit SB)) [a4_slots; a4_cn; a4_band; a4_fh; a4_fsh] None a4_facts)
  (restrict (w_H Wc) (@mkst fx rX (Z_to_bv 64 (BASE + PF_DONE)) memc (seg_rom SEGS)))).
{ exact (st_ok_pi_pin_reg' EA ss_a4_0 _ 22%bv SB HS0 ltac:(exact R22)
    eq_refl). }
pose proof (SRr_run_pi_AJ B LAWS) as RUNP.
pose proof (SRr_run_pi_AJ_call B LAWS) as RUNC.
pose proof (paj_ret_at (PL := PL_seg) (PI := PI)) as RET.
unfold cfg_at. change (w64 (BASE + PF_DONE)) with (Z_to_bv 64 (BASE + PF_DONE)).
paj_run_shc RUNP RUNC HS HJ.
{ (* every byte the run writes is in this call's own frame or its shadow *)
  lazymatch goal with |- awr_ok _ _ ?Ev ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ev rs' stk spx fp b0 bc fr0 lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_cons_ro; [cbn; lia|].
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen; [reflexivity | exact U35 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
    right; right; right; left. exists 5, pos. split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. rewrite EFB. lia. }
  eapply awr_ok_cons_gen; [reflexivity | exact U27 | | apply awr_ok_nil].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha.
    right; right; right; left. exists 5, pos. split; [left; reflexivity|]. right.
    unfold in_zr. cbn [fst snd]. rewrite EFB.
    replace (shadow_addr (frame_addr (p_ly v) 5 pos)) with (pf_SH v pos) by reflexivity.
    change (2048 / 8) with 256. lia. } }
(* ---------- the bytes RUN A kept ---------- *)
pose proof (kept_of_frame (segs := SEGS) EA _ (w_H Wc) memc _
  (fun a => (pf_F v pos <= a < pf_F v pos + 8) \/ (pf_SH v pos + 4 <= a < pf_SH v pos + 6)) HFr
  ltac:(intros b wlo whi a Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin];
                [injection Hq as <- <- <-; cbn [base_val] in Hrr;
                 rewrite ?U9, ?U27, ?U32, ?U34, ?U35 in Hrr; first [left; lia | right; lia | lia] |]);
        destruct Hin)) as K1.
clear HF HFr HG.
(* ---------- the call registers ---------- *)
assert (QA1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + PF_RET4)).
{ a4_rreg HS. apply (codeptr_val EA PF_RET4 HEI). }
assert (QA2 : getr (ms_regs ms) 2 = w64 (pf_s1 v))
  by (a4_rreg HS; rewrite a4_den_atom0; exact EW2).
assert (QA3 : getr (ms_regs ms) 3 = w64 (as_gp B))
  by (a4_rreg HS; rewrite a4_den_atom0; unfold EA;
      rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat rX Ex 3%nat 3%bv eq_refl); exact R3).
assert (QA4 : getr (ms_regs ms) 4 = w64 (as_tp B))
  by (a4_rreg HS; rewrite a4_den_atom0; unfold EA;
      rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat rX Ex 4%nat 4%bv eq_refl); exact R4).
assert (QA8 : getr (ms_regs ms) 8 = w64 (pf_sp0 v))
  by (a4_rreg HS; rewrite a4_den_atom0; unfold EA;
      rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat rX Ex 8%nat 8%bv eq_refl); exact R8).
assert (QA10 : getr (ms_regs ms) 10 = w64 (pf_F v pos))
  by (a4_rreg HS; rewrite a4_den_atom0; exact EW35).
assert (QA11 : getr (ms_regs ms) 11 = w64 1152)
  by (a4_rreg HS; unfold w64; rewrite denot_lit_U, U_SLit; reflexivity).
assert (QA18 : getr (ms_regs ms) 18 = w64 (Z.of_nat (length (rc_seg cf))))
  by (a4_rreg HS; rewrite a4_den_atom0; exact EW33).
(* the flag word is outside what RUN A wrote *)
assert (QFL : rdword (rdW Wc (ms_mem ms)) (frame_addr (p_ly v) 5 pos + fs_frame_bytes 5 - 8)
              = Some (flag_addr (p_ly v) 5 pos)).
{ rewrite EFB.
  replace (frame_addr (p_ly v) 5 pos) with (pf_F v pos) by reflexivity.
  replace (flag_addr (p_ly v) 5 pos) with (pf_FL v pos) by reflexivity.
  rewrite (rdword_ext (rdW Wc memc) (rdW Wc (ms_mem ms))); [rewrite EFB in HFLG; exact HFLG|].
  intros kk Hkk. apply K1; [lia|].
  intros [Hq | Hq]; [lia|]. destruct HF3b as [Hd | Hd]; lia. }
pmkst HS.
eapply SRr_bind.
{ apply (aj_stack_free_cls_atS SEGS B LAWS pa_segs_low ML (SIG SS___asan_stack_free_5) 5 (ASF5 fx)
    ltac:(lia) Wc (ms_regs ms) (ms_mem ms) STK_reac_segconf_parse_file (pf_sp0 v)
    (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [] (p_ly v) Sc _ 0
    (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + PF_RET4)) pos 1152 HJ).
  - unfold spZ at 1. rewrite QA2. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - assert (Hs1m16 : pf_s1 v mod 16 = 0).
    { rewrite (Z.div_mod (pf_s1 v) 32 ltac:(lia)), Hs1m32.
      replace (32 * (pf_s1 v / 32) + 0) with ((2 * (pf_s1 v / 32)) * 16) by lia. apply Z_mod_mult. }
    pose proof (Z.div_mod (pf_s1 v) 16 ltac:(lia)).
    pose proof (Z.div_mod (pf_sp0 v) 16 ltac:(lia)).
    pose proof (Z.div_mod (pf_s1 v - pf_sp0 v) 16 ltac:(lia)).
    pose proof (Z.mod_pos_bound (pf_s1 v - pf_sp0 v) 16 ltac:(lia)).
    lia.
  - lia.
  - lia.
  - exact QA3.
  - exact QA4.
  - exact QA1.
  - apply ret_ok_codeptr_v; [unfold PF_RET4, AF_reac_segconf_parse_file; lia | vm_compute; reflexivity].
  - replace (frame_addr (p_ly v) 5 pos) with (pf_F v pos) by reflexivity. exact QA10.
  - exact QA11.
  - exact QFL. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & K2).
(* ---------- the bytes the whole call kept ---------- *)
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ a4_Wr (pf_F v pos) (pf_SH v pos) (pf_s1 v) (pf_FL v pos) a ->
  rdW Wc mem2 a = rdW Wc memc a).
{ intros a Ha HW. unfold a4_Wr in HW.
  rewrite (K2 a Ha
    ltac:(intros Hc; apply HW; right; left;
          change (shadow_addr (frame_addr (p_ly v) 5 pos)) with (pf_SH v pos) in Hc;
          change (fs_frame_bytes 5 / 8) with 256 in Hc; exact Hc)
    ltac:(intros Hc; apply HW; right; right; left;
          change (flag_addr (p_ly v) 5 pos) with (pf_FL v pos) in Hc; exact Hc)
    ltac:(intros Hc; apply HW; right; right; right; lia)).
  apply K1; [exact Ha | intros [Hc | Hc]; apply HW; [left; exact Hc | right; left; lia]]. }
(* ---------- the seed of RUN C ---------- *)
assert (HPres : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr (ms_regs ms) r).
{ intros r Hr. pose proof (HP2 (bv_unsigned r) Hr) as Hq. rewrite Z_to_bv_bv_unsigned in Hq. exact Hq. }
assert (QB8 : getr regs2 8 = w64 (pf_sp0 v)) by (rewrite (HPres 8%bv ltac:(a4_cs)); exact QA8).
assert (QB18 : getr regs2 18 = w64 (Z.of_nat (length (rc_seg cf))))
  by (rewrite (HPres 18%bv ltac:(a4_cs)); exact QA18).
pose proof (Eimg_env (Ereg regs2 (map (fun r => getr (p_regs v) (Z_to_bv 5 r)) PF_SAVED))) as HEI2.
set (Ex2 := map (fun r => getr (p_regs v) (Z_to_bv 5 r)) PF_SAVED) in HEI2 |- *.
set (EC := Eimg (Ereg regs2 Ex2)) in HEI2 |- *.
assert (EX0 : forall j r, nth_error PF_SAVED j = Some r ->
  ew EC (32 + j)%nat = getr (p_regs v) (Z_to_bv 5 r)).
{ intros j r Hj.
  assert (Hj13 : (j < length PF_SAVED)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  unfold PF_SAVED in Hj13. cbn [length] in Hj13.
  unfold EC. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite ew_Ereg_extra. unfold Ex2. apply nth_error_nth. rewrite nth_error_map, Hj. reflexivity. }
assert (EX : forall j (r : bv 5), nth_error PF_SAVED j = Some (bv_unsigned r) ->
  ew EC (32 + j)%nat = getr (p_regs v) r).
{ intros j r Hj. rewrite (EX0 j _ Hj), Z_to_bv_bv_unsigned. reflexivity. }
assert (EWC8 : ew EC 8 = w64 (pf_sp0 v)).
{ unfold EC. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_nat regs2 Ex2 8%nat 8%bv eq_refl). exact QB8. }
assert (UC8 : bv_unsigned (ew EC 8) = pf_sp0 v) by (rewrite EWC8; apply unsigned_lit_small; lia).
assert (HSC : st_ok_pi SEGS VAL EC ss_a4c
  (restrict (w_H Wc) (@mkst fx regs2 (Z_to_bv 64 (BASE + PF_RET4)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_a4c. apply pa_entry_st_ok_full.
  - unfold EC. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil].
    unfold a4_stk, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite UC8.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_forall. intros ck Hck. apply in_map_iff in Hck. destruct Hck as (j & <- & Hj).
    apply in_seq in Hj.
    destruct (nth_error PF_SAVED j) as [r|] eqn:Er;
      [|exfalso; apply nth_error_None in Er; unfold PF_SAVED in Er; cbn [length] in Er; lia].
    apply (chunk_ok_val SEGS EC _ _ _ 8%N _ (bv_unsigned (getr (p_regs v) (Z_to_bv 5 r)))).
    + cbn [sv_denot]. rewrite Z.add_0_r, !Z_to_bv_bv_unsigned. exact (EX0 j r Er).
    + change (8 * Z.of_N 8) with 64. apply u64_range.
    + lia.
    + replace (pf_sp0 v + (-8 - 8 * Z.of_nat j)) with (pf_sp0 v - 8 - 8 * Z.of_nat j) by lia.
      apply (val_mem_of_rdword SEGS (w_H Wc) mem2).
      rewrite (rdword_ext (rdW Wc memc) (rdW Wc mem2)); [exact (HSAV j r Er)|].
      intros kk Hkk. apply KEEP2; [lia|]. apply APART. right; left. lia.
  - cbn. split; exact I.
  - split; [cbn; exact I | split; exact I]. }
paj_run_sh RUNP HSC HJ2.
{ (* the save area is read-only: RUN C writes no byte *)
  intros a (r & Hr & Ha). unfold ss_a4c in Hr. cbn [ss_mem In] in Hr. destruct Hr as [<- | []].
  unfold a4_stk in Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. lia. }
(* ---------- the return ---------- *)
assert (KEEPF : forall a, 0 <= a < 2 ^ 64 -> ~ a4_Wr (pf_F v pos) (pf_SH v pos) (pf_s1 v) (pf_FL v pos) a ->
  rdW Wc (ms_mem ms0) a = rdW Wc memc a).
{ intros a Ha HW.
  rewrite (kept_of_frame (segs := SEGS) EC _ (w_H Wc) mem2 _ (fun _ : Z => False) HFr
    ltac:(intros b wlo whi x Hin Hrr; vm_compute in Hin;
          repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]);
          destruct Hin) a Ha ltac:(tauto)).
  exact (KEEP2 a Ha HW). }
assert (QC1 : getr (ms_regs ms0) 1%bv = getr (p_regs v) 1%bv).
{ a4_rreg HSC. rewrite a4_den_atom0. exact (EX 0%nat 1%bv eq_refl). }
assert (QC10 : getr (ms_regs ms0) 10 = w64 (Z.of_nat (length (rc_seg cf))))
  by (a4_rreg HSC; rewrite a4_den_atom0; unfold EC;
      rewrite Eimg_low by (unfold A_TEXT; lia);
      rewrite (ew_Ereg_nat regs2 Ex2 18%nat 18%bv eq_refl); exact QB18).
eapply (RET Wc _ _ _ _ _ HSC eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
unfold PF_POSTr. apply (apost_baseF_of_base SEGS). unfold apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ =>
  exists (p_ly v), (stack_free_state 5 pos Sc), r, m, d end.
split; [rewrite QC1; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
split; [apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ2|].
split.
{ apply aregs_preserved_eqs.
  all: a4_rreg HSC; rewrite a4_den_atom0.
  1: { unfold EC. rewrite Eimg_low by (unfold A_TEXT; lia).
       rewrite (ew_Ereg_nat regs2 Ex2 8%nat 8%bv eq_refl), QB8.
       unfold pf_sp0, spZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  1: { unfold EC. rewrite Eimg_low by (unfold A_TEXT; lia).
       rewrite (ew_Ereg_nat regs2 Ex2 3%nat 3%bv eq_refl).
       rewrite (HPres 3%bv ltac:(a4_cs)), QA3, <- Hgp. reflexivity. }
  1: { unfold EC. rewrite Eimg_low by (unfold A_TEXT; lia).
       rewrite (ew_Ereg_nat regs2 Ex2 4%nat 4%bv eq_refl).
       rewrite (HPres 4%bv ltac:(a4_cs)), QA4, <- Htp. reflexivity. }
  all: lazymatch goal with |- ew _ ?n = getr _ _ =>
         let j := eval compute in (n - 32)%nat in apply (EX j); reflexivity end. }
(* ---------- the post ---------- *)
assert (EAB : ablocks B (p_ly v) (stack_free_state 5 pos Sc) = ablocks B (p_ly v) Sc)
  by (unfold ablocks; rewrite blocks_stack_free_state; reflexivity).
split; [exact QC10|].
split.
{ destruct HRC as (bs & Hbs & Henc). exists bs. split; [|exact Henc].
  intros i Hi. rewrite KEEPF.
  - exact (Hbs i Hi).
  - destruct Henc as (Hlen & _). unfold seg_spec.SEG_C_SIZE in Hlen, Hbhi. lia.
  - apply APART. left. destruct Henc as (Hlen & _). unfold seg_spec.SEG_C_SIZE in Hlen |- *. lia. }
split; [rewrite EAB; exact HPERM|].
split; [reflexivity|].
destruct HSfs as (fS & ESc). rewrite ESc. unfold stack_free_state. eexists. reflexivity.
Qed.

End h.

Theorem pf_a4_holds : S_A4 B.
Proof. exact (fun f0 => @a4_done f0). Qed.

End g.
