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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 610 of its 655 lines of code are new or changed and 408 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): piece e (p5) of
   segment S14 of the walk of the test harness's entry function LLVMFuzzerTestOneInput (0x84dc0):
   the statement s22_p5_stmt of LLVMFuzzerTestOneInput_s22k.v, from the inner point S22_VM
   (0x85cd0, m_split of segment i succeeded) to the cut K85d04 i (0x85d04).

   proves function LLVMFuzzerTestOneInput (segment S14 piece only; reuse search, rule 24: released units, the earlier
   proof delivery and working heads; the result is recorded with the commissioning brief; none: written new)

   THE FORM: the image-A twin of this piece (image A's S14 walk (piece e), lib/A/Prog/LLVMFuzzerTestOneInput_s22e.v,
   sha256 bd7ec949b3bf, built rc=0 on image A's build VM), itself plugin-hostd/fuzz_command's lib/A/Prog/
   LLVMFuzzerTestOneInput_s42.v (origin/ossv/recipes 501c0d516c69): a run to the call of the runtime's memcpy entry,
   aj_intrin_atS, a seed afresh after the call, a run to the cut, and the cut applied to the run's last state; with
   image B's registers, slots and pcs. The code (dis/LLVMFuzzerTestOneInput.fuzz_segconf.asan-ubsan.s:966-978, the
   listing lib/B/Prog/SegList.v:1015-1027):
     0x85cd0 ld a0,64(s1)            a0 := v = FR + 32 (slot 64 of LT_LV)
     0x85cd4 mv a1,s3                a1 := &m->seg[i] (the name)
     0x85cd8 mv a2,s7                a2 := pn = di
     0x85cdc jal <__asan_memcpy>     PCall SS___asan_memcpy (SegList.v:1018): v[0 .. pn) := name[0 .. pn)
     0x85ce0 li a0,16
     0x85ce4 bgeu s7,a0,TRAP         pn >= 16: decided in the run (s7 = pn in [1, 15], the seed's atom fact)
     0x85ce8 ld a6,200(s1)           a6 := the shadow base (lt_frame's 200(s1))
     0x85cec ld a0,96(s1)            a0 := ~(FR + 32) (slot 96 of LT_LD)
     0x85cf0 bltu a0,s7,TRAP         ~(FR + 32) < pn: decided in the run (the seed's atom fact on ~(FR + 32))
     0x85cf4 ld a0,64(s1)            a0 := v
     0x85cf8 add s7,a0,s7            s7 := v + pn (the seed's alias)
     0x85cfc sb zero,0(s7)           v[pn] := 0
     0x85d00 sw s5,16(a0)            v.vid := vid (s5)
   No instrumented check lies in 0x85cd0 .. 0x85d00 (image B's store v.parent[pn] = 0 has none: the two UBSan traps
   guard it); both traps are decided inside the second run by the facts of its seed, so no trap edge is split. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0v YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YG0s YG0p.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
SegSyms SegList SegPa SegPaLib PaCall PaDenot PaSB PaLibF PaLibG PaLibH PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import LLVMFuzzerTestOneInput_c SegInstB
  LLVMFuzzerTestOneInput_inst LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s22k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ============================== readers that agree on a range (the image-A twin's) ============================== *)
Definition s22e_kept (rd rd' : reader) (a n : Z) : Prop := forall x, a <= x < a + n -> rd' x = rd x.
Lemma s22e_kept_bytes : forall rd rd' a bs, s22e_kept rd rd' a (Z.of_nat (length bs)) -> sa_bytes rd a bs -> sa_bytes rd' a bs.
Proof. intros rd rd' a bs HK H i Hi. rewrite HK by lia. exact (H i Hi). Qed.
Lemma s22e_kept_zs : forall rd rd' a l, s22e_kept rd rd' a (Z.of_nat (length l)) -> sa_zs rd a l -> sa_zs rd' a l.
Proof. intros rd rd' a l HK H i Hi. rewrite HK by lia. exact (H i Hi). Qed.
Lemma s22e_kept_val : forall rd rd' a n v, s22e_kept rd rd' a (Z.of_nat n) -> sa_val rd a n v -> sa_val rd' a n v.
Proof. intros rd rd' a n v HK H i Hi. rewrite HK by lia. exact (H i Hi). Qed.
Lemma s22e_kept_word : forall rd rd' a v, s22e_kept rd rd' a 8 -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof. intros rd rd' a v HK H. rewrite (rdword_ext rd rd' a); [exact H|]. intros k Hk. apply HK. lia. Qed.
Lemma s22e_kept_rconf : forall rd rd' c r, s22e_kept rd rd' c seg_spec.SEG_C_SIZE -> sa_rconf rd c r -> sa_rconf rd' c r.
Proof.
intros rd rd' c r HK (bs & Hb & He). exists bs. split; [|exact He].
apply (s22e_kept_bytes rd); [|exact Hb]. destruct He as (Hl & _). rewrite Hl. exact HK.
Qed.
Lemma s22e_kept_mconf : forall rd rd' m r, s22e_kept rd rd' m seg_spec.SEG_M_SIZE -> sa_mconf rd m r -> sa_mconf rd' m r.
Proof.
intros rd rd' m r HK (bs & Hb & He). exists bs. split; [|exact He].
apply (s22e_kept_bytes rd); [|exact Hb]. destruct He as (Hl & _). rewrite Hl. exact HK.
Qed.
Lemma s22e_kept_rtab : forall rd rd' a t, s22e_kept rd rd' a (18 * Z.of_nat (length t)) -> sa_rtab rd a t -> sa_rtab rd' a t.
Proof.
intros rd rd' a t HK (bs & Hb & He). exists bs. split; [|exact He].
apply (s22e_kept_bytes rd); [|exact Hb]. destruct He as (Hl & _). rewrite Hl. intros x Hx. apply HK. lia.
Qed.
Lemma s22e_kept_mtab : forall rd rd' a t, s22e_kept rd rd' a (20 * Z.of_nat (length t)) -> sa_mtab rd a t -> sa_mtab rd' a t.
Proof.
intros rd rd' a t HK (bs & Hb & He). exists bs. split; [|exact He].
apply (s22e_kept_bytes rd); [|exact Hb]. destruct He as (Hl & _). rewrite Hl. intros x Hx. apply HK. lia.
Qed.
Lemma s22e_kept_guard : forall rd rd' tab cap, s22e_kept rd rd' (tab + seg_spec.RVLAN_SIZE * cap) 18 ->
  sa_guardtab rd tab cap -> sa_guardtab rd' tab cap.
Proof. intros rd rd' tab cap HK H. apply (s22e_kept_bytes rd); [exact HK | exact H]. Qed.
(* a callee-saved register across a call *)
Lemma s22e_pres : forall regs regs' (r : bv 5) z,
  aregs_preserved regs regs' -> acallee_saved z -> Z_to_bv 5 z = r -> getr regs' r = getr regs r.
Proof. intros regs regs' r z HP Hz <-. exact (HP z Hz). Qed.
(* a byte the symbolic state holds as the chunk 0 *)
Lemma s22e_rd_zero : forall segs H (m : word -> option byte) a,
  val_mem segs (mrestrict H m) a 1 0 -> aview segs H m a = Some 0.
Proof.
intros segs H m a Hv. pose proof (Hv 0%nat ltac:(lia)) as H0. change (a + Z.of_nat 0) with (a + 0) in H0.
rewrite Z.add_0_r in H0. unfold aview. rewrite H0. reflexivity.
Qed.
(* the n bytes of a value the symbolic state holds as a chunk, as SegABase.sa_val *)
Lemma s22e_sa_val : forall segs H (m : word -> option byte) a n v,
  val_mem segs (mrestrict H m) a n v -> sa_val (aview segs H m) a n v.
Proof.
intros segs H m a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn [Z.of_N]. unfold le_byte.
pose proof (Z.mod_pos_bound (Z.shiftr (v mod 2 ^ (8 * Z.of_nat n)) (8 * Z.of_nat k)) 256 ltac:(lia)). lia.
Qed.

(* ============================== the frame's object v and its shadow ============================== *)
(* v = FR + 32 is usable for its 20 bytes when the frame's shadow bytes 4 .. 6 are 00 00 04 (lt_fsh LFO_NV) *)
Lemma s22e_v_addr : forall (rd : reader) F, F mod 8 = 0 -> sa_zs rd (shadow_addr F) (lt_fsh LFO_NV) ->
  range_addressable rd SHADOW_OFF (F + 32) 20.
Proof.
intros rd F HF HZ x Hx. unfold shadow_of_addr.
pose proof (HZ 4%nat ltac:(rewrite lt_fsh_len; lia)) as H4.
pose proof (HZ 5%nat ltac:(rewrite lt_fsh_len; lia)) as H5.
pose proof (HZ 6%nat ltac:(rewrite lt_fsh_len; lia)) as H6.
change (Z.of_nat 4) with 4 in H4. change (Z.of_nat 5) with 5 in H5. change (Z.of_nat 6) with 6 in H6.
change (nth 4 (lt_fsh LFO_NV) 0) with 0 in H4. change (nth 5 (lt_fsh LFO_NV) 0) with 0 in H5.
change (nth 6 (lt_fsh LFO_NV) 0) with 4 in H6.
unfold shadow_addr in H4, H5, H6.
destruct (Z_lt_le_dec x (F + 40)) as [Hl1|Hl1]; [|destruct (Z_lt_le_dec x (F + 48)) as [Hl2|Hl2]].
- exists 0. split; [|left; reflexivity]. replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + F / 8 + 4) by lia. exact H4.
- exists 0. split; [|left; reflexivity]. replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + F / 8 + 5) by lia. exact H5.
- exists 4. split; [replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + F / 8 + 6) by lia; exact H6|].
  right. lia.
Qed.
(* the shadow hull of v's first n <= 16 bytes is the frame's shadow word 0 *)
Lemma s22e_hull_v : forall (rd : reader) F n, F mod 64 = 0 -> 0 <= F -> 0 < n <= 16 ->
  (forall j, 0 <= j < 8 -> rd (shadow_addr F + j) <> None) -> shadow_hull_vis rd (F + 32) n.
Proof.
intros rd F n HF HF0 Hn Hv s Hs.
assert (Hs' : shadow_addr F <= s < shadow_addr F + 8) by (unfold shadow_addr, SHADOW_OFF in *; lia).
replace s with (shadow_addr F + (s - shadow_addr F)) by lia. apply Hv. lia.
Qed.

Ltac s22e_in := cbn [In]; repeat (first [left; reflexivity | right]).

(* ============================== the two symbolic states ============================== *)
(* 1, at 0x85cd0 (S22_VM): every register its own atom, atom 32 = v = FR + 32; the slot 64(s1) (s1 = atom 9) read
   only *)
Definition s22e_r1 : YP09.region := YP09.mkRegion (Some 9%nat) 64 72 0 0 [YP09.mkChunk 64 (CVal 8 (SOff 32 0))].
Definition ss_s22e1 : sstate := mkSS S22_VM sr_atoms [s22e_r1] None (mkFacts [] [] []).
(* 2, at 0x85ce0, seated afresh after the call: atom 32 = v, 33 = ~v (the word of 96(s1)), 34 = the shadow base (the
   word of 200(s1)), 35 = v + pn (the alias of add s7,a0,s7); s7 = pn (atom 23) in [1, 15] and ~v at or above
   2 ^ 63 decide the two UBSan tests; the word v + 16 and the byte v + pn are write windows *)
Definition s22e_r2s : YP09.region := YP09.mkRegion (Some 9%nat) 64 208 0 0
  [YP09.mkChunk 64 (CVal 8 (SOff 32 0)); YP09.mkChunk 96 (CVal 8 (SOff 33 0)); YP09.mkChunk 200 (CVal 8 (SOff 34 0))].
Definition s22e_r2v : YP09.region := YP09.mkRegion (Some 32%nat) 16 20 16 20 [].
Definition s22e_r2p : YP09.region := YP09.mkRegion (Some 35%nat) 0 1 0 1 [].
Definition s22e_facts2 : facts :=
  mkFacts [(23%nat, mkAF 1 15 0); (33%nat, mkAF (2 ^ 63) (2 ^ 64 - 1) 0)] []
    [(SAlu ALU_ADD (SOff 32 0) (SOff 23 0), SOff 35 0)].
Definition ss_s22e2 : sstate := mkSS 0xf20 sr_atoms [s22e_r2s; s22e_r2v; s22e_r2p] None s22e_facts2.
(* the token runner's shadow base (a6) and band; the first run crosses no instrumented check *)
Definition s22e_Bx : sv := SOff 16 0.
Definition s22e_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the offsets of the loop's slots LT_LV ++ LT_LD (all in [16, 216]: above s1, below the saved registers) *)
Lemma s22e_L_offs : forall cx c m tab mt i o v, In (o, v) (LT_LV cx c m ++ LT_LD cx m tab mt i) -> 16 <= o <= 216.
Proof.
intros cx c m tab mt i o v H. unfold LT_LV, LT_LD in H. cbn [app In] in H.
repeat (destruct H as [H|H]; [injection H as <- _; lia|]). destruct H.
Qed.
Definition s22e_E1 (regs : bvmap 5 word) (v : Z) : env := Eimg (Ereg regs [Z_to_bv 64 v]).
Definition s22e_E2 (regs : bvmap 5 word) (v pn : Z) : env :=
  Eimg (Ereg regs [Z_to_bv 64 v; Z_to_bv 64 (lt_not v); Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 (v + pn)]).

Lemma s22e_seed1 : forall (W : world SEGS) regs mem s1 v,
  getr regs 9 = w64 s1 -> 0 <= s1 -> s1 + 72 <= 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  rdword (rdW W mem) (s1 + 64) = Some v ->
  st_ok_pi SEGS VAL (s22e_E1 regs v) ss_s22e1
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + S22_VM)) mem (seg_rom SEGS))).
Proof.
intros W regs mem s1 v R9 Hs0 Hs1 Hv Hw64.
assert (U9 : bv_unsigned (ew (s22e_E1 regs v) 9) = s1).
{ unfold s22e_E1. rewrite (ew_Eimg_Ereg_nat regs _ 9 9%bv eq_refl), R9. apply unsigned_lit_small. lia. }
assert (E32 : ew (s22e_E1 regs v) 32 = Z_to_bv 64 v).
{ unfold s22e_E1. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). }
unfold ss_s22e1. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold s22e_E1. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok, s22e_r1.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U9.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS _ _ s1 64 8 (SOff 32 0) v);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
  exact (val_mem_of_rdword SEGS (w_H W) mem _ v Hw64).
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [exact I | split; [exact I | exact I]].
Qed.

Lemma s22e_seed2 : forall (W : world SEGS) regs mem s1 v pn,
  getr regs 9 = w64 s1 -> getr regs 23 = w64 pn ->
  0 <= s1 -> s1 + 208 <= 2 ^ 64 -> 4096 <= v -> v + 20 <= s1 + 64 -> v + 20 <= 2 ^ 63 -> 1 <= pn <= 15 ->
  rdword (rdW W mem) (s1 + 64) = Some v -> rdword (rdW W mem) (s1 + 96) = Some (lt_not v) ->
  rdword (rdW W mem) (s1 + 200) = Some SHADOW_OFF ->
  writable_at SEGS (mrestrict (w_H W) mem) (v + pn) ->
  (forall o, 16 <= o < 20 -> writable_at SEGS (mrestrict (w_H W) mem) (v + o)) ->
  st_ok_pi SEGS VAL (s22e_E2 regs v pn) ss_s22e2
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0xf20)) mem (seg_rom SEGS))).
Proof.
intros W regs mem s1 v pn R9 R23 Hs0 Hs1 Hv0 Hvs Hv1 Hpn Hw64 Hw96 Hw200 Hwp Hw16.
set (E := s22e_E2 regs v pn).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hr; subst E; unfold s22e_E2; apply ew_Eimg_Ereg_nat; exact Hr).
assert (EX : forall j, (j < 4)%nat -> ew E (32 + j) =
  nth j [Z_to_bv 64 v; Z_to_bv 64 (lt_not v); Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 (v + pn)] (Z_to_bv 64 0))
  by (intros j Hj; subst E; unfold s22e_E2; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
cbn [Nat.add nth] in E32, E33, E34, E35. clear EX.
assert (U9 : bv_unsigned (ew E 9) = s1) by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = pn) by (rewrite (EE 23%nat 23%bv eq_refl), R23; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = v) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = lt_not v) by (rewrite E33; apply unsigned_lit_small; unfold lt_not; lia).
assert (U35 : bv_unsigned (ew E 35) = v + pn) by (rewrite E35; apply unsigned_lit_small; lia).
unfold ss_s22e2. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E. unfold s22e_E2. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  + unfold region_ok, s22e_r2s. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
    * apply (chunk_ok_val SEGS _ _ s1 64 8 (SOff 32 0) v);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Hw64).
    * apply (chunk_ok_val SEGS _ _ s1 96 8 (SOff 33 0) (lt_not v));
        [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold lt_not; cbn; lia | cbn; lia |].
      exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Hw96).
    * apply (chunk_ok_val SEGS _ _ s1 200 8 (SOff 34 0) SHADOW_OFF);
        [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SHADOW_OFF; cbn; lia
        | cbn; lia |].
      exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Hw200).
  + unfold region_ok, s22e_r2v. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U32. split; [lia|]. split; [lia|]. split; [exact Hw16 | apply Forall_nil].
  + unfold region_ok, s22e_r2p. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U35. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. replace (v + pn + o) with (v + pn) by lia. exact Hwp.
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, s22e_r2s, s22e_r2v, s22e_r2p.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32, U35.
  repeat split; lia.
- split; [|split; [exact I|]].
  + cbn [s22e_facts2 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U23, U33. change (2 ^ 0) with 1. rewrite !Z.mod_1_r. unfold lt_not.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
  + cbn [s22e_facts2 f_alias alias_ok]. split; [|exact I].
    apply U_inj. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U32, U23, U35, !Z.add_0_r.
    rewrite (zcanon_small v) by lia. rewrite (zcanon_small pn) by lia. reflexivity.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
(* the allocator record's laws (a theorem of image B's kit: lib/B/YG0q.v AR_laws_ok) *)
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* the runtime's memcpy entry, at every FP state (BRIEF.md's text, word for word) *)
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (pa_sigma SS___asan_memcpy).
Let RUN := paj_run B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ (PI := PI) B LAWS.

(* the numbers of the entry's frame at a point of the walk (image B: the 352-byte frame, s1 = (SP0 - 352) & ~31) *)
Lemma s22e_layout : forall cx ly S (W : world SEGS) regs mem md k o,
  lt_base B MT cx -> lt_frame B cx ly S W regs mem md k o ->
  x_sp0 cx mod 16 = 0 /\ alloc_ceiling + 32768 <= x_sp0 cx <= 2 ^ 47 /\
  x_s1 cx mod 32 = 0 /\ x_sp0 cx - 384 < x_s1 cx <= x_sp0 cx - 352 /\ spZ regs = x_s1 cx /\
  frames S = [(LT_FCLS, x_fpos cx)] /\ frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx /\
  x_fr cx mod 64 = 0 /\ 4096 <= x_fr cx /\ x_fr cx + 512 <= alloc_ceiling /\ in_app (x_fr cx) 512 /\
  fs_frame_bytes LT_FCLS = 512 /\ off_img (x_fr cx) 512.
Proof.
intros cx ly S W regs mem md k o HB HF.
pose proof HB as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hfr0 & _).
pose proof HPRE as (_ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof HF as (HJ & R2 & _).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
assert (EB : fs_frame_bytes LT_FCLS = 512) by reflexivity.
assert (Hs1 : x_s1 cx mod 32 = 0 /\ x_sp0 cx - 384 < x_s1 cx <= x_sp0 cx - 352).
{ unfold x_s1, LT_FRAME. pose proof (Z.mod_pos_bound (x_sp0 cx - 352) 32 ltac:(lia)).
  split; [|lia]. rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity. }
assert (HSP : alloc_ceiling + 32768 <= x_sp0 cx <= 2 ^ 47).
{ unfold x_sp0. unfold STK_LLVMFuzzerTestOneInput in Hslo. lia. }
assert (HFS : frames S = [(LT_FCLS, x_fpos cx)]) by (rewrite Hfrs, Hfr0; reflexivity).
assert (HFA : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx).
{ unfold x_fr, frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
assert (Hin : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite HFS; left; reflexivity).
destruct (frames_bounds _ _ LAWS ly S W mem md _ _ HAR Hin) as (F1 & F2 & F3).
destruct (frame_al64 _ _ ly S W mem md _ _ HAR Hin) as (F4 & _).
pose proof (frm_off_imgP B ly S W mem md _ _ HAR Hin) as F5.
rewrite HFA, EB in *.
split; [exact Hal16|]. split; [exact HSP|]. split; [exact (proj1 Hs1)|]. split; [exact (proj2 Hs1)|].
split; [unfold spZ; rewrite R2; apply unsigned_lit_small; pose proof asan_consts as (C1 & _); lia|].
split; [exact HFS|]. split; [reflexivity|]. split; [exact F4|]. split; [exact F1|]. split; [exact F2|].
split; [exact F3|]. split; [reflexivity | exact F5].
Qed.

(* a harness block at a later state of the same blocks: its shadow is AR's there *)
Lemma s22e_hblk_kept : forall ly S (rd : reader) ly2 S2 (W2 : world SEGS) mem2 md2 a n,
  AR SEGS B ly2 S2 W2 mem2 md2 -> lt_hblk B ly S rd a n -> In (a, n) (ablocks B ly2 S2) ->
  lt_hblk B ly2 S2 (rdW W2 mem2) a n.
Proof.
intros ly S rd ly2 S2 W2 mem2 md2 a n HAR2 (_ & H4096 & H16 & (Ha0 & Ha63 & Hamem & _)) Hin2.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 Hin2) as (_ & _ & _ & _ & _ & _ & Hn).
destruct (al_shadow _ _ LAWS _ _ _ _ _ _ _ HAR2 Hin2) as [_ Hhull].
split; [exact Hin2|]. split; [exact H4096|]. split; [exact H16|].
split; [exact Ha0|]. split; [exact Ha63|]. split; [exact Hamem|].
destruct (Z.eq_dec n 0) as [->|Hn0].
- split; [intros x Hx; lia | intros Hx; lia].
- assert (Hr : req_size n = n) by (unfold req_size; destruct (Z.eqb_spec n 0); lia).
  split.
  + apply (range_addressable_of_block SEGS B LAWS ly2 S2 W2 mem2 md2 a n a n HAR2 Hin2); lia.
  + intros _. rewrite <- Hr. exact Hhull.
Qed.

(* the frame part of a point carried to a state that keeps its bytes (image B's lt_frame: 200(s1) the shadow base,
   184(s1) SH(FR)) *)
Lemma s22e_frame_kept : forall cx ly S (W : world SEGS) regs mem md k o regs' mem' md',
  lt_frame B cx ly S W regs mem md k o ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  s22e_kept (rdW W mem) (rdW W mem') (x_sp0 cx - 104) 104 ->
  s22e_kept (rdW W mem) (rdW W mem') (x_fr cx) 24 -> s22e_kept (rdW W mem) (rdW W mem') (x_fr cx + LT_FLAGW) 8 ->
  s22e_kept (rdW W mem) (rdW W mem') (x_s1 cx + 184) 24 -> s22e_kept (rdW W mem) (rdW W mem') (x_sh cx) 36 ->
  lt_frame B cx ly S W regs' mem' md' k o.
Proof.
intros cx ly S W regs mem md k o regs' mem' md' HF HJ' E2 E3 E4 E8 E9 KS KH KW K184 KZ.
destruct HF as (_ & R2 & R3 & R4 & R8 & R9 & HSV & H0 & H8 & H16 & HW & H200 & HZS & H184).
split; [exact HJ'|]. rewrite E2, E3, E4, E8, E9.
split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
split.
{ intros i r Hi. pose proof (HSV i r Hi) as H. apply (s22e_kept_word (rdW W mem)); [|exact H].
  assert (Hi13 : (i < length LT_SAVED)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
  cbn [LT_SAVED length] in Hi13. intros x Hx. apply KS. lia. }
split; [apply (s22e_kept_word (rdW W mem)); [intros x Hx; apply KH; lia | exact H0]|].
split; [apply (s22e_kept_word (rdW W mem)); [intros x Hx; apply KH; lia | exact H8]|].
split; [apply (s22e_kept_word (rdW W mem)); [intros x Hx; apply KH; lia | exact H16]|].
split; [apply (s22e_kept_word (rdW W mem)); [exact KW | exact HW]|].
split; [apply (s22e_kept_word (rdW W mem)); [intros x Hx; apply K184; lia | exact H200]|].
split; [apply (s22e_kept_zs (rdW W mem)); [rewrite lt_fsh_len; exact KZ | exact HZS]|].
apply (s22e_kept_word (rdW W mem)); [intros x Hx; apply K184; lia | exact H184].
Qed.

(* lt_img reads only bytes of the image's span [0x10000, kImgEnd) (pa_img_range for every in_img byte; the RELRO
   window, the .got word, the guard and longl are numbers inside it): a reader that keeps that span keeps lt_img (the
   form of the S09 walk's s18_lt_img_kept, with the span in place of the image facts) *)
Lemma s22e_img_kept : forall cx (W' : world SEGS) mem' (rd : reader),
  (forall a, 0x10000 <= a < kImgEnd -> rdW W' mem' a = rd a) ->
  lt_img B cx rd -> lt_img B cx (rdW W' mem').
Proof.
intros cx W' mem' rd K0 (HRO & HIM & HGI).
assert (K : forall a, in_img SEGS a -> rdW W' mem' a = rd a) by (intros a Ha; apply K0; exact (pa_img_range a Ha)).
assert (KI : forall q n, sa_img SEGS B q n -> forall a, q <= a < q + n -> rdW W' mem' a = rd a).
{ intros q n0 Hq a Ha. destruct (Hq a Ha) as (H1 & _ & _). exact (K a H1). }
assert (KW : forall q n a, sa_img SEGS B q n -> q <= a -> a + 8 <= q + n -> rdword (rdW W' mem') a = rdword rd a).
{ intros q n0 a Hq H1 H2. apply rdword_ext. intros k Hk. apply (KI q n0 Hq). lia. }
assert (KL : forall a s, sa_lit SEGS B rd a s -> sa_lit SEGS B (rdW W' mem') a s).
{ intros a s (Ha & ((Hz & Hn0) & _) & Hp & Hr & Hi). split; [exact Ha|]. split; [split; [split|]|].
  - intros i Hix. rewrite length_app in Hix. cbn [length] in Hix.
    rewrite (KI _ _ Hi); [exact (Hz i ltac:(rewrite length_app; cbn [length]; lia))|]. lia.
  - exact Hn0.
  - exact (sa_tail_of_romtail SEGS (w_H W') mem' _ Hr).
  - split; [exact Hp|]. split; [exact Hr | exact Hi]. }
destruct HIM as (Hm40 & Hm40i & HLF & HLR & (Hcp & Hci & Hcr) & HCa & (Hwp & Hwi & Hwr) & (Hrp & Hri & Hrr) & (Hg1 & Hg2)
  & HLP & HLT & HLI & HD1 & HD2 & HD3).
split; [|split].
- intros a Hro Ho He. rewrite <- (HRO a Hro Ho He). apply K0.
  destruct Hro as [(s & Hs & _ & Hr) | Hr].
  + apply pa_img_range. exists s. split; [exact Hs | exact Hr].
  + unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI in Hr. unfold kImgEnd. lia.
- split; [|split; [exact Hm40i|]].
  { intros k Hk. rewrite (KI _ _ Hm40i); [exact (Hm40 k Hk) | lia]. }
  split; [intros s Hs; destruct (HLF s Hs) as [Hl Ha]; exact (conj (KL _ _ Hl) Ha)|].
  split; [intros s Hs; destruct (HLR s Hs) as [Hl Ha]; exact (conj (KL _ _ Hl) Ha)|].
  split.
  { split; [exact Hcp|]. split; [exact Hci|]. intros i Hi. destruct (Hcr i Hi) as (tp & Htp & Hl).
    exists tp. split; [|exact (KL _ _ Hl)]. rewrite (KW _ _ _ Hci); [exact Htp | |];
    unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES, pin_spec.CAT_N in *; lia. }
  split; [exact HCa|].
  split.
  { split; [exact Hwp|]. split; [exact Hwi|]. intros i Hi. destruct (Hwr i Hi) as (wp & Hwp' & Hl).
    exists wp. split; [|exact (KL _ _ Hl)]. rewrite (KW _ _ _ Hwi); [exact Hwp' | lia | lia]. }
  split.
  { split; [exact Hrp|]. split; [exact Hri|]. intros i Hi k Hk. rewrite (KI _ _ Hri); [exact (Hrr i Hi k Hk) | lia]. }
  split.
  { split.
    - rewrite <- Hg1. apply rdword_ext. intros k Hk. apply K0. unfold gotwA, kImgEnd. lia.
    - destruct Hg2 as (g & Hg). exists g. rewrite <- Hg. apply rdword_ext. intros k Hk. apply K0.
      unfold guardA, kImgEnd. lia. }
  split; [exact HLP|]. split; [exact HLT|]. split; [exact HLI|]. split; [exact HD1|]. split; [exact HD2 | exact HD3].
- intros i Hi. rewrite K0; [exact (HGI i Hi)|]. unfold longlA, A_LONGL, LONGL_W, kImgEnd. lia.
Qed.

(* ============================== piece e: S22_VM -> K85d04 ============================== *)
Lemma s22_p5 : s22_p5_stmt B MT.
Proof.
intros i HK. unfold S22_VM_stmt.
intros cx ly S W regs mem md k acc c m tab mt di vid HB0 HFRM HINV Hign Hsplit Hdi Hvid R19 R21 R23 R24 HRK.
pose proof HINV as (Hi & Hdecl & HCORE & HHc & HHm & HHt & HHmt & HSL & HCM & HTABS).
pose proof HCORE as (HFR & HIMG & HBLK & HBUD).
pose proof HFR as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFW & H200 & HZS & H184).
destruct HRK as (R20 & R22 & R26 & R27).
pose proof HB0 as (HPRE & _). pose proof HPRE as (_ & _ & _ & Hgp0 & Htp0 & _).
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (s22e_layout cx ly S W regs mem md k LFO_NV HB0 HFR)
  as (Lsp16 & Lsp & Ls132 & Ls1 & Lspz & Lfrs & Lfa & LF64 & LF4096 & LFceil & LFapp & LFB & LFimg).
assert (HFin : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Lfrs; left; reflexivity).
pose proof (proj1 HJ) as HAR0.
(* the numbers: the frame's placement, its 64-alignment, the shadow address, the parent's length *)
assert (LFlh : x_fr cx + 512 <= 2147446784 \/ 17594333495296 <= x_fr cx).
{ destruct LFapp as [_ [H|[H _]]]; [left; unfold kLowShadowBeg in H; lia | right; rewrite C3 in H; lia]. }
assert (LFoi : x_fr cx + 512 <= 65536 \/ 6299648 <= x_fr cx) by (unfold off_img in LFimg; lia).
assert (HFq : x_fr cx = 64 * (x_fr cx / 64)) by (pose proof (Z.div_mod (x_fr cx) 64 ltac:(lia)); lia).
assert (HF8 : x_fr cx mod 8 = 0)
  by (rewrite HFq; rewrite Z.mul_comm; replace (x_fr cx / 64 * 64) with ((x_fr cx / 64 * 8) * 8) by lia; apply Z_mod_mult).
assert (Hsh : x_sh cx = SHADOW_OFF + 8 * (x_fr cx / 64)).
{ unfold x_sh, shadow_addr. f_equal. rewrite HFq at 1. replace (64 * (x_fr cx / 64)) with ((8 * (x_fr cx / 64)) * 8) by lia.
  apply Z.div_mul. lia. }
remember (x_fr cx / 64) as qF eqn:HqF. clear HqF.
assert (Ho16 : (x_s1 cx - x_sp0 cx) mod 16 = 0).
{ pose proof (Z.div_mod (x_s1 cx) 32 ltac:(lia)) as D1. rewrite Ls132 in D1.
  pose proof (Z.div_mod (x_sp0 cx) 16 ltac:(lia)) as D2. rewrite Lsp16 in D2.
  replace (x_s1 cx - x_sp0 cx) with ((2 * (x_s1 cx / 32) - x_sp0 cx / 16) * 16) by lia. apply Z_mod_mult. }
clear Ls132 Lsp16.
destruct (s22_name_str cx i c m (rdW W mem) HCM Hi) as ((HNZ & HN0) & HNL & HNF).
assert (Hi32 : (i < 32)%nat).
{ pose proof HCM as [_ Hm']. unfold sa_mconf, sa_mconfp in Hm'. destruct Hm' as (bs & _ & Henc).
  destruct Henc as (_ & Hle & _). unfold x_mcF in Hi. lia. }
assert (Hdi16 : 0 < Z.of_nat di < 16) by lia.
(* the four blocks *)
pose proof HHc as (HcIn & Hc4096 & _). pose proof HHm as (HmIn & Hm4096 & _).
pose proof HHt as (HtIn & Ht4096 & _). pose proof HHmt as (HmtIn & Hmt4096 & _).
destruct (al_blocks _ _ LAWS ly S W mem md m seg_spec.SEG_M_SIZE HAR0 HmIn) as (_ & _ & Hmceil & _ & _ & _ & _).
destruct (al_blocks _ _ LAWS ly S W mem md tab (x_tabn cx) HAR0 HtIn) as (_ & _ & Htceil & _ & _ & _ & Htn).
change (req_size seg_spec.SEG_M_SIZE) with seg_spec.SEG_M_SIZE in Hmceil.
pose proof (req_size_pos (x_tabn cx) ltac:(lia)) as [Rt1 Rt2].
assert (HNb : seg_spec.mseg_addr m i + 16 <= m + seg_spec.SEG_M_SIZE)
  by (unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE, seg_spec.SEG_M_SIZE; lia).
assert (HNa : m <= seg_spec.mseg_addr m i) by (unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE; lia).
pose proof (sep_block_frame SEGS B LAWS ly S W mem md m seg_spec.SEG_M_SIZE LT_FCLS (x_fpos cx) HAR0 HmIn HFin) as HdmF.
unfold zdisjoint in HdmF. cbn [fst snd] in HdmF. rewrite Lfa, LFB in HdmF.
change (req_size seg_spec.SEG_M_SIZE) with seg_spec.SEG_M_SIZE in HdmF.
(* every block lies apart from the frame and below the stack *)
assert (KBLK0 : forall b n, In (b, n) (ablocks B ly S) -> forall x, b <= x < b + n ->
  0 <= x < 2 ^ 64 /\ x < alloc_ceiling /\ ~ (x_fr cx <= x < x_fr cx + 512)).
{ intros b n Hin x Hx.
  destruct (al_blocks _ _ LAWS ly S W mem md b n HAR0 Hin) as (_ & Hb4096 & Hbceil & _ & _ & _ & Hn).
  pose proof (req_size_pos n ltac:(lia)) as [_ Hrq].
  pose proof (sep_block_frame SEGS B LAWS ly S W mem md b n LT_FCLS (x_fpos cx) HAR0 Hin HFin) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Lfa, LFB in Hd. lia. }

(* ---- 0x85cd0 .. 0x85cdc: a0 := 64(s1) = v, a1 := s3 = the name, a2 := s7 = pn, the jal of memcpy ---- *)
assert (Hv64 : rdword (rdW W mem) (x_s1 cx + 64) = Some (x_fr cx + FO_V)).
{ apply HSL. apply in_or_app. left. unfold LT_LV. s22e_in. }
pose proof (s22e_seed1 W regs mem (x_s1 cx) (x_fr cx + FO_V) R9 ltac:(lia) ltac:(lia) ltac:(unfold FO_V; lia) Hv64) as HS.
assert (HEI : img_env VAL A_LIM (s22e_E1 regs (x_fr cx + FO_V))) by (unfold s22e_E1; apply Eimg_env).
assert (HAEA : env_agree 32 (Ereg regs [Z_to_bv 64 (x_fr cx + FO_V)]) (s22e_E1 regs (x_fr cx + FO_V))).
{ split; [intros n Hn; unfold s22e_E1; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. }
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (s22e_E1 regs (x_fr cx + FO_V)) n = getr regs r)
  by (intros n r Hr; unfold s22e_E1; apply ew_Eimg_Ereg_nat; exact Hr).
assert (E32 : ew (s22e_E1 regs (x_fr cx + FO_V)) 32 = Z_to_bv 64 (x_fr cx + FO_V))
  by (unfold s22e_E1; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (SHOK : sh_ok SEGS s22e_Bx [] (s22e_E1 regs (x_fr cx + FO_V)) (mrestrict (w_H W) mem))
  by (unfold sh_ok; apply Forall_nil).
unfold cfg_at. change (w64 (BASE + S22_VM)) with (Z_to_bv 64 (BASE + S22_VM)).
paj_run_tok RUN HS HJ SHOK s22e_span.
{ awr_ok_tac. }
rename HF into HFA, HFr into HFrA, HG into HGA.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mm) _ => set (md1 := mm) in *; clearbody md1 end.
lazymatch type of HS with context [restrict _ ?m1] => rename m1 into msA end.
(* the run wrote nothing *)
assert (KA : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem msA) a = rdW W mem a).
{ intros a Ha.
  apply (kept_of_frame (s22e_E1 regs (x_fr cx + FO_V)) _ (w_H W) mem _ (fun _ => False) HFrA);
    [| exact Ha | exact (fun H => H)].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In _ (windows ?rs) => let w := eval vm_compute in (windows rs) in change (In (b, wlo, whi) w) in Hin end.
  cbn [In] in Hin. destruct Hin as [Hq | []]. injection Hq as <- <- <-. exfalso. lia. }
pose proof (proj1 HJ) as HARA.
(* the registers at the jal *)
pmkst HS.
pose proof (regs_kept_of_st_ok SEGS _ _ _ regs [Z_to_bv 64 (x_fr cx + FO_V)]
  [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS HAEA ltac:(vm_compute; reflexivity)) as PA.
cbn [ms_regs restrict] in PA.
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
assert (P10' : getr (ms_regs msA) 10 = w64 (x_fr cx + FO_V)) by (rewrite P10; exact E32).
assert (P11' : getr (ms_regs msA) 11 = w64 (seg_spec.mseg_addr m i)) by (rewrite P11, (EE 19%nat 19%bv eq_refl); exact R19).
assert (P12' : getr (ms_regs msA) 12 = w64 (Z.of_nat di)) by (rewrite P12, (EE 23%nat 23%bv eq_refl); exact R23).
assert (P3' : getr (ms_regs msA) 3 = w64 (as_gp B)) by (rewrite (PA 3%bv ltac:(s22e_in)), R3; exact Hgp0).
assert (P4' : getr (ms_regs msA) 4 = w64 (as_tp B)) by (rewrite (PA 4%bv ltac:(s22e_in)), R4; exact Htp0).
assert (HspT : spZ (ms_regs msA) = x_sp0 cx + (x_s1 cx - x_sp0 cx)).
{ unfold spZ at 1. rewrite (PA 2%bv ltac:(s22e_in)). change (bv_unsigned (getr regs 2)) with (spZ regs). rewrite Lspz. lia. }
assert (HraT : YK0s.ret_ok (Z_to_bv 64 (BASE + 0xf20))) by (apply ret_ok_codeptr_v; [lia | reflexivity]).
(* the frame and the name at the jal *)
destruct (al_frames _ _ LAWS ly S W (ms_mem msA) md1 LT_FCLS (x_fpos cx) HARA HFin) as (_ & _ & _ & HFSpresA).
rewrite Lfa, LFB in HFSpresA. change (512 / 8) with 64 in HFSpresA.
destruct (al_blocks _ _ LAWS ly S W (ms_mem msA) md1 m seg_spec.SEG_M_SIZE HARA HmIn) as (_ & _ & _ & _ & HmpresA & _ & _).
change (req_size seg_spec.SEG_M_SIZE) with seg_spec.SEG_M_SIZE in HmpresA.
assert (ZSA : sa_zs (rdW W (ms_mem msA)) (shadow_addr (x_fr cx)) (lt_fsh LFO_NV)).
{ apply (s22e_kept_zs (rdW W mem)); [|exact HZS]. rewrite lt_fsh_len. intros x Hx. change (Z.of_nat 36) with 36 in Hx.
  fold (x_sh cx) in Hx. rewrite Hsh in Hx. apply KA; unfold SHADOW_OFF in *; lia. }
assert (RAA : range_addressable (rdW W (ms_mem msA)) SHADOW_OFF (x_fr cx + 32) 20) by exact (s22e_v_addr _ _ HF8 ZSA).
(* ---- the memcpy of the parent: v[0 .. pn) := name[0 .. pn) ---- *)
eapply SRr_bind.
{ apply (aj_intrin_atS SEGS B LAWS pa_segs_low OCpy (pa_sigma SS___asan_memcpy) (AMEMCPY fx) W (ms_regs msA) (ms_mem msA)
    STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx)
    [(LT_FCLS, x_fpos cx)] ly S md1 k (x_fr cx + FO_V) (seg_spec.mseg_addr m i) (Z.of_nat di) (x_s1 cx - x_sp0 cx)
    (Z_to_bv 64 (BASE + 0xf20)) HJ P10' P11' P12' ltac:(lia) ltac:(unfold FO_V; lia) ltac:(unfold FO_V; lia) HspT Ho16
    ltac:(lia) ltac:(change ESTACK with 4096; rewrite HSTK; lia) P3' P4' P1 HraT).
  - intros a Ha. split.
    + right; right; right; left. exists LT_FCLS, (x_fpos cx). split; [left; reflexivity|].
      left. rewrite Lfa, LFB. unfold in_zr. cbn [fst snd]. unfold FO_V in Ha. lia.
    + change ESTACK with 4096. unfold FO_V in Ha. lia.
  - intros a Ha _ [[_ Himg] | Hst]; exfalso.
    + pose proof (pa_img_range _ Himg) as HIR. unfold kImgEnd in HIR. unfold FO_V in Ha. lia.
    + unfold FO_V in Ha. lia.
  - unfold amem_range. unfold FO_V. lia.
  - apply (range_addressable_sub _ _ (x_fr cx + 32) 20); [exact RAA | unfold FO_V; lia | unfold FO_V; lia].
  - intros _. unfold FO_V. apply (s22e_hull_v _ (x_fr cx) (Z.of_nat di) LF64 ltac:(lia) ltac:(lia)).
    intros j Hj. apply (aview_some_of_apresent SEGS). exact (proj1 (HFSpresA j ltac:(lia))).
  - split; [lia|]. split; [lia|]. split.
    { intros a Ha. split.
      - apply (aview_some_of_apresent SEGS). exact (proj1 (HmpresA a ltac:(lia))).
      - rewrite HspT. change ESTACK with 4096. lia. }
    split; [unfold FO_V; lia|].
    split; [exact (amem_range_of_block SEGS B LAWS ly S W (ms_mem msA) md1 m seg_spec.SEG_M_SIZE (seg_spec.mseg_addr m i)
              (Z.of_nat di) HARA HmIn HNa ltac:(change (req_size seg_spec.SEG_M_SIZE) with seg_spec.SEG_M_SIZE; lia))|].
    split; [exact (range_addressable_of_block SEGS B LAWS ly S W (ms_mem msA) md1 m seg_spec.SEG_M_SIZE
              (seg_spec.mseg_addr m i) (Z.of_nat di) HARA HmIn HNa
              ltac:(change (req_size seg_spec.SEG_M_SIZE) with seg_spec.SEG_M_SIZE; lia))|].
    intros Hpos. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W (ms_mem msA) md1 m seg_spec.SEG_M_SIZE
      (seg_spec.mseg_addr m i) (Z.of_nat di) HARA HmIn HNa
      ltac:(change (req_size seg_spec.SEG_M_SIZE) with seg_spec.SEG_M_SIZE; lia) Hpos). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & H10b & HCPY & HKC & HPRS & HSAME).
clear HS SHOK.
(* back at 0x85ce0: the callee-saved registers, and the bytes kept outside v[0 .. pn) and the window below s1 *)
assert (Q : forall (r : bv 5) z, acallee_saved z -> Z_to_bv 5 z = r ->
  In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs2 r = getr regs r).
{ intros r z Hz Hr Hin. rewrite (s22e_pres _ _ r z HP2 Hz Hr). exact (PA r Hin). }
assert (Q9 : getr regs2 9 = w64 (x_s1 cx))
  by (rewrite (Q 9%bv 9 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity) ltac:(s22e_in)); exact R9).
assert (Q23 : getr regs2 23 = w64 (Z.of_nat di))
  by (rewrite (Q 23%bv 23 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity) ltac:(s22e_in)); exact R23).
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx - 4096 <= a < x_s1 cx) ->
  ~ (x_fr cx + 32 <= a < x_fr cx + 52) -> rdW W mem2 a = rdW W mem a).
{ intros a Ha N2 N3. rewrite (HKC a Ha); [exact (KA a Ha) | unfold FO_V; lia | change ESTACK with 4096; lia]. }
pose proof (proj1 HJ2) as HAR2.
destruct (al_frames _ _ LAWS ly S W mem2 md2 LT_FCLS (x_fpos cx) HAR2 HFin) as (_ & _ & HFpres2 & _).
rewrite Lfa, LFB in HFpres2.
assert (H64b : rdword (rdW W mem2) (x_s1 cx + 64) = Some (x_fr cx + FO_V)).
{ apply (s22e_kept_word (rdW W mem)); [|exact Hv64]. intros x Hx. apply K2; lia. }
assert (H96b : rdword (rdW W mem2) (x_s1 cx + 96) = Some (lt_not (x_fr cx + FO_V))).
{ apply (s22e_kept_word (rdW W mem)); [|apply HSL; apply in_or_app; right; unfold LT_LD; s22e_in].
  intros x Hx. apply K2; lia. }
assert (H200b : rdword (rdW W mem2) (x_s1 cx + 200) = Some SHADOW_OFF).
{ apply (s22e_kept_word (rdW W mem)); [|exact H200]. intros x Hx. apply K2; lia. }
assert (Hwd : writable_at SEGS (mrestrict (w_H W) mem2) (x_fr cx + FO_V + Z.of_nat di)).
{ apply (apresent_writable SEGS). exact (proj1 (HFpres2 (x_fr cx + FO_V + Z.of_nat di) ltac:(unfold FO_V; lia))). }
assert (Hw16 : forall o, 16 <= o < 20 -> writable_at SEGS (mrestrict (w_H W) mem2) (x_fr cx + FO_V + o)).
{ intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFpres2 (x_fr cx + FO_V + o) ltac:(unfold FO_V; lia))). }
pose proof (s22e_seed2 W regs2 mem2 (x_s1 cx) (x_fr cx + FO_V) (Z.of_nat di) Q9 Q23 ltac:(lia) ltac:(lia)
  ltac:(unfold FO_V; lia) ltac:(unfold FO_V; lia) ltac:(unfold FO_V; lia) ltac:(lia) H64b H96b H200b Hwd Hw16) as HS.
set (E2 := s22e_E2 regs2 (x_fr cx + FO_V) (Z.of_nat di)) in HS.
assert (HEIB : img_env VAL A_LIM E2) by (subst E2; unfold s22e_E2; apply Eimg_env).
assert (HAEB : env_agree 32 (Ereg regs2 [Z_to_bv 64 (x_fr cx + FO_V); Z_to_bv 64 (lt_not (x_fr cx + FO_V));
  Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 (x_fr cx + FO_V + Z.of_nat di)]) E2).
{ split; [intros n Hn; subst E2; unfold s22e_E2; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. }
assert (EEB : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = getr regs2 r)
  by (intros n r Hr; subst E2; unfold s22e_E2; apply ew_Eimg_Ereg_nat; exact Hr).
assert (EBX : forall j, (j < 4)%nat -> ew E2 (32 + j) =
  nth j [Z_to_bv 64 (x_fr cx + FO_V); Z_to_bv 64 (lt_not (x_fr cx + FO_V)); Z_to_bv 64 SHADOW_OFF;
         Z_to_bv 64 (x_fr cx + FO_V + Z.of_nat di)] (Z_to_bv 64 0))
  by (intros j Hj; subst E2; unfold s22e_E2; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EBX 0%nat ltac:(lia)) as EB32. pose proof (EBX 2%nat ltac:(lia)) as EB34.
pose proof (EBX 3%nat ltac:(lia)) as EB35. cbn [Nat.add nth] in EB32, EB34, EB35. clear EBX.
assert (UB32 : bv_unsigned (ew E2 32) = x_fr cx + FO_V) by (rewrite EB32; apply unsigned_lit_small; unfold FO_V; lia).
assert (UB35 : bv_unsigned (ew E2 35) = x_fr cx + FO_V + Z.of_nat di)
  by (rewrite EB35; apply unsigned_lit_small; unfold FO_V; lia).
assert (EB21 : ew E2 21 = Z_to_bv 64 vid)
  by (rewrite (EEB 21%nat 21%bv eq_refl),
        (Q 21%bv 21 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity) ltac:(s22e_in)); exact R21).
clearbody E2.
(* ---- 0x85ce0 .. 0x85d00: the trap tests pn >= 16 and ~v < pn (decided), a6 := the shadow base, v[pn] := 0,
   v.vid := vid; the run stops at 0x85d04 ---- *)
paj_run_to_sh RUNTOP HS HJ2 0xf44.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen with (n := 32%nat) (b := x_fr cx + FO_V); [reflexivity | exact UB32 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left. exists LT_FCLS, (x_fpos cx).
    split; [left; reflexivity|]. left. rewrite Lfa, LFB. unfold in_zr. cbn [fst snd]. unfold FO_V in Ha. lia. }
  eapply awr_ok_cons_gen with (n := 35%nat) (b := x_fr cx + FO_V + Z.of_nat di); [reflexivity | exact UB35 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left. exists LT_FCLS, (x_fpos cx).
    split; [left; reflexivity|]. left. rewrite Lfa, LFB. unfold in_zr. cbn [fst snd]. unfold FO_V in Ha. lia. }
  apply awr_ok_nil. }
rename HF into HFB, HFr into HFrB, HG into HGB.
lazymatch goal with |- SRr _ _ (mkCfg _ ?mm) _ => set (md3 := mm) in *; clearbody md3 end.
lazymatch type of HS with context [restrict _ ?m3] => rename m3 into ms3 end.
(* the run wrote only v[pn] and v.vid *)
assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (x_fr cx + FO_V + Z.of_nat di <= a < x_fr cx + FO_V + Z.of_nat di + 1) ->
  ~ (x_fr cx + FO_V + 16 <= a < x_fr cx + FO_V + 20) -> rdW W (ms_mem ms3) a = rdW W mem2 a).
{ intros a Ha N1 N2.
  apply (kept_of_frame E2 _ (w_H W) mem2 _
    (fun x => (x_fr cx + FO_V + Z.of_nat di <= x < x_fr cx + FO_V + Z.of_nat di + 1) \/
              (x_fr cx + FO_V + 16 <= x < x_fr cx + FO_V + 20)) HFrB);
    [| exact Ha | intros [Hq | Hq]; contradiction].
  intros b wlo whi x Hin Hx.
  lazymatch type of Hin with In _ (windows ?rs) => let w := eval vm_compute in (windows rs) in change (In (b, wlo, whi) w) in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hx; rewrite ?UB32, ?UB35 in Hx; cbv beta; lia |]).
  destruct Hin. }
(* every byte outside the window below s1 and v's 20 bytes is the segment entry's *)
assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx - 4096 <= a < x_s1 cx) ->
  ~ (x_fr cx + 32 <= a < x_fr cx + 52) -> rdW W (ms_mem ms3) a = rdW W mem a).
{ intros a Ha N2 N3. rewrite (KB a Ha); [exact (K2 a Ha N2 N3) | unfold FO_V; lia | unfold FO_V; lia]. }
assert (KBLK : forall b n, In (b, n) (ablocks B ly S) -> forall x, b <= x < b + n -> rdW W (ms_mem ms3) x = rdW W mem x).
{ intros b n Hin x Hx. destruct (KBLK0 b n Hin x Hx) as (Hx0 & Hx1 & Hx2). apply KALL; lia. }
(* the chunks of v.vid and v[pn] *)
assert (RK : forall j r, nth_error (ss_mem ltac:(lazymatch type of HS with st_ok_pi _ _ _ ?s _ => exact s end)) j = Some r ->
  region_ok SEGS E2 (mrestrict (w_H W) (ms_mem ms3)) r)
  by (intros j r Hj; exact (st_ok_pi_region_nth _ _ (restrict (w_H W) ms3) j r HS Hj)).
lazymatch type of HS with st_ok_pi _ _ _ ?ssB _ =>
  let r1 := eval vm_compute in (nth 1 (ss_mem ssB) (YP09.mkRegion None 0 0 0 0 [])) in
  let r2 := eval vm_compute in (nth 2 (ss_mem ssB) (YP09.mkRegion None 0 0 0 0 [])) in
  pose proof (RK 1%nat r1 ltac:(vm_compute; reflexivity)) as RB2;
  pose proof (RK 2%nat r2 ltac:(vm_compute; reflexivity)) as RB3
end.
clear RK.
destruct RB2 as (_ & _ & _ & CB2). destruct RB3 as (_ & _ & _ & CB3).
cbn [YP09.r_base YP09.r_chunks base_val] in CB2, CB3. rewrite UB32 in CB2. rewrite UB35 in CB3.
assert (HZ : rdW W (ms_mem ms3) (x_fr cx + FO_V + Z.of_nat di) = Some 0).
{ apply Forall_inv in CB3.
  pose proof (val_of_chunk_ok SEGS _ _ _ 0 1 (SLit 0) 0 CB3 eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as HV.
  rewrite Z.add_0_r in HV. exact (s22e_rd_zero _ _ _ _ HV). }
assert (HVAL : sa_val (rdW W (ms_mem ms3)) (x_fr cx + FO_VID) 4 vid).
{ apply Forall_inv in CB2.
  pose proof (val_of_chunk_ok SEGS _ _ _ 16 4 (SOff 21 0) vid CB2
    ltac:(cbn [sv_denot]; rewrite EB21, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as HV.
  replace (x_fr cx + FO_VID) with (x_fr cx + FO_V + 16) by (unfold FO_V, FO_VID; lia).
  exact (s22e_sa_val _ _ _ _ 4 vid HV). }
(* the registers at 0x85d04 *)
pmkst HS.
prreg HS (16%bv : bv 5) F16.
pose proof (regs_kept_of_st_ok_pi _ _ _ regs2 [Z_to_bv 64 (x_fr cx + FO_V); Z_to_bv 64 (lt_not (x_fr cx + FO_V));
  Z_to_bv 64 SHADOW_OFF; Z_to_bv 64 (x_fr cx + FO_V + Z.of_nat di)]
  [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26; 27]%bv HS HAEB ltac:(vm_compute; reflexivity)) as HPB.
cbn [ms_regs restrict] in HPB.
assert (FIN : forall (r : bv 5) z, acallee_saved z -> Z_to_bv 5 z = r ->
  In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26; 27]%bv -> getr (ms_regs ms3) r = getr regs r).
{ intros r z Hz Hr Hin. rewrite (HPB r Hin). apply (Q r z Hz Hr). cbn [In] in Hin |- *. tauto. }
assert (F16' : getr (ms_regs ms3) 16 = w64 SHADOW_OFF) by (rewrite F16; exact EB34).
assert (HAR3 : AR SEGS B ly S W (ms_mem ms3) md3) by exact (proj1 HJ2).
(* ---- the cut K85d04 i ---- *)
assert (HFR3 : lt_frame B cx ly S W (ms_regs ms3) (ms_mem ms3) md3 k LFO_NV).
{ apply (s22e_frame_kept cx ly S W regs mem md k LFO_NV (ms_regs ms3) (ms_mem ms3) md3 HFR HJ2).
  - exact (FIN 2%bv 2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity) ltac:(s22e_in)).
  - exact (FIN 3%bv 3 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity) ltac:(s22e_in)).
  - exact (FIN 4%bv 4 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity) ltac:(s22e_in)).
  - exact (FIN 8%bv 8 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity) ltac:(s22e_in)).
  - exact (FIN 9%bv 9 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity) ltac:(s22e_in)).
  - intros x Hx. apply KALL; lia.
  - intros x Hx. apply KALL; lia.
  - intros x Hx. unfold LT_FLAGW in Hx. apply KALL; lia.
  - intros x Hx. apply KALL; lia.
  - intros x Hx. rewrite Hsh in Hx. apply KALL; unfold SHADOW_OFF in *; lia. }
assert (HIMG3 : lt_img B cx (rdW W (ms_mem ms3))).
{ apply (s22e_img_kept cx W (ms_mem ms3) (rdW W mem)); [|exact HIMG].
  intros a Ha. unfold kImgEnd in Ha. apply KALL; lia. }
assert (HSL3 : lt_slots cx (rdW W (ms_mem ms3)) (LT_LV cx c m ++ LT_LD cx m tab mt i)).
{ intros o v Hin. pose proof (s22e_L_offs cx c m tab mt i o v Hin) as Ho.
  apply (s22e_kept_word (rdW W mem)); [|exact (HSL o v Hin)].
  intros x Hx. apply KALL; lia. }
assert (HCM3 : lt_cm (rdW W (ms_mem ms3)) c m (x_run cx)).
{ destruct HCM as [HRC HMC]. split.
  - apply (s22e_kept_rconf (rdW W mem)); [|exact HRC]. intros x Hx. exact (KBLK c _ HcIn x Hx).
  - apply (s22e_kept_mconf (rdW W mem)); [|exact HMC]. intros x Hx. exact (KBLK m _ HmIn x Hx). }
assert (HTABS3 : lt_tabs cx (rdW W (ms_mem ms3)) tab mt (snd (x_decl cx i))).
{ destruct HTABS as (Hl0 & HRT & HGT & HNN & HMT & HMl).
  split; [exact Hl0|]. split.
  { apply (s22e_kept_rtab (rdW W mem)); [|exact HRT]. intros x Hx. apply (KBLK tab (x_tabn cx) HtIn).
    unfold x_tabn, seg_spec.RVLAN_SIZE. lia. }
  split.
  { apply (s22e_kept_guard (rdW W mem)); [|exact HGT]. intros x Hx. apply (KBLK tab (x_tabn cx) HtIn).
    unfold x_tabn, seg_spec.RVLAN_SIZE in *. lia. }
  split.
  { apply (s22e_kept_val (rdW W mem)); [|exact HNN]. intros x Hx. unfold FO_N in Hx. apply KALL; lia. }
  split; [|exact HMl].
  apply (s22e_kept_mtab (rdW W mem)); [|exact HMT]. intros x Hx. apply (KBLK mt (x_mtn cx) HmtIn).
  unfold x_mtn, seg_spec.MVLAN_SIZE. lia. }
assert (HSTRZ : sa_strz (rdW W (ms_mem ms3)) (x_fr cx + FO_V) (firstn di (SegModel.ms_name (x_seg cx i)))).
{ split.
  - intros j Hj. rewrite length_app, length_firstn in Hj. cbn [length] in Hj.
    destruct (Nat.lt_ge_cases j di) as [Hlt | Hge].
    + rewrite app_nth1 by (rewrite length_firstn; lia). rewrite nth_firstn.
      destruct (Nat.ltb_spec j di) as [_|Hn]; [|lia].
      rewrite (KB (x_fr cx + FO_V + Z.of_nat j)); [| unfold FO_V; lia | unfold FO_V; lia | unfold FO_V; lia].
      rewrite (HCPY (Z.of_nat j) ltac:(lia)).
      rewrite (KA (seg_spec.mseg_addr m i + Z.of_nat j)) by lia.
      pose proof (HNZ j ltac:(rewrite length_app; cbn [length]; lia)) as Hb.
      rewrite app_nth1 in Hb by lia. exact Hb.
    + assert (Hj' : j = di) by lia. subst j.
      rewrite app_nth2 by (rewrite length_firstn; lia). rewrite length_firstn.
      replace (di - Nat.min di (length (SegModel.ms_name (x_seg cx i))))%nat with 0%nat by lia.
      cbn [nth]. exact HZ.
  - intros Hin. apply HN0. rewrite <- (firstn_skipn di (SegModel.ms_name (x_seg cx i))).
    apply in_or_app. left. exact Hin. }
change (SRr SEGS W (cfg_at SEGS (BASE + LO_K85d04) (ms_regs ms3) (ms_mem ms3) md3) (lt_post B MT cx)).
exact (HK fx cx ly S W (ms_regs ms3) (ms_mem ms3) md3 k acc c m tab mt (firstn di (SegModel.ms_name (x_seg cx i))) vid
  HB0 HFRM Hi (conj HFR3 (conj HIMG3 (conj HBLK HBUD)))
  (s22e_hblk_kept ly S _ ly S W (ms_mem ms3) md3 c _ HAR3 HHc HcIn)
  (s22e_hblk_kept ly S _ ly S W (ms_mem ms3) md3 m _ HAR3 HHm HmIn)
  (s22e_hblk_kept ly S _ ly S W (ms_mem ms3) md3 tab _ HAR3 HHt HtIn)
  (s22e_hblk_kept ly S _ ly S W (ms_mem ms3) md3 mt _ HAR3 HHmt HmtIn)
  Hign Hsplit F16'
  ltac:(rewrite (FIN 20%bv 20 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity) ltac:(s22e_in)); exact R20)
  ltac:(rewrite (FIN 21%bv 21 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity) ltac:(s22e_in)); exact R21)
  ltac:(rewrite (FIN 22%bv 22 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity) ltac:(s22e_in)); exact R22)
  ltac:(rewrite (FIN 24%bv 24 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity) ltac:(s22e_in)); exact R24)
  ltac:(rewrite (FIN 26%bv 26 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity) ltac:(s22e_in)); exact R26)
  ltac:(rewrite (FIN 27%bv 27 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity) ltac:(s22e_in)); exact R27)
  Hdecl HSL3 HCM3 HTABS3 HSTRZ HVAL).
Qed.

End e.
End f.
End d.
