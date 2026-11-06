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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 610 of its 654 lines of code are new or changed and 409 lines of the source are left out. *)
(* The image-B port of lib/A/Prog/reac_segconf_declared_s2.v (commit 6121a10279e4), ADAPTED:
   the same design (a token run over the checked stretch from KL, the frame's shadow made a writable region for a
   token run with an empty span to the call, the call of reac_declared_vlan_split through
   PaNoChain.cl_callS_wide, the re-seat at the return with a0 pinned to split's answer), written against image B's
   code, registers and slots, with image B's two UBSan trap branches refuted at their branch and image B's
   no-split arm that reloads a3 from 80(s1).
   Segment S2 of the walk of reac_segconf_declared on fuzz_segconf.asan-ubsan (image B; the interface is
   reac_segconf_declared_d.v, the facts it shares with no other segment reac_segconf_declared_s2a.v): the head of
   the loop over c->seg, from the cut KL (0x8a000) at pass i to the latch KT (0x8a0b4) at pass i or to the cut KA
   (0x8a048) after reac_declared_vlan_split returned 1. The stretch:
     0x8a000 beq s8,a4 -> unimp        UBSan trap: i = 32           refuted: i < length segs <= 32 (rconf_enc)
     0x8a004 bltu a3,s2 -> unimp       UBSan trap: ~c <u 356 i      refuted: c + 356 i < 2 ^ 64 (c's block)
     0x8a008-0x8a014 the inline check of seg[i].ignore (srli/add/lb of its shadow byte, bnez to the slow path
       0x8a0d8, whose andi/addi 3/bge goes to the error path 0x8a210 or back to 0x8a018): passes, its obligation
       is range_addressable (c + 356 i + 24) 4, which the allocator invariant gives for c's live block
     0x8a018 lw a0,24(s6)               seg[i].ignore (0 or 1)
     0x8a01c bnez a0 -> KT             ignored: KT at pass i, nothing written (dcl_go_ignore)
     0x8a020-0x8a03c the frame's shadow bytes 4, 5 := 0 and 8 := 2 (parent and vid addressable), the arguments
     0x8a040 jal reac_declared_vlan_split, through its contract (PaNoChain.cl_callS_wide)
     0x8a044 beqz a0                   split gave 1: KA; split gave 0: 0x8a09c-0x8a0b0 (a3 := 80(s1), a4 := 32,
                                       the three shadow bytes := 0xf8) to KT at pass i (dcl_go_nosplit)
   The frame's shadow lies in the shadow band, so the token run that stores to it has an empty span
   (dcs2_Bspan0), and the run from the return to KT that stores to it is a plain run (PaLibF.v
   SRr_run_to_pi_AJ). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaSB PaDenot PaLibG PaLibF PaLibH PaCall PaCallRun PaNoChain.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegObj SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
reac_declared_vlan_split_c reac_declared_vlan_add_c reac_segconf_declared_c reac_segconf_declared_d
reac_segconf_declared_lem reac_segconf_declared_s2a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the return point of the split call *)
Definition DCS2_RET : Z := AF_reac_segconf_declared + 0x1c8.

(* reader facts as the engine's val_mem; the reader under a memory equal pointwise; a fact from a value *)
Lemma dcs2_val_mem : forall segs H mem a n v,
  sa_val (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:E; [|cbn [option_map] in Hv; discriminate].
cbn [option_map] in Hv. injection Hv as Hv. f_equal.
first [ rewrite <- Hv
| change (YG0f.le_byte v n k) with (YO0f.le_byte v n k); rewrite <- Hv
| change (YO0f.le_byte v n k) with (YG0f.le_byte v n k); rewrite <- Hv ].
symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma dcs2_aview_ext : forall segs H (m m' : word -> option byte), (forall x, m' x = m x) ->
  forall a, aview segs H m' a = aview segs H m a.
Proof. intros segs H m m' He a. unfold aview, mbyte, mrestrict. cbv beta. rewrite (He (Z_to_bv 64 a)). reflexivity. Qed.
Lemma dcs2_afact : forall E m v lo hi al,
  ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi -> v mod 2 ^ al = 0 -> 0 <= al <= 64 ->
  afact_ok E m (mkAF lo hi al).
Proof.
intros E m v lo hi al Hm Hv Hlh Hal Hal2. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Hm, unsigned_lit_small by exact Hv. split; [exact Hlh | split; [exact Hal | exact Hal2]].
Qed.
(* lw sign-extends the ignore flag, a small non-negative value *)
Lemma dcs2_sext_U : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 -> U E (SExt true 32 (SOff n 0)) = v.
Proof.
intros E n v He Hv. rewrite U_SExt, (U_atom E n v He) by lia.
unfold zcanon, M64, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
cbn -[Z.add Z.mul Z.modulo Z.div Z.sub]. lia.
Qed.
(* a run over read-only regions writes nothing *)
Lemma dcs2_frame_ro : forall E rs (m m' : word -> option byte), frame_of E rs m m' ->
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> forall x, m' x = m x.
Proof.
intros E rs m m' H Hro x. apply H. intros (r & Hr & Ha).
rewrite forallb_forall in Hro. pose proof (Hro r Hr) as Hw. apply Z.leb_le in Hw. lia.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the state at KL: the registers, atom 32 = seg[i].ignore; the region of seg[i].ignore based at s6 = c + 356 i
   (atom 22); the shadow base s5 (atom 21) is the token engine's Bx; s9 = c + 356 i + 24 (atom 25) is the address
   the inline check tests *)
Definition dcs2_EA (regs : bvmap 5 word) (ign : Z) : env := Eimg (Ereg regs [w64 ign]).
Definition dcs2_Bx : sv := SOff 21 0.
Definition dcs2_ignR : YP09.region := YP09.mkRegion (Some 22%nat) 24 28 0 0 [YP09.mkChunk 24 (CVal 4 (SOff 32 0))].
Definition dcs2_factsA : facts :=
  mkFacts [(21%nat, mkAF SB SB 0); (22%nat, mkAF 4096 (2 ^ 47 - 32) 2); (25%nat, mkAF 4096 (2 ^ 47 - 32) 2)] [] [].
Definition dcs2_ssA : sstate := mkSS DC_KL sr_atoms [dcs2_ignR] None dcs2_factsA.
(* the frame's 16 shadow bytes, based at s11 = SB + F / 8 (atom 27), writable *)
Definition dcs2_shR : YP09.region := YP09.mkRegion (Some 27%nat) 0 16 0 16 [].
(* the states at the return point 0x8a044: no region when split gave 1 (the beqz to KA); when it gave 0, the slot
   80(s1) (~c, atom 32) the reload at 0x8a09c reads and the frame's shadow the stores at 0x8a0a8-0x8a0b0 write *)
Definition dcs2_slotR : YP09.region := YP09.mkRegion (Some 9%nat) 80 88 0 0 [YP09.mkChunk 80 (CVal 8 (SOff 32 0))].
Definition dcs2_ssS : sstate := mkSS DCS2_RET sr_atoms [] None (mkFacts [] [] []).
Definition dcs2_ssN : sstate :=
  mkSS DCS2_RET sr_atoms [dcs2_slotR; dcs2_shR] None (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] []).
Lemma dcs2_pres : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r H Hr. pose proof (H _ Hr) as E. rewrite Z_to_bv_bv_unsigned in E. exact E. Qed.
Lemma dcs2_seedS : forall (W : world SEGS) mem (regs : bvmap 5 word) v,
  st_ok_pi SEGS VAL (dcs2_EA regs v) dcs2_ssS
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + DCS2_RET)) mem (seg_rom SEGS))).
Proof using.
intros W mem regs v. rewrite restrict_mkst_fx. unfold dcs2_ssS. apply pa_entry_st_ok_full.
- unfold dcs2_EA. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn. repeat constructor.
- split; [exact I | split; [exact I | exact I]].
Qed.
Lemma dcs2_seedN : forall (W : world SEGS) mem (regs : bvmap 5 word) s1 F nc,
  getr regs 9 = w64 s1 -> getr regs 27 = w64 (SB + F / 8) -> 2 ^ 46 <= s1 -> s1 + 88 <= 2 ^ 47 -> s1 mod 32 = 0 ->
  0 <= F / 8 < 0xffffff00000 -> 0 <= nc < 2 ^ 64 -> rdword (rdW W mem) (s1 + 80) = Some nc ->
  (forall o, 0 <= o < 16 -> apresent (w_H W) mem (SB + F / 8 + o)) ->
  st_ok_pi SEGS VAL (dcs2_EA regs nc) dcs2_ssN
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + DCS2_RET)) mem (seg_rom SEGS))).
Proof using.
intros W mem regs s1 F nc H9 H27 Hs1a Hs1b Hs1m HF Hnc Hslot Hpres.
set (E := dcs2_EA regs nc).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr).
{ intros m rr Hm. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst E. unfold dcs2_EA. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (X32 : ew E 32 = w64 nc)
  by (subst E; unfold dcs2_EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E9 : ew E 9 = Z_to_bv 64 s1) by (rewrite (EEo 9%nat 9%bv eq_refl); exact H9).
assert (E27 : ew E 27 = Z_to_bv 64 (SB + F / 8)) by (rewrite (EEo 27%nat 27%bv eq_refl); exact H27).
assert (U9 : base_val E (Some 9%nat) = s1) by (cbn [base_val]; rewrite E9; apply unsigned_lit_small; lia).
assert (U27 : base_val E (Some 27%nat) = SB + F / 8) by (cbn [base_val]; rewrite E27; apply unsigned_lit_small; unfold SB; lia).
rewrite restrict_mkst_fx. unfold dcs2_ssN. apply pa_entry_st_ok_full.
- subst E. unfold dcs2_EA. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold dcs2_slotR, dcs2_shR. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    apply (chunk_ok_val SEGS E _ s1 80 8 (SOff 32 0) nc);
      [cbn [sv_denot]; rewrite X32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Hslot)].
  + rewrite U27. split; [unfold SB; lia|]. split; [unfold SB; lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). exact (Hpres o Ho).
- apply pairwise_disjoint_of_extents. unfold dcs2_slotR, dcs2_shR, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite U9, U27.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold SB.
  repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok].
  split; [apply (dcs2_afact E 9%nat s1); [exact E9 | lia | lia | change (2 ^ 5) with 32; exact Hs1m | lia]|].
  exact I.
Qed.
Lemma dcs2_EA_reg : forall (regs : bvmap 5 word) v m (rr : bv 5), Z.of_nat m = bv_unsigned rr ->
  ew (dcs2_EA regs v) m = getr regs rr.
Proof using.
intros regs v m rr Hm. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold dcs2_EA. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm.
Qed.
Lemma dcs2_EA_x32 : forall (regs : bvmap 5 word) v, ew (dcs2_EA regs v) 32 = w64 v.
Proof using. intros regs v. unfold dcs2_EA. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra regs _ 0). Qed.
(* the span of the token run over the shadow stores: the writable shadow window lies outside it *)
Definition dcs2_Bspan0 : Z * Z := (0, 0).
(* the three shadow bytes split's caller stores, read back from the frame's shadow region *)
Lemma dcs2_shR_bytes : forall E H mem,
  region_ok SEGS E (mrestrict H mem) (YP09.mkRegion (Some 27%nat) 0 16 0 16
    [YP09.mkChunk 8 (CVal 1 (SLit 2)); YP09.mkChunk 5 (CVal 1 (SLit 0)); YP09.mkChunk 4 (CVal 1 (SLit 0))]) ->
  aview SEGS H mem (bv_unsigned (ew E 27) + 4) = Some 0 /\ aview SEGS H mem (bv_unsigned (ew E 27) + 5) = Some 0 /\
  aview SEGS H mem (bv_unsigned (ew E 27) + 8) = Some 2.
Proof using.
intros E H mem (_ & _ & _ & HC). cbn [YP09.r_chunks YP09.r_base base_val] in HC.
apply Forall_inv_tail in HC as HC'. apply Forall_inv in HC as H8.
apply Forall_inv_tail in HC' as HC''. apply Forall_inv in HC' as H5. apply Forall_inv in HC'' as H4.
destruct (H8 0 ltac:(cbn; lia)) as (b8 & E8a & E8b).
destruct (H5 0 ltac:(cbn; lia)) as (b5 & E5a & E5b).
destruct (H4 0 ltac:(cbn; lia)) as (b4 & E4a & E4b).
cbn [YP09.cbyte YP09.c_val YP09.c_off] in E8a, E5a, E4a, E8b, E5b, E4b.
injection E8a as <-. injection E5a as <-. injection E4a as <-.
rewrite Z.add_0_r in E8b, E5b, E4b.
unfold aview. rewrite E8b, E5b, E4b. split; [|split]; reflexivity.
Qed.

Lemma dcs2_seedA : forall (W : world SEGS) mem (regs : bvmap 5 word) X ign,
  getr regs 21 = w64 SB -> getr regs 22 = w64 X -> getr regs 25 = w64 (X + 24) ->
  4096 <= X -> X + 24 <= 2 ^ 47 - 32 -> X mod 4 = 0 -> 0 <= ign < 2 ^ 32 ->
  sa_val (rdW W mem) (X + 24) 4 ign ->
  st_ok_pi SEGS VAL (dcs2_EA regs ign) dcs2_ssA
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + DC_KL)) mem (seg_rom SEGS))) /\
  sh_ok SEGS dcs2_Bx [] (dcs2_EA regs ign) (mrestrict (w_H W) mem).
Proof using.
intros W mem regs X ign H21 H22 H25 HX1 HX2 HX4 Hign HV.
set (E := dcs2_EA regs ign).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr).
{ intros m rr Hm. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  subst E. unfold dcs2_EA. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (X32 : ew E 32 = w64 ign)
  by (subst E; unfold dcs2_EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E21 : ew E 21 = Z_to_bv 64 SB) by (rewrite (EEo 21%nat 21%bv eq_refl); exact H21).
assert (E22 : ew E 22 = Z_to_bv 64 X) by (rewrite (EEo 22%nat 22%bv eq_refl); exact H22).
assert (E25 : ew E 25 = Z_to_bv 64 (X + 24)) by (rewrite (EEo 25%nat 25%bv eq_refl); exact H25).
assert (U22 : base_val E (Some 22%nat) = X).
{ cbn [base_val]. rewrite E22. apply unsigned_lit_small. lia. }
split; [|unfold sh_ok; apply Forall_nil].
rewrite restrict_mkst_fx. unfold dcs2_ssA. apply pa_entry_st_ok_full.
- subst E. unfold dcs2_EA. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold dcs2_ignR. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite U22. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  apply (chunk_ok_val SEGS E _ X 24 4 (SOff 32 0) ign);
    [cbn [sv_denot]; rewrite X32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
    | cbn; lia | lia | exact (dcs2_val_mem SEGS (w_H W) mem _ 4%nat ign HV)].
- apply pairwise_disjoint_of_extents. unfold dcs2_ignR, extent_of_region. cbn. repeat constructor.
- split; [|split; [exact I | exact I]].
  cbn [dcs2_factsA f_atoms atoms_ok].
  split; [apply (dcs2_afact E 21%nat SB); [exact E21 | unfold SB; lia | lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | lia]|].
  split; [apply (dcs2_afact E 22%nat X); [exact E22 | lia | lia | change (2 ^ 2) with 4; exact HX4 | lia]|].
  split; [apply (dcs2_afact E 25%nat (X + 24)); [exact E25 | lia | lia | change (2 ^ 2) with 4; clear - HX4; Z.div_mod_to_equations; lia | lia]|].
  exact I.
Qed.

Section e.
Variable B : asyms.
Variables RLO RHI GOTW GUARD : Z.
(* every program function's call target against the listing's base (SegObj.seg_sig_prog) *)
Hypothesis SIGP : seg_sig_prog (PI := PI).
(* the callee's contract, at split's entry and stack *)
Hypothesis SPLIT : forall fx0 : YK11.FPState, @reac_declared_vlan_split_contract fx0 rc SK SEGS B
  (BASE + AF_reac_declared_vlan_split) DC_STK_SPLIT RLO RHI GOTW GUARD.
(* the two image facts of the interface (dc_ro_imgP, dc_sspP) *)
Hypothesis RO_IMG : dc_ro_imgP RLO RHI.
Hypothesis SSP : dc_sspP B GOTW GUARD.
Context {RO : ro_below_ofl SEGS RLO RHI}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RUNTOP := SRr_run_to_pi_AJ (PL := PL_seg) B LAWS.
Ltac dcs2_awr_ro :=
  lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
Ltac dcs2_mdv nm := lazymatch goal with |- context [with_vm_backing (m_vm_lazy ?md) ?mt ?md] =>
  set (nm := with_vm_backing (m_vm_lazy md) mt md) in *; clearbody nm end.
Ltac dcs2_name HS nm :=
  lazymatch type of HS with context [restrict _ ?m] => rename m into nm end.
Ltac dcs2_rr HS r Hr := prreg HS r Hr;
  try (let n := eval vm_compute in (Z.to_nat (bv_unsigned r)) in rewrite (dcs2_EA_reg _ _ n r eq_refl) in Hr).
Ltac dcs2_cs := cbv [acallee_saved];
  match goal with |- context [bv_unsigned ?x] => let z := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with z end;
  lia.
(* split's post (reac_declared_vlan_split_c.v:191-198) at a call with string s, parent and vid *)
Definition dcs2_splitQ (s : list Z) (parent vid : Z) (ly : alayout) (S : astate) (W : world SEGS)
  (mem : word -> option byte) (regs : bvmap 5 word)
  : alayout -> astate -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly' S' W' regs' mem' md' =>
 getr regs' 10 = w64 (match SegModel.vlan_split s with Some _ => 1 | None => 0 end) /\
 (match SegModel.vlan_split s with
  | Some (p, v) => sa_strz (aview SEGS (w_H W') mem') parent p /\ sa_val (aview SEGS (w_H W') mem') vid 2 v
  | None => True
  end) /\
 sa_kept SEGS W mem W' mem' regs DC_STK_SPLIT (split_E parent vid s) /\
 sa_noalloc B ly S ly' S'.
Lemma dcs2_sig : SIGMA SS_reac_declared_vlan_split = BASE + AF_reac_declared_vlan_split.
Proof using SIGP.
assert (H1 : In SS_reac_declared_vlan_split seg_prog_syms) by (cbv [seg_prog_syms In]; tauto).
rewrite (SIGP _ H1). f_equal; vm_compute; reflexivity.
Qed.

Lemma dc_S2 : dc_S2P B DC_STK RLO RHI GOTW GUARD.
Proof using SIGP SPLIT RO_IMG SSP RO LAWS RUN RUNTO BR RUNTOP.
intros c i HPRE HKT HKA. unfold from_KL, dc_from.
intros ti added ly3 S3 W3 regs3 mem3 md3 (HFI & HUN & HTAB & Hi & HLOOP & HLR & HARG & HSL).
pose proof HFI as [HJ F2 F3 F4 F8 F9 F27 FSV F32 F40 FTB FMX FN FFL].
pose proof HLR as (R24 & R22 & R25 & R23 & R20 & R19 & R26 & R21 & R18).
pose proof HARG as (R13 & R14).
pose proof HPRE as [HAFN _ _ HC64 _ _ _ _ _ _ HDP _ HNEV].
pose proof HUN as [HPERM Hly3 HFS]. subst ly3.
pose proof HJ as HJ0.
pose proof HJ as (HAR3 & _ & _ & _ & _ & Hfrs & Hnev3 & _).
pose proof HAFN as (HAR0 & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct (dc_sp1_facts (dc_sp0 c) Hal16) as (Hs1m & Hs1).
change (dc_sp1 (dc_sp0 c)) with (dc_s1 c) in Hs1m, Hs1.
change (spZ (x_regs c)) with (dc_sp0 c) in Hal16, Hstk0, Hceil, Hslo, Hshi, H47, Hbot, Htop, Htop2.
assert (DS : DC_STK = 12592) by reflexivity. assert (DSS : DC_STK_SPLIT = 12352) by reflexivity.
pose proof HTAB as (_ & _ & _ & HTI).
pose proof HDP as (Hc0 & Hc16 & _ & (pb & nb & Hin & Hp1 & Hp2) & _).
assert (Hin3 : In (pb, nb) (ablocks B (x_ly c) S3)) by exact (Permutation_in _ (Permutation_sym HPERM) Hin).
destruct (al_blocks _ _ LAWS _ _ _ _ _ pb nb HAR3 Hin3) as (_ & Hpb4096 & Hpbc & Hpbapp & _ & _ & Hnb).
pose proof (req_size_pos nb (proj1 Hnb)) as [_ Hrq].
pose proof asan_consts as (C1 & _).
unfold seg_spec.SEG_C_SIZE in Hp2.
destruct (dcs2_rconf_at B RLO RHI GOTW GUARD c (x_ly c) S3 W3 mem3 md3 0 HPRE HJ HUN) as (bs & Hbs & Henc).
pose proof Henc as (_ & Hle32 & _).
assert (Hi32 : (i < 32)%nat) by (unfold dc_segs in Hi; lia).
set (sg := nth i (dc_segs c) rseg_d) in *.
set (ign := if rs_ignore sg then 1 else 0).
assert (Hign : 0 <= ign <= 1) by (unfold ign; destruct (rs_ignore sg); lia).
assert (HIGN : sa_val (rdW W3 mem3) (x_c c + 356 * Z.of_nat i + 24) 4 ign).
{ exact (dcs2_rd_ign _ _ _ i (ex_intro _ bs (conj Hbs Henc)) Hi). }
set (X := x_c c + 356 * Z.of_nat i) in *.
assert (HX : 4096 <= X /\ X + 28 <= x_c c + 16616) by (unfold X; lia).
assert (HX4 : X mod 4 = 0).
{ unfold X. replace (x_c c + 356 * Z.of_nat i) with ((4 * (x_c c / 16) + 89 * Z.of_nat i) * 4)
    by (pose proof (Z.div_mod (x_c c) 16 ltac:(lia)); lia).
  apply Z.mod_mul. lia. }
assert (HRA24 : range_addressable (rdW W3 mem3) SHADOW_OFF (X + 24) 4)
  by exact (range_addressable_of_block SEGS B LAWS (x_ly c) S3 W3 mem3 md3 pb nb (X + 24) 4 HAR3 Hin3
    ltac:(unfold X; lia) ltac:(unfold X; lia)).
destruct (dcs2_seedA W3 mem3 regs3 X ign R21 R22 R25 ltac:(lia) ltac:(lia) HX4 ltac:(lia) HIGN) as [HS SHOK].
assert (HEI : img_env VAL A_LIM (dcs2_EA regs3 ign)) by (unfold dcs2_EA; apply Eimg_env).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew (dcs2_EA regs3 ign) m = getr regs3 rr).
{ intros m rr Hm. pose proof (bv_unsigned_in_range 5 rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  unfold dcs2_EA. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hm. }
assert (X32 : ew (dcs2_EA regs3 ign) 32 = w64 ign)
  by (unfold dcs2_EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
assert (UB : U (dcs2_EA regs3 ign) dcs2_Bx = SHADOW_OFF)
  by (unfold dcs2_Bx; rewrite (U_atom _ 21 SB) by (first [rewrite (EEo 21%nat 21%bv eq_refl); exact R21 | unfold SB; lia]); reflexivity).
assert (U25 : U (dcs2_EA regs3 ign) (SOff 25 0) = X + 24)
  by (apply U_atom; [rewrite (EEo 25%nat 25%bv eq_refl); exact R25 | lia]).
(* the frame (1, x_fpos c) at the cut *)
assert (Hfin : In (1, x_fpos c) (frames S3)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 1 (x_fpos c) HAR3 Hfin) as (HF4096 & HFc & HFapp).
destruct (frame_al64 SEGS B _ _ _ _ _ 1 (x_fpos c) HAR3 Hfin) as (HF64 & _ & _).
change (fs_frame_bytes 1) with 128 in HFc, HFapp.
change (frame_addr (x_ly c) 1 (x_fpos c)) with (dc_F c) in HF4096, HFc, HFapp, HF64.
assert (HFb : dc_F c / 8 < 0xffffff00000).
{ assert (dc_F c / 8 < 0x7fffff800000 / 8) by (apply Z.div_lt_upper_bound; lia).
  change (0x7fffff800000 / 8) with 0xffffff00000 in H. exact H. }
pose proof (Z.div_pos (dc_F c) 8 ltac:(lia) ltac:(lia)) as HF8p.
pose proof (dcs2_mem_of B c 0 (x_ly c) S3 W3 regs3 mem3 md3 ti added HFI HTAB HSL) as HM3.
unfold cfg_at, w64.
(* 0x8a000 beq s8,a4: the UBSan trap i = 32 *)
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. rewrite branch_eq_U in Hc.
  rewrite (U_atom _ 24 (Z.of_nat i)) in Hc by (first [rewrite (EEo 24%nat 24%bv eq_refl); exact R24 | lia]).
  rewrite (U_atom _ 14 32) in Hc by (first [rewrite (EEo 14%nat 14%bv eq_refl); exact R14 | lia]).
  apply Z.eqb_eq in Hc. lia. }
clear Hc.
paj_run_tok RUN HS HJ SHOK Bspan.
{ dcs2_awr_ro. }
dcs2_name HS msA.
pose proof (dcs2_frame_ro _ _ _ _ HF eq_refl) as HEQa. clear HF HFr HG.
dcs2_mdv mdA.
(* 0x8a004 bltu a3,s2: the UBSan trap ~c <u 356 i *)
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. rewrite branch_ltu_U in Hc.
  rewrite (U_atom _ 13 (2 ^ 64 - 1 - x_c c)) in Hc
    by (first [rewrite ?ew_ewset_other by lia; rewrite (EEo 13%nat 13%bv eq_refl); exact R13 | lia]).
  rewrite (U_atom _ 18 (356 * Z.of_nat i)) in Hc
    by (first [rewrite ?ew_ewset_other by lia; rewrite (EEo 18%nat 18%bv eq_refl); exact R18 | lia]).
  apply Z.ltb_lt in Hc. unfold X in *. lia. }
clear Hc.
(* 0x8a008 .. 0x8a018: the inline check of seg[i].ignore, its load; stop at bnez a0 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ rewrite U25. eapply (obl_of_range SEGS _ _ _ _ _ 4 (X + 24) 4); [| exact UB | lia | lia].
  intros x Hx. destruct (HRA24 x Hx) as (sv0 & Hsv & Hok). exists sv0. split; [|exact Hok].
  rewrite (dcs2_aview_ext SEGS (w_H W3) mem3 (ms_mem msA) HEQa). exact Hsv. }
{ dcs2_awr_ro. }
dcs2_mdv mdB. dcs2_name HS msB.
pose proof (dcs2_frame_ro _ _ _ _ HF eq_refl) as HEQb. clear HF HFr HG.
assert (HEQB : forall x, ms_mem msB x = mem3 x) by (intros x; rewrite HEQb; exact (HEQa x)).
(* 0x8a01c bnez a0: seg[i].ignore *)
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* ignored: KT at pass i, nothing written *)
  rewrite branch_ne_U in Hc.
  rewrite (dcs2_sext_U _ 32 ign) in Hc by (first [rewrite ?ew_ewset_other by lia; exact X32 | lia]).
  rewrite U_SLit in Hc. change (zcanon 0) with 0 in Hc.
  apply negb_true_iff, Z.eqb_neq in Hc.
  assert (Hig : rs_ignore sg = true) by (unfold ign in Hc; destruct (rs_ignore sg); [reflexivity | lia]).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan DC_KT.
  { dcs2_awr_ro. }
  dcs2_mdv mdC. dcs2_name HS msC.
  pose proof (dcs2_frame_ro _ _ _ _ HF eq_refl) as HEQc. clear HF HFr HG.
  assert (HEQ : forall x, ms_mem msC x = mem3 x) by (intros x; rewrite HEQc; exact (HEQB x)).
  prreg HS (2%bv : bv 5) T2. prreg HS (3%bv : bv 5) T3. prreg HS (4%bv : bv 5) T4. prreg HS (8%bv : bv 5) T8.
  prreg HS (9%bv : bv 5) T9. prreg HS (27%bv : bv 5) T27. prreg HS (13%bv : bv 5) T13.
  prreg HS (14%bv : bv 5) T14. prreg HS (18%bv : bv 5) T18. prreg HS (19%bv : bv 5) T19.
  prreg HS (20%bv : bv 5) T20. prreg HS (21%bv : bv 5) T21. prreg HS (22%bv : bv 5) T22.
  prreg HS (23%bv : bv 5) T23. prreg HS (24%bv : bv 5) T24. prreg HS (25%bv : bv 5) T25.
  prreg HS (26%bv : bv 5) T26.
  rewrite (EEo 2%nat 2%bv eq_refl) in T2. rewrite (EEo 3%nat 3%bv eq_refl) in T3.
  rewrite (EEo 4%nat 4%bv eq_refl) in T4. rewrite (EEo 8%nat 8%bv eq_refl) in T8.
  rewrite (EEo 9%nat 9%bv eq_refl) in T9. rewrite (EEo 27%nat 27%bv eq_refl) in T27.
  rewrite (EEo 13%nat 13%bv eq_refl) in T13. rewrite (EEo 14%nat 14%bv eq_refl) in T14.
  rewrite (EEo 18%nat 18%bv eq_refl) in T18. rewrite (EEo 19%nat 19%bv eq_refl) in T19.
  rewrite (EEo 20%nat 20%bv eq_refl) in T20. rewrite (EEo 21%nat 21%bv eq_refl) in T21.
  rewrite (EEo 22%nat 22%bv eq_refl) in T22. rewrite (EEo 23%nat 23%bv eq_refl) in T23.
  rewrite (EEo 24%nat 24%bv eq_refl) in T24. rewrite (EEo 25%nat 25%bv eq_refl) in T25.
  rewrite (EEo 26%nat 26%bv eq_refl) in T26.
  pmkst HS.
  assert (HMC : dcs2_mem c ti added W3 (ms_mem msC)).
  { apply (dcs2_mem_tr c ti added W3 W3 mem3 _ HM3). intros a _. exact (dcs2_aview_ext SEGS _ _ _ HEQ a). }
  pose proof HMC as (_ & _ & _ & _ & _ & _ & _ & HTABC & HSLC).
  apply (HKT ti added (x_ly c) S3 W3 (ms_regs msC) (ms_mem msC) mdC). unfold INV_KT.
  split.
  { apply (dcs2_fi_of B c 0 (x_ly c) S3 W3 (ms_regs msC) (ms_mem msC) mdC ti added HMC HJ);
      [rewrite T2; exact F2 | rewrite T3; exact F3 | rewrite T4; exact F4 | rewrite T8; exact F8
      | rewrite T9; exact F9 | rewrite T27; exact F27]. }
  split; [exact HUN|]. split; [exact HTABC|]. split; [exact Hi|].
  split.
  { destruct HLOOP as [HL1 HL2]. split; [|lia].
    rewrite <- (dcl_go_ignore (dc_segs c) i ti (x_max c) added Hi Hig). exact HL1. }
  split.
  { unfold dc_lregs. rewrite T24, T22, T25, T23, T20, T19, T26, T21, T18.
    exact (conj R24 (conj R22 (conj R25 (conj R23 (conj R20 (conj R19 (conj R26 (conj R21 R18)))))))). }
  split; [unfold dc_aregs; rewrite T13, T14; exact (conj R13 R14) | exact HSLC].
- (* not ignored: the frame's shadow made addressable, the arguments, the call *)
  rewrite branch_ne_U in Hc.
  rewrite (dcs2_sext_U _ 32 ign) in Hc by (first [rewrite ?ew_ewset_other by lia; exact X32 | lia]).
  rewrite U_SLit in Hc. change (zcanon 0) with 0 in Hc.
  apply negb_false_iff, Z.eqb_eq in Hc.
  assert (Hig : rs_ignore sg = false) by (unfold ign in Hc; destruct (rs_ignore sg); [lia | reflexivity]).
  destruct (al_frames _ _ LAWS _ _ _ _ _ 1 (x_fpos c) (proj1 HJ) Hfin) as (_ & _ & _ & HFSH).
  change (frame_addr (x_ly c) 1 (x_fpos c)) with (dc_F c) in HFSH. change (fs_frame_bytes 1 / 8) with 16 in HFSH.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
    assert (B27 : bv_unsigned (ew Ex 27) = SB + dc_F c / 8)
      by (rewrite ?ew_ewset_other by lia; rewrite (EEo 27%nat 27%bv eq_refl), F27; apply unsigned_lit_small; unfold SB; lia);
    assert (B22 : bv_unsigned (ew Ex 22) = X)
      by (rewrite ?ew_ewset_other by lia; rewrite (EEo 22%nat 22%bv eq_refl), R22; apply unsigned_lit_small; unfold X; lia);
    assert (ROK : region_ok SEGS Ex (ms_mem (restrict (w_H W3) msx)) dcs2_shR);
    [ unfold region_ok, dcs2_shR;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
      rewrite B27; split; [unfold SB; lia|]; split; [unfold SB; lia|]; split; [|constructor];
      intros o Ho; apply (apresent_writable SEGS);
      replace (SB + dc_F c / 8 + o) with (shadow_addr (dc_F c) + o) by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia);
      exact (proj1 (HFSH o ltac:(lia)))
    | ];
    assert (RDJ : all_disjoint Ex dcs2_shR (ss_mem ssx));
    [ let rs2 := eval vm_compute in (ss_mem ssx) in change (all_disjoint Ex dcs2_shR rs2);
      cbn [all_disjoint]; unfold extent_disjoint, dcs2_shR;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val extent_of_region fst snd]; rewrite ?B27, ?B22;
      unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hpbapp; unfold SB, X in *;
      repeat split; lia
    | ];
    pose proof (st_ok_pi_add_region Ex ssx _ dcs2_shR HS eq_refl ROK RDJ) as HS2;
    clear HS ROK RDJ
  end.
  lazymatch type of HS2 with st_ok_pi _ _ ?Ex _ _ =>
    assert (AF27 : afact_ok Ex 27 (mkAF (SB + 512) (SB + 2 ^ 44 - 16) 2))
      by (apply (dcs2_afact Ex 27%nat (SB + dc_F c / 8));
          [rewrite ?ew_ewset_other by lia; rewrite (EEo 27%nat 27%bv eq_refl); exact F27 | unfold SB; lia
          | unfold SB; split; [assert (512 <= dc_F c / 8) by (apply Z.div_le_lower_bound; lia); lia | lia]
          | change (2 ^ 2) with 4; unfold SB; clear - HF64; Z.div_mod_to_equations; lia | lia]) end.
  pose proof (st_ok_pi_add_fact _ _ _ 27%nat _ HS2 AF27) as HS3. clear HS2 AF27.
  lazymatch type of HS3 with st_ok_pi ?a ?b ?c ?ss ?m => let ss' := eval vm_compute in ss in change ss with ss' in HS3 end.
  lazymatch type of HS3 with st_ok_pi _ _ ?Ex _ (restrict _ ?msx) =>
    assert (SHOK3 : sh_ok SEGS dcs2_Bx [] Ex (mrestrict (w_H W3) (ms_mem msx))) by constructor end.
  (* 0x8a01c .. 0x8a040: the branch, the three shadow stores, the arguments, the call *)
  paj_run_tok RUN HS3 HJ SHOK3 dcs2_Bspan0.
  { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
    eapply awr_ok_cons_gen with (n := 27%nat) (b := SB + dc_F c / 8); [reflexivity | exact B27 | |].
    { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left. exists 1, (x_fpos c).
      split; [left; reflexivity|]. right. unfold in_zr, shadow_addr. cbn [fst snd].
      change (fs_frame_bytes 1 / 8) with 16. change (frame_addr (x_ly c) 1 (x_fpos c)) with (dc_F c).
      unfold SB, SHADOW_OFF in *. lia. }
    repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
  pmkst HS3. dcs2_mdv mdD. dcs2_name HS3 msD.
  (* the run wrote the frame's shadow only *)
  pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => SB + dc_F c / 8 <= a < SB + dc_F c / 8 + 16) HFr
    ltac:(intros b wlo whi a Hin' Hrr; vm_compute in Hin';
      repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?B27 in Hrr; cbv beta; lia |]);
      destruct Hin')) as UND.
  clear HF HFr HG.
  (* the registers at the call *)
  dcs2_rr HS3 (1%bv : bv 5) P1. dcs2_rr HS3 (2%bv : bv 5) P2. dcs2_rr HS3 (3%bv : bv 5) P3.
  dcs2_rr HS3 (4%bv : bv 5) P4. dcs2_rr HS3 (8%bv : bv 5) P8. dcs2_rr HS3 (9%bv : bv 5) P9.
  dcs2_rr HS3 (10%bv : bv 5) P10. dcs2_rr HS3 (11%bv : bv 5) P11. dcs2_rr HS3 (12%bv : bv 5) P12.
  dcs2_rr HS3 (13%bv : bv 5) P13.
  dcs2_rr HS3 (18%bv : bv 5) P18. dcs2_rr HS3 (19%bv : bv 5) P19. dcs2_rr HS3 (20%bv : bv 5) P20.
  dcs2_rr HS3 (21%bv : bv 5) P21. dcs2_rr HS3 (22%bv : bv 5) P22. dcs2_rr HS3 (23%bv : bv 5) P23.
  dcs2_rr HS3 (24%bv : bv 5) P24. dcs2_rr HS3 (25%bv : bv 5) P25. dcs2_rr HS3 (26%bv : bv 5) P26.
  dcs2_rr HS3 (27%bv : bv 5) P27.
  rewrite (dcs2_EA_reg regs3 ign 22 22%bv eq_refl), R22 in P10.
  rewrite (dcs2_EA_reg regs3 ign 19 19%bv eq_refl), R19 in P11.
  rewrite (dcs2_EA_reg regs3 ign 26 26%bv eq_refl), R26 in P13.
  (* the frame's shadow at the call: bytes 4, 5 = 0, byte 8 = 2 *)
  lazymatch type of HS3 with st_ok _ ?Ex ?ssx ?msx =>
    let r := eval vm_compute in (nth 0 (ss_mem ssx) dcs2_shR) in
    pose proof (st_ok_region_nth Ex ssx msx 0 r HS3 ltac:(vm_compute; reflexivity)) as HR0 end.
  lazymatch type of HR0 with region_ok _ ?Ex _ _ =>
    destruct (dcs2_shR_bytes Ex (w_H W3) (ms_mem msD) HR0) as (SH4 & SH5 & SH8) end.
  rewrite B27 in SH4, SH5, SH8. clear HR0.
  (* the memory at the call: the cut's, outside the frame's shadow *)
  assert (HDB : forall a, 0 <= a < 2 ^ 64 -> ~ (SB + dc_F c / 8 <= a < SB + dc_F c / 8 + 16) ->
    rdW W3 (ms_mem msD) a = rdW W3 mem3 a).
  { intros a Ha Hn. rewrite (UND a Ha Hn). exact (dcs2_aview_ext SEGS _ _ _ HEQB a). }
  assert (HMD : dcs2_mem c ti added W3 (ms_mem msD)).
  { apply (dcs2_mem_tr c ti added W3 W3 mem3 _ HM3). intros a HZa.
    destruct (dcs2_Z_out B RLO RHI GOTW GUARD c ti (x_ly c) S3 W3 mem3 md3 0 HPRE HJ0 HUN HTI a HZa)
      as (Ha64 & Hns & _).
    exact (HDB a Ha64 Hns). }
  (* split's premises: the read-only window, the frame chain, split_pre *)
  pose proof (dcs2_aro B RLO RHI GOTW GUARD c (x_ly c) S3 W3 (ms_mem msD) mdD 0 RO_IMG HPRE HJ) as HRODC.
  assert (HNV : forall kk, 0 <= kk < 4 -> rdW W3 (ms_mem msD) (x_n c + kk) <> None).
  { pose proof HMD as (_ & _ & _ & _ & _ & _ & _ & (_ & Hnv & _) & _). intros kk Hk.
    replace (x_n c + kk) with (x_n c + Z.of_nat (Z.to_nat kk)) by lia.
    rewrite (Hnv (Z.to_nat kk) ltac:(lia)). discriminate. }
  destruct (dcs2_chain B RLO RHI GOTW GUARD c (x_ly c) S3 W3 (ms_mem msD) mdD 0 HPRE HJ (proj1 HMD) HNV)
    as (ch1 & HCH).
  pose proof (dcs2_split_pre B RLO RHI GOTW GUARD c i (x_ly c) S3 W3 (ms_mem msD) mdD 0 (ms_regs msD)
    SSP HPRE HJ HUN Hi SH4 SH5 SH8) as HSPRE.
  set (s := rs_name sg) in *.
  assert (HSPc : spZ (ms_regs msD) = dc_sp0 c + (dc_s1 c - dc_sp0 c)).
  { unfold spZ. rewrite P2, F2. unfold w64. rewrite unsigned_lit_small by (destruct Hs1 as [E1 | E1]; lia). lia. }
  assert (Ho16 : (dc_s1 c - dc_sp0 c) mod 16 = 0).
  { destruct Hs1 as [E1 | E1]; rewrite E1;
    [replace (dc_sp0 c - 224 - dc_sp0 c) with (-224) by lia | replace (dc_sp0 c - 240 - dc_sp0 c) with (-240) by lia];
    reflexivity. }
  assert (HCH' : achain (x_ly c) (rdW W3 (ms_mem msD)) (dc_sp0 c + (dc_s1 c - dc_sp0 c)) (s0Z (ms_regs msD)) ch1).
  { replace (dc_sp0 c + (dc_s1 c - dc_sp0 c)) with (dc_s1 c) by lia.
    replace (s0Z (ms_regs msD)) with (dc_sp0 c)
      by (unfold s0Z; rewrite P8, F8; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
    exact HCH. }
  assert (P3' : getr (ms_regs msD) 3 = w64 (as_gp B)) by (rewrite P3; exact F3).
  assert (P4' : getr (ms_regs msD) 4 = w64 (as_tp B)) by (rewrite P4; exact F4).
  pose proof pa_B_ok as HBASE. pose proof (pa_base_lo (PL := PL_seg)) as HBLO.
  assert (HRA : YK0s.ret_ok (getr (ms_regs msD) 1)) by (rewrite P1; apply ret_ok_codeptr_v; [lia | reflexivity]).
  assert (HRA4 : 4096 <= bv_unsigned (getr (ms_regs msD) 1)) by (rewrite P1, unsigned_lit_small by lia; lia).
  assert (HNEVS : st_nev S3 + EV_reac_declared_vlan_split <= EV_MAX).
  { unfold EV_reac_declared_vlan_split. unfold EV_reac_segconf_declared in HNEV. lia. }
  assert (HX64 : 0 <= X < 2 ^ 64) by lia.
  assert (HP64 : 0 <= dc_F c + 32 < 2 ^ 64) by lia.
  assert (HV64 : 0 <= dc_F c + 64 < 2 ^ 64) by lia.
  assert (HFP1 : forall a, inFP (split_W (dc_F c + 32) (dc_F c + 64) s) a ->
    dc_F c + 32 <= a < dc_F c + 48 \/ dc_F c + 64 <= a < dc_F c + 66)
    by (intros a Ha; pose proof (dcs2_split_W _ _ _ _ Ha); lia).
  (* 0x8a040: jal reac_declared_vlan_split, through its contract; the return address 0x8a044 = BASE + 21124 *)
  rewrite dcs2_sig.
  eapply SRr_bind.
  { refine (cl_callS_wide B LAWS W3 (ms_regs msD) (ms_mem msD) (Z_to_bv 64 (BASE + AF_reac_declared_vlan_split))
      DC_STK (dc_sp0 c) (dc_FP c) (x_ly c) (x_S c) (x_W c) (x_mem c) (x_md c) [(1, x_fpos c)] (x_ly c)
      S3 mdD 0 DC_STK_SPLIT (split_W (dc_F c + 32) (dc_F c + 64) s) EV_reac_declared_vlan_split
      (dc_s1 c - dc_sp0 c) (getr (ms_regs msD) 1) ch1
      (dcs2_splitQ s (dc_F c + 32) (dc_F c + 64) (x_ly c) S3 W3 (ms_mem msD) (ms_regs msD))
      HJ HSPc Ho16 ltac:(destruct Hs1 as [E1 | E1]; lia) ltac:(lia) ltac:(destruct Hs1 as [E1 | E1]; lia)
      P3' P4' eq_refl HRA HRA4 HCH' _ _ _).
    - intros HPRE1. exact (SPLIT fx (x_ly c) S3 W3 (ms_regs msD) (ms_mem msD) mdD ch1 X
        (dc_F c + 32) 16 (dc_F c + 64) s HPRE1 HRODC P10 HX64 P11 HP64 P12 ltac:(lia) P13 HV64 HSPRE HNEVS).
    - intros a Ha. right; right; right; left. exists 1, (x_fpos c). split; [left; reflexivity|]. left.
      pose proof (HFP1 a Ha). unfold in_zr. cbn [fst snd]. change (frame_addr (x_ly c) 1 (x_fpos c)) with (dc_F c).
      change (fs_frame_bytes 1) with 128. lia.
    - intros ly2' S2' W2' regs2' mem2' md2' _ a Ha Hw _. exfalso. pose proof (HFP1 a Ha). lia. }
  cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HJc4 & HP4 & HK4).
  unfold dcs2_splitQ in HK4. destruct HK4 as (HA0 & HPOST & HKEPT & HNA).
  pose proof (dcs2_un_call B c (x_ly c) S3 ly4 S4 HUN HNA) as HUN4.
  destruct HNA as (HPERM4 & -> & (f4 & HS4eq)).
  change (0 + EV_reac_declared_vlan_split) with 0 in HJ4.
  rewrite P1. change (Z_to_bv 64 (BASE + 21124)) with (Z_to_bv 64 (BASE + DCS2_RET)).
  (* the callee-saved registers after the call *)
  assert (RR : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr (ms_regs msD) r = getr regs3 r ->
    getr regs4 r = getr regs3 r) by (intros r Hr E1; rewrite (dcs2_pres _ _ r HP4 Hr); exact E1).
  assert (G2 : getr regs4 2 = getr regs3 2) by (apply RR; [dcs2_cs | exact P2]).
  assert (G3 : getr regs4 3 = getr regs3 3) by (apply RR; [dcs2_cs | exact P3]).
  assert (G4 : getr regs4 4 = getr regs3 4) by (apply RR; [dcs2_cs | exact P4]).
  assert (G8 : getr regs4 8 = getr regs3 8) by (apply RR; [dcs2_cs | exact P8]).
  assert (G9 : getr regs4 9 = getr regs3 9) by (apply RR; [dcs2_cs | exact P9]).
  assert (G18 : getr regs4 18 = getr regs3 18) by (apply RR; [dcs2_cs | exact P18]).
  assert (G19 : getr regs4 19 = getr regs3 19) by (apply RR; [dcs2_cs | exact P19]).
  assert (G20 : getr regs4 20 = getr regs3 20) by (apply RR; [dcs2_cs | exact P20]).
  assert (G21 : getr regs4 21 = getr regs3 21) by (apply RR; [dcs2_cs | exact P21]).
  assert (G22 : getr regs4 22 = getr regs3 22) by (apply RR; [dcs2_cs | exact P22]).
  assert (G23 : getr regs4 23 = getr regs3 23) by (apply RR; [dcs2_cs | exact P23]).
  assert (G24 : getr regs4 24 = getr regs3 24) by (apply RR; [dcs2_cs | exact P24]).
  assert (G25 : getr regs4 25 = getr regs3 25) by (apply RR; [dcs2_cs | exact P25]).
  assert (G26 : getr regs4 26 = getr regs3 26) by (apply RR; [dcs2_cs | exact P26]).
  assert (G27 : getr regs4 27 = getr regs3 27) by (apply RR; [dcs2_cs | exact P27]).
  (* what split kept: the zones of the cut and the frame's shadow *)
  assert (HSPD : spZ (ms_regs msD) = dc_s1 c) by (rewrite HSPc; lia).
  unfold sa_kept in HKEPT.
  assert (HKZ : forall a, dcs2_Z c ti a -> rdW W4 mem4 a = rdW W3 (ms_mem msD) a).
  { intros a HZa. destruct (dcs2_Z_out B RLO RHI GOTW GUARD c ti (x_ly c) S3 W3 mem3 md3 0 HPRE HJ0 HUN HTI a HZa)
      as (Ha64 & _ & Hnw & Hnp & Hnv).
    apply HKEPT; [exact Ha64 | rewrite HSPD; exact Hnw |].
    intros HE. destruct (dcs2_split_E _ _ _ _ HE) as [HE1 | HE1]; lia. }
  pose proof (dcs2_mem_tr c ti added W3 W4 (ms_mem msD) mem4 HMD HKZ) as HM4.
  assert (HSH4 : forall o, 0 <= o < 16 ->
    rdW W4 mem4 (SB + dc_F c / 8 + o) = rdW W3 (ms_mem msD) (SB + dc_F c / 8 + o)).
  { intros o Ho. destruct (dcs2_sh_out B RLO RHI GOTW GUARD c (x_ly c) S3 W3 mem3 md3 0 HPRE HJ0 HUN o Ho)
      as (Ha64 & Hnw & Hne & _).
    apply HKEPT; [exact Ha64 | rewrite HSPD; exact Hnw | exact (Hne s)]. }
  assert (HEIR : forall v, img_env VAL A_LIM (dcs2_EA regs4 v)) by (intros v; unfold dcs2_EA; apply Eimg_env).
  revert HA0 HPOST. destruct (SegModel.vlan_split s) as [[p v]|] eqn:Hvs; intros HA0 HPOST.
  + (* split gave 1: `beqz a0` at 0x8a044 not taken, KA at pass i *)
    destruct HPOST as (HSTRZ & HVAL).
    pose proof (st_ok_pi_pin_reg' _ _ _ 10%bv 1 (dcs2_seedS W4 mem4 regs4 0) HA0 eq_refl) as HS4.
    lazymatch type of HS4 with st_ok_pi ?a ?b ?c ?ss ?m => let ss' := eval vm_compute in ss in change ss with ss' in HS4 end.
    pose proof (HEIR 0) as HEI4.
    paj_run_to_sh RUNTOP HS4 HJ4 DC_KA.
    { apply (awr_ok_nil SEGS B). }
    dcs2_mdv mdK. dcs2_name HS4 msK.
    pose proof (dcs2_frame_ro _ _ _ _ HF eq_refl) as HEQK. clear HF HFr HG.
    dcs2_rr HS4 (2%bv : bv 5) T2. dcs2_rr HS4 (3%bv : bv 5) T3. dcs2_rr HS4 (4%bv : bv 5) T4.
    dcs2_rr HS4 (8%bv : bv 5) T8. dcs2_rr HS4 (9%bv : bv 5) T9. dcs2_rr HS4 (27%bv : bv 5) T27.
    dcs2_rr HS4 (18%bv : bv 5) T18. dcs2_rr HS4 (19%bv : bv 5) T19. dcs2_rr HS4 (20%bv : bv 5) T20.
    dcs2_rr HS4 (21%bv : bv 5) T21. dcs2_rr HS4 (22%bv : bv 5) T22. dcs2_rr HS4 (23%bv : bv 5) T23.
    dcs2_rr HS4 (24%bv : bv 5) T24. dcs2_rr HS4 (25%bv : bv 5) T25. dcs2_rr HS4 (26%bv : bv 5) T26.
    pmkst HS4.
    assert (HRK : forall a, rdW W4 (ms_mem msK) a = rdW W4 mem4 a)
      by (intros a; exact (dcs2_aview_ext SEGS _ _ _ HEQK a)).
    assert (HMK : dcs2_mem c ti added W4 (ms_mem msK))
      by (apply (dcs2_mem_tr c ti added W4 W4 mem4 _ HM4); intros a _; exact (HRK a)).
    pose proof HMK as (_ & _ & _ & _ & _ & _ & _ & HTABK & HSLK).
    apply (HKA ti added p v (x_ly c) S4 W4 (ms_regs msK) (ms_mem msK) mdK). unfold INV_KA.
    split.
    { apply (dcs2_fi_of B c 0 (x_ly c) S4 W4 (ms_regs msK) (ms_mem msK) mdK ti added HMK HJ4);
        [rewrite T2, G2; exact F2 | rewrite T3, G3; exact F3 | rewrite T4, G4; exact F4 | rewrite T8, G8; exact F8
        | rewrite T9, G9; exact F9 | rewrite T27, G27; exact F27]. }
    split; [exact HUN4|]. split; [exact HTABK|]. split; [exact Hi|]. split; [exact HLOOP|].
    split.
    { unfold dc_lregs. rewrite T24, G24, T22, G22, T25, G25, T23, G23, T20, G20, T19, G19, T26, G26, T21, G21, T18, G18.
      exact (conj R24 (conj R22 (conj R25 (conj R23 (conj R20 (conj R19 (conj R26 (conj R21 R18)))))))). }
    split; [exact HSLK|]. split; [exact Hig|]. split; [exact Hvs|].
    split; [destruct HSTRZ as [Hz Hn0]; split; [intros j Hj; rewrite HRK; exact (Hz j Hj) | exact Hn0]|].
    split; [intros k Hk; rewrite HRK; exact (HVAL k Hk)|].
    split; [rewrite HRK, HSH4 by lia; exact SH4|].
    split; [rewrite HRK, HSH4 by lia; exact SH5|].
    rewrite HRK, HSH4 by lia; exact SH8.
  + (* split gave 0: `beqz a0` to 0x8a09c, a3 := 80(s1), a4 := 32, the three shadow bytes := 0xf8, KT at pass i *)
    clear HPOST.
    pose proof HJ4 as (HAR4 & _ & _ & _ & _ & Hfrs4 & _).
    assert (Hfin4 : In (1, x_fpos c) (frames S4)) by (rewrite Hfrs4; left; reflexivity).
    destruct (al_frames _ _ LAWS _ _ _ _ _ 1 (x_fpos c) HAR4 Hfin4) as (_ & _ & _ & HFS4).
    change (frame_addr (x_ly c) 1 (x_fpos c)) with (dc_F c) in HFS4. change (fs_frame_bytes 1 / 8) with 16 in HFS4.
    assert (HPS4 : forall o, 0 <= o < 16 -> apresent (w_H W4) mem4 (SB + dc_F c / 8 + o)).
    { intros o Ho. replace (SB + dc_F c / 8 + o) with (shadow_addr (dc_F c) + o)
        by (unfold shadow_addr; rewrite <- SB_SHADOW_OFF; lia).
      exact (proj1 (HFS4 o Ho)). }
    pose proof HM4 as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & HSL80 & _)).
    assert (Q9 : getr regs4 9 = w64 (dc_s1 c)) by (rewrite G9; exact F9).
    assert (Q27 : getr regs4 27 = w64 (SB + dc_F c / 8)) by (rewrite G27; exact F27).
    pose proof (dcs2_seedN W4 mem4 regs4 (dc_s1 c) (dc_F c) (2 ^ 64 - 1 - x_c c) Q9 Q27
      ltac:(destruct Hs1 as [E1 | E1]; lia) ltac:(destruct Hs1 as [E1 | E1]; lia) Hs1m ltac:(lia) ltac:(lia)
      HSL80 HPS4) as HS4.
    pose proof (st_ok_pi_pin_reg' _ _ _ 10%bv 0 HS4 HA0 eq_refl) as HS5. clear HS4.
    lazymatch type of HS5 with st_ok_pi ?a ?b ?c ?ss ?m => let ss' := eval vm_compute in ss in change ss with ss' in HS5 end.
    pose proof (HEIR (2 ^ 64 - 1 - x_c c)) as HEI5.
    assert (B27' : bv_unsigned (ew (dcs2_EA regs4 (2 ^ 64 - 1 - x_c c)) 27) = SB + dc_F c / 8)
      by (rewrite (dcs2_EA_reg _ _ 27 27%bv eq_refl), Q27; apply unsigned_lit_small; unfold SB; lia).
    paj_run_to_sh RUNTOP HS5 HJ4 DC_KT.
    { lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
        let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
      apply awr_ok_cons_ro; [cbn; lia|].
      eapply awr_ok_cons_gen with (n := 27%nat) (b := SB + dc_F c / 8); [reflexivity | exact B27' | |].
      { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left. exists 1, (x_fpos c).
        split; [left; reflexivity|]. right. unfold in_zr, shadow_addr. cbn [fst snd].
        change (fs_frame_bytes 1 / 8) with 16. change (frame_addr (x_ly c) 1 (x_fpos c)) with (dc_F c).
        unfold SB, SHADOW_OFF in *. lia. }
      apply awr_ok_nil. }
    dcs2_mdv mdK. dcs2_name HS5 msK.
    pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun a => SB + dc_F c / 8 <= a < SB + dc_F c / 8 + 16) HFr
      ltac:(intros b wlo whi a Hin' Hrr; vm_compute in Hin';
        repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?B27' in Hrr; cbv beta; lia |]);
        destruct Hin')) as UNK.
    clear HF HFr HG.
    dcs2_rr HS5 (2%bv : bv 5) T2. dcs2_rr HS5 (3%bv : bv 5) T3. dcs2_rr HS5 (4%bv : bv 5) T4.
    dcs2_rr HS5 (8%bv : bv 5) T8. dcs2_rr HS5 (9%bv : bv 5) T9. dcs2_rr HS5 (27%bv : bv 5) T27.
    dcs2_rr HS5 (13%bv : bv 5) T13. dcs2_rr HS5 (14%bv : bv 5) T14.
    dcs2_rr HS5 (18%bv : bv 5) T18. dcs2_rr HS5 (19%bv : bv 5) T19. dcs2_rr HS5 (20%bv : bv 5) T20.
    dcs2_rr HS5 (21%bv : bv 5) T21. dcs2_rr HS5 (22%bv : bv 5) T22. dcs2_rr HS5 (23%bv : bv 5) T23.
    dcs2_rr HS5 (24%bv : bv 5) T24. dcs2_rr HS5 (25%bv : bv 5) T25. dcs2_rr HS5 (26%bv : bv 5) T26.
    rewrite dcs2_EA_x32 in T13.
    pmkst HS5.
    assert (HMK : dcs2_mem c ti added W4 (ms_mem msK)).
    { apply (dcs2_mem_tr c ti added W4 W4 mem4 _ HM4). intros a HZa.
      destruct (dcs2_Z_out B RLO RHI GOTW GUARD c ti (x_ly c) S3 W3 mem3 md3 0 HPRE HJ0 HUN HTI a HZa)
        as (Ha64 & Hns & _).
      exact (UNK a Ha64 Hns). }
    pose proof HMK as (_ & _ & _ & _ & _ & _ & _ & HTABK & HSLK).
    apply (HKT ti added (x_ly c) S4 W4 (ms_regs msK) (ms_mem msK) mdK). unfold INV_KT.
    split.
    { apply (dcs2_fi_of B c 0 (x_ly c) S4 W4 (ms_regs msK) (ms_mem msK) mdK ti added HMK HJ4);
        [rewrite T2, G2; exact F2 | rewrite T3, G3; exact F3 | rewrite T4, G4; exact F4 | rewrite T8, G8; exact F8
        | rewrite T9, G9; exact F9 | rewrite T27, G27; exact F27]. }
    split; [exact HUN4|]. split; [exact HTABK|]. split; [exact Hi|].
    split.
    { destruct HLOOP as [HL1 HL2]. split; [|lia].
      rewrite <- (dcl_go_nosplit (dc_segs c) i ti (x_max c) added Hi Hig Hvs). exact HL1. }
    split.
    { unfold dc_lregs. rewrite T24, G24, T22, G22, T25, G25, T23, G23, T20, G20, T19, G19, T26, G26, T21, G21, T18, G18.
      exact (conj R24 (conj R22 (conj R25 (conj R23 (conj R20 (conj R19 (conj R26 (conj R21 R18)))))))). }
    split; [unfold dc_aregs; split; [exact T13 | exact T14] | exact HSLK].
Qed.

End e.
End f.
End d.
