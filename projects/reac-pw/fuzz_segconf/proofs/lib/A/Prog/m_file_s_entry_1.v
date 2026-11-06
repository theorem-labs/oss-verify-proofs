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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 398 of its 473 lines of code are new or changed and 378 lines of the source are left out. *)
(* S_MF_ENTRY, part 1 (the entry seed); the top lemma s_mf_entry is in m_file_s_entry.v. The first segment of m_file's walk on fuzz_segconf.asan (image A, m_file at 0x85ebc), from the
   entry to the head 0x860d0 or to the release 0x86e70 (lib/A/Prog/m_file_m.v's MF_ENTRY_stmt from MF_HEAD_F and
   MF_EXIT_F). 141 instructions, two calls and two instrumented checks (the G2 walk owner's guide MF-CUTS-A.md section 4):

     0x85ebc-0x85f28  the prologue: the 288-byte frame, the probe store at sp0 - 288, ra and s0 .. s11 at
                      sp0 - 104 .. sp0 - 8, s0 = sp0, the realignment `andi sp,sp,-32` (s1), the arguments into
                      s5 / s11 / s4, the shadow base from the GOT word (as_got_shadow B), and the read of the
                      use-after-return option cell (as_uar_cell B, AR's constant 1), whose `beqz` the executor
                      decides, so the real-stack fallback 0x85f4c-0x85f64 is dead and is never walked;
     0x85f30          the class-1 side-stack frame request (a0 = 0x80), stepped with aj_stack_malloc_atS;
     0x85f68-0x85ff0  the frame header (FB + 0 = 0x41b58ab3, + 8 = 0x1d8f6, + 16 = 0x85ebc) and the 16 shadow
                      bytes (0xf1 x 4, 0xf8 x 8 for low.i, 0xf3 x 4);
     0x85ff4          `bnez s4`: the label or the literal "reac-pw.conf" (the inner cut ENT_LBL,
                      m_file_s_entry_c.v; m_file_s_entry_3.v walks the two arms to the call separately);
     0x86014          snprintf(c->reading, 96, "%s", that pointer), the shared contract
                      RtPFCmd.asnprintf_sh at the trampoline, stepped with aj_art_own_atF / srr_after_artF;
     0x86018-0x86048  c->gen++ (the checked load 0x86028, the store 0x86048 has no check);
     0x8604c-0x86060  *text: the checked load 0x86054 and `beqz` to the release 0x86e70 (MF_EXIT_stmt);
     0x86064-0x860cc  the set-up of the spill slots (mf_cells with cur = None, s6 = 0) and the head 0x860d0
                      (MF_HEAD_stmt at any bound above the text's length).

   The model: m_file mc s lab = fst (m_lines (mf_c1 mc lab, None) 0 (lines s)) (m_file_s_entry_m.v), with
   mf_c1 the entry model after the two writes this segment makes.
   A lane of the G2 walk owner. Closed against G2 FINAL (the image-A owner's contracts 6f783602b5e3). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaArt PaArtOwn PaNoChain PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtPFShared RtPFCmd RtFormat.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_s_entry_m m_file_s_entry_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ===================================== the program points ===================================== *)
(* listing offsets, = AF_m_file + (pc - 0x85ebc) *)
Definition MF_SM : Z := AF_m_file + 0x074.      (* 0x85f30, the class-1 side-stack frame request *)
Definition MF_RET_SM : Z := AF_m_file + 0x078.  (* 0x85f34, after it *)
Definition MF_JOIN : Z := AF_m_file + 0x144.    (* 0x86000, where the two label arms join *)
Definition MF_SNP : Z := AF_m_file + 0x158.     (* 0x86014, the snprintf call *)
Definition MF_RET_SNP : Z := AF_m_file + 0x15c. (* 0x86018, after it *)

(* the objects the code forms in this segment (SegAddr.seg_objs; the pairs are SegList's PHi / PAddHi):
   13 = "reac-pw.conf" 0x210a0 (0x85ff8), 14 = "%s" 0x21080 (0x86000), 15 = m_key.words 0xa1880 (0x860a0),
   10 = the frame descriptor 0x1d8f6 (0x85f74), 11 = m_file itself 0x85ebc (0x85f78) *)
Definition MF_OBJ_BASE : nat := 13.
Definition MF_OBJ_FS : nat := 14.
Definition MF_OBJ_WORDS : nat := 15.

(* ===================================== the entry state ===================================== *)
(* the atoms over the registers: 32 the shadow base, 33 s1 = (sp0 - 288) & -32, 34 the use-after-return cell,
   35 c->gen at the entry, 36 the first byte of the text and its NUL, 37 the pointer snprintf prints *)
Definition MfBx : sv := SOff 32 0.
Definition mf_extra (sp0 ucell gen0 b0 lptr : Z) : list word :=
map (Z_to_bv 64) [SB; sp0 - 288 - (sp0 - 288) mod 32; ucell; gen0; b0; lptr].
(* the first byte of the text's bytes and its NUL *)
Definition mf_b0 (s : list Z) : Z := nth 0 (s ++ [0]) 0.
(* what the label becomes at the snprintf call: the label, or the literal "reac-pw.conf" *)
Definition mf_lptr (lp : Z) (lab : option (list Z)) : Z :=
match lab with Some _ => lp | None => seg_litA_fz S_base end.

(* the regions of the entry state: the probe word and the saved registers of the prologue, the spill slots
   above s1, c->gen, the text's first byte, the shadow base's GOT word and cell, the use-after-return GOT word
   and cell *)
Definition mf_r_probe : YP09.region := YP09.mkRegion (Some 2%nat) (-288) (-280) (-288) (-280) [].
Definition mf_r_saves : YP09.region := YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 [].
Definition mf_r_slots : YP09.region := YP09.mkRegion (Some 33%nat) 24 184 24 184 [].
Definition mf_r_gen : YP09.region :=
YP09.mkRegion (Some 10%nat) seg_spec.MC_GEN (seg_spec.MC_GEN + 4) 0 0
[YP09.mkChunk seg_spec.MC_GEN (CVal 4 (SOff 35 0))].
Definition mf_r_txt : YP09.region := YP09.mkRegion (Some 11%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 36 0))].
Definition mf_regions0 : smem :=
[mf_r_probe; mf_r_saves; mf_r_slots; mf_r_gen; mf_r_txt; got_regionP; bcell_regionP 32;
 uar_got_regionP 34; uar_cell_regionP 34].
Definition mf_facts0 : facts :=
mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, PTR 4); (11%nat, PTR 0);
          (32%nat, mkAF SB SB 0); (33%nat, mkAF (2 ^ 46) (2 ^ 47) 5);
          (34%nat, mkAF 65536 6295552 2); (35%nat, mkAF 0 (2 ^ 31) 0); (36%nat, mkAF 0 256 0) ] []
        [ (SAlu ALU_AND (SOff 2 (-288)) (SLit (-32)), SOff 33 0) ].
Definition ss_mf0 : sstate := mkSS AF_m_file sr_atoms mf_regions0 None mf_facts0.
(* the shadow knowledge of the two checks: c->gen's granule and the text's first byte *)
Definition mf_SH0 : list shent := [ mkSHE 10 seg_spec.MC_GEN (seg_spec.MC_GEN + 8); mkSHE 11 0 1 ].
(* an opaque wrapper for disjunctive address facts: lia does not case-split under it (numberE.v:115) *)
Definition mf_nam (P : Prop) : Prop := P.

(* normalise a symbolic state after an edit (check_reply_s1.v:75) *)
(* the disjointness of a new region from the state's, over the atoms' values (check_reply_s1.v:98-101) *)
Ltac mfdj h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 :=
  lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
    let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
  cbn [all_disjoint]; unfold extent_disjoint;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  repeat match goal with U : bv_unsigned (ew ?Ey ?n) = _ |- context [bv_unsigned (ew ?Ey ?n)] => rewrite U end;
  revert h1 h2 h3 h4 h5 h6 h7 h8 h9 h10; clear;
  unfold mf_nam, seg_spec.MC_GEN, seg_spec.SEG_M_SIZE, mf_s1, SB, SHADOW_OFF; intros;
  repeat split; lia.
Ltac mfnorm HS := lazymatch type of HS with st_ok_pi ?a ?b ?c ?ss ?ms => let v := eval vm_compute in ss in change ss with v in HS end.

(* ===================================== small readers' lemmas ===================================== *)
(* a value the reader shows is a value of the restricted memory (check_reply_s1.v:62-70 for aval_mem) *)
Lemma mf_val_mem_of_sa : forall segs H (mem : word -> option byte) a n v,
sa_val (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; [|discriminate].
cbn in Hv. injection Hv as Hv. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
try unfold YG0f.le_byte in *; try unfold YO0f.le_byte in *. rewrite <- Hv.
symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.
(* every byte the ASan reader shows is a byte *)
Lemma mf_aview_byte : forall segs H (mem : word -> option byte) a x,
aview segs H mem a = Some x -> 0 <= x < 256.
Proof.
intros segs H mem a x Hx. unfold aview in Hx.
destruct (mbyte segs (mrestrict H mem) a) as [b|]; [|discriminate].
cbn in Hx. injection Hx as <-. pose proof (bv_unsigned_in_range 8 b).
change (bv_modulus 8) with 256 in *. lia.
Qed.
(* the first byte of a C string and its NUL, as a one-byte value of the reader *)
Lemma mf_sa_val_b0 : forall segs H (mem : word -> option byte) p s,
sa_strz (aview segs H mem) p s -> sa_val (aview segs H mem) p 1%nat (mf_b0 s).
Proof.
intros segs H mem p s Hs k Hk. assert (k = 0%nat) by lia. subst k.
pose proof (proj1 Hs 0%nat ltac:(rewrite length_app; cbn [length]; lia)) as H0.
rewrite Z.add_0_r in H0 |- *. unfold mf_b0.
pose proof (mf_aview_byte segs H mem p _ H0) as Hr.
replace (le_byte (nth 0 (s ++ [0]) 0) 1 0) with (nth 0 (s ++ [0]) 0); [exact H0|].
unfold le_byte. cbn [Z.of_nat]. replace (8 * 0) with 0 by lia. rewrite Z.shiftr_0_r.
replace (8 * 1) with 8 by lia. change (2 ^ 8) with 256.
rewrite Z.mod_mod by lia. symmetry. apply Z.mod_small. lia.
Qed.

(* ===================== reading the prologue's stores back from the state ===================== *)
(* the frame's sixteen shadow bytes, as the run 0x85fa4-0x85fd8 left them: 0xf1 x 4, 0xf8 x 8 (low.i), 0xf3 x 4 *)
Definition mf_shadow_chunks : list YP09.chunk :=
[YP09.mkChunk 11 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 10 (CVal 1 (SLit 18446744073709551608));
 YP09.mkChunk 9 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 8 (CVal 1 (SLit 18446744073709551608));
 YP09.mkChunk 7 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 6 (CVal 1 (SLit 18446744073709551608));
 YP09.mkChunk 5 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 4 (CVal 1 (SLit 18446744073709551608));
 YP09.mkChunk 15 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 14 (CVal 1 (SLit 18446744073709551603));
 YP09.mkChunk 13 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 12 (CVal 1 (SLit 18446744073709551603));
 YP09.mkChunk 3 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 2 (CVal 1 (SLit 18446744073709551601));
 YP09.mkChunk 1 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 0 (CVal 1 (SLit 18446744073709551601))].
(* the entry's ra and s0 .. s11 below sp0, as the prologue 0x85ec4-0x85ef4 left them *)
Definition mf_saves_chunks : list YP09.chunk :=
[YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0));
 YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0));
 YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
 YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
 YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
 YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
 YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].

Section r. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section r1.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
(* low.i's eight shadow bytes 0xf8, read back from the frame's shadow region *)
Lemma mf_low_bytes : forall (E : env) m (b : Z),
region_ok SEGS E m (YP09.mkRegion (Some 57%nat) 0 16 0 16 mf_shadow_chunks) ->
bv_unsigned (ew E 57) = b ->
forall i, 4 <= i < 12 -> val_mem SEGS m (b + i) 1%nat 248.
Proof.
intros E m b RG U i Hi.
assert (HC : forall od, In od [4; 5; 6; 7; 8; 9; 10; 11] ->
  val_mem SEGS m (b + od) 1%nat 248).
{ intros od Hod.
  pose proof (field_of_region_any E m 57%nat b mf_shadow_chunks 0 16 0 16 od 1
                (SLit 18446744073709551608) RG U
                ltac:(unfold mf_shadow_chunks; cbn [In] in Hod |- *;
                      repeat (destruct Hod as [<- | Hod]; [tauto|]); destruct Hod)
                ltac:(cbn; lia)) as HV.
  cbn [sv_denot N.to_nat Pos.to_nat] in HV.
  replace (bv_unsigned (Z_to_bv 64 18446744073709551608) mod 2 ^ (8 * Z.of_N 1)) with 248 in HV
    by (vm_compute; reflexivity).
  exact HV. }
apply HC. cbn [In].
destruct (Z.eq_dec i 4) as [->|]; [tauto|]. destruct (Z.eq_dec i 5) as [->|]; [tauto|].
destruct (Z.eq_dec i 6) as [->|]; [tauto|]. destruct (Z.eq_dec i 7) as [->|]; [tauto|].
destruct (Z.eq_dec i 8) as [->|]; [tauto|]. destruct (Z.eq_dec i 9) as [->|]; [tauto|].
destruct (Z.eq_dec i 10) as [->|]; [tauto|]. destruct (Z.eq_dec i 11) as [->|]; [tauto|]. lia.
Qed.
(* the entry's callee-saved registers, read back from the prologue's region *)
Lemma mf_saved_bytes : forall (E : env) m (sp0 : Z) (regs : bvmap 5 word),
region_ok SEGS E m (YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 mf_saves_chunks) ->
bv_unsigned (ew E 2) = sp0 ->
(forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) ->
mf_saved m sp0 regs.
Proof.
intros E m sp0 regs RG U ER j r Hj.
assert (HC : forall od n (rr : bv 5), In (YP09.mkChunk od (CVal 8 (SOff n 0))) mf_saves_chunks ->
  (n < 32)%nat -> Z.of_nat n = bv_unsigned rr ->
  val_mem SEGS m (sp0 + od) 8%nat (bv_unsigned (getr regs rr))).
{ intros od n rr Hin Hn Hr.
  pose proof (field_of_region_any E m 2%nat sp0 mf_saves_chunks (-104) 0 (-104) 0 od 8
                (SOff n 0) RG U Hin ltac:(cbn; lia)) as HV.
  cbn [sv_denot] in HV. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (ER n rr Hn Hr) in HV.
  rewrite Z.mod_small in HV
    by (pose proof (bv_unsigned_in_range 64 (getr regs rr)); unfold bv_modulus in *; cbn in *; lia).
  exact HV. }
do 13 (destruct j as [|j];
  [cbn in Hj; injection Hj as <-;
   lazymatch goal with
   |- val_mem _ _ (sp0 - 8 - 8 * Z.of_nat ?jj) 8 (bv_unsigned (getr _ (Z_to_bv 5 ?rz))) =>
     let od := eval vm_compute in (-8 - 8 * Z.of_nat jj) in
     let n := eval vm_compute in (Z.to_nat rz) in
     replace (sp0 - 8 - 8 * Z.of_nat jj) with (sp0 + od) by (cbn; lia);
     apply (HC od n (Z_to_bv 5 rz));
       [unfold mf_saves_chunks; cbn [In]; tauto | cbn; lia | vm_compute; reflexivity]
   end |]).
destruct j; cbn in Hj; discriminate Hj.
Qed.
(* the frame's flag pointer at FB + 120, kept from the frame request across a run that leaves its word alone *)
Lemma mf_flag_keep : forall (W : world SEGS) m2 m3 (F FL : Z),
(forall a, 0 <= a < 2 ^ 64 -> F + 120 <= a < F + 128 -> aview SEGS (w_H W) m3 a = aview SEGS (w_H W) m2 a) ->
0 <= F -> F + 128 <= 2 ^ 64 ->
rdword (aview SEGS (w_H W) m2) (F + 128 - 8) = Some FL ->
val_mem SEGS (mrestrict (w_H W) m3) (F + 120) 8 FL.
Proof.
intros W m2 m3 F FL K H0 H1 HR.
pose proof (val_mem_of_rdword SEGS (w_H W) m2 _ _ HR) as HV.
replace (F + 128 - 8) with (F + 120) in HV by lia.
apply (val_mem_moved SEGS (w_H W) (w_H W) m2 m3 (F + 120) (F + 120) 8 FL); [|exact HV].
intros k Hk. apply K; lia.
Qed.
End r1.
End r.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
(* the environment of the entry state *)
Definition MfE (regs : bvmap 5 word) (ucell gen0 b0 lptr : Z) : env :=
Eimg (Ereg regs (mf_extra (spZ regs) ucell gen0 b0 lptr)).
Section e.
Variable B : asyms.
(* the record hypotheses the owner's list fixes for every m_file segment *)
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SSP : forall ly S (W : world SEGS) mem md,
AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) SegInstA.gotwA SegInstA.guardA.
(* the class-1 side-stack frame this function takes at 0x85f30 (G2-COMMON) *)
Hypothesis ASM : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 1.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ML : model_laws (as_universe B).
(* the snprintf wrapper (interceptor row 4) at the listing's trampoline and image A's cells *)
Hypothesis ASNP : forall fx0 : YK11.FPState,
@RtFormat.asnprintf_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_snprintf)
  SegInstA.gotwA SegInstA.guardA.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS. Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let errno_low := pal_env B TL.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.

(* the values of the three objects this segment forms *)
Lemma mf_val_base : VAL (A_OBJ MF_OBJ_BASE) = seg_litA_fz S_base.
Proof. rewrite (VOBJS MF_OBJ_BASE ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma mf_val_fs : VAL (A_OBJ MF_OBJ_FS) = seg_litA_fz F_s.
Proof. rewrite (VOBJS MF_OBJ_FS ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.
Lemma mf_val_words : VAL (A_OBJ MF_OBJ_WORDS) = SegInstA.wordsA.
Proof. rewrite (VOBJS MF_OBJ_WORDS ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

(* the arithmetic of the realignment `andi sp,sp,-32` at 0x85efc (check_reply_k.v:94-102) *)
Lemma mf_land_m32 : forall x, 0 <= x < 2 ^ 64 -> Z.land x (2 ^ 64 - 32) = x - x mod 32.
Proof.
intros x Hx.
replace (2 ^ 64 - 32) with (Z.land (Z.ones 64) (Z.lnot (Z.ones 5))) by reflexivity.
rewrite Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia.
rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32.
pose proof (Z.div_mod x 32 ltac:(lia)). lia.
Qed.
(* s1 = (sp0 - 288) & -32 lies 0 or 16 bytes below sp0 - 288 (the entry sp is 16-aligned) *)
Lemma mf_s1_bounds : forall sp0, sp0 mod 16 = 0 ->
mf_s1 sp0 = sp0 - 288 - (sp0 - 288) mod 32 /\ ((sp0 - 288) mod 32 = 0 \/ (sp0 - 288) mod 32 = 16) /\
mf_s1 sp0 mod 32 = 0 /\ sp0 - 304 <= mf_s1 sp0 <= sp0 - 288.
Proof.
intros sp0 H16. unfold mf_s1.
pose proof (Z.mod_pos_bound (sp0 - 288) 32 ltac:(lia)) as Hb.
pose proof (Z.div_mod (sp0 - 288) 32 ltac:(lia)) as Hd.
pose proof (Z.div_mod sp0 16 ltac:(lia)) as Hd16.
assert (Hm : (sp0 - 288) mod 16 = 0)
  by (replace (sp0 - 288) with (sp0 + (-18) * 16) by lia; rewrite Z_mod_plus_full; exact H16).
pose proof (Z.div_mod ((sp0 - 288) mod 32) 16 ltac:(lia)) as Hd2.
assert (H2 : (sp0 - 288) mod 32 mod 16 = 0)
  by (rewrite <- Znumtheory.Zmod_div_mod with (m := 32); [exact Hm | lia | lia | exists 2; reflexivity]).
split; [reflexivity|]. split; [lia|].
split; [replace (sp0 - 288 - (sp0 - 288) mod 32) with (((sp0 - 288) / 32) * 32) by lia; apply Z_mod_mult | lia].
Qed.

(* ===================================== the entry state ===================================== *)
(* The symbolic state at 0x85ebc: the registers as themselves, the prologue's two stack ranges and the spill
   slots above s1 writable, c->gen and the text's first byte readable, the shadow base's and the
   use-after-return flag's GOT words and cells; and the shadow knowledge of this segment's two checks
   (c->gen's granule 0x86028 and the text's first byte 0x86054), both from the contract's sa_addr. *)
Lemma mf_entry_seed : forall v,
mf_cx B v ->
sa_val (rdW (mv_W v) (mv_mem v)) (mv_c v + seg_spec.MC_GEN) 4%nat (mc_gen (mv_mc v)) ->
0 <= mc_gen (mv_mc v) ->
0 <= mf_lptr (mv_lp v) (mv_lab v) < 2 ^ 64 ->
st_ok_pi SEGS VAL
  (MfE (mv_regs v) (as_uar_cell B) (mc_gen (mv_mc v)) (mf_b0 (mv_s v)) (mf_lptr (mv_lp v) (mv_lab v))) ss_mf0
  (restrict (w_H (mv_W v)) (mkst (mv_regs v) (Z_to_bv 64 (BASE + AF_m_file)) (mv_mem v) (seg_rom SEGS)))
/\ sh_ok SEGS MfBx mf_SH0
     (MfE (mv_regs v) (as_uar_cell B) (mc_gen (mv_mc v)) (mf_b0 (mv_s v)) (mf_lptr (mv_lp v) (mv_lab v)))
     (mrestrict (w_H (mv_W v)) (mv_mem v))
/\ (let E := MfE (mv_regs v) (as_uar_cell B) (mc_gen (mv_mc v)) (mf_b0 (mv_s v)) (mf_lptr (mv_lp v) (mv_lab v)) in
    bv_unsigned (ew E 2) = spZ (mv_regs v) /\ bv_unsigned (ew E 33) = mf_s1 (spZ (mv_regs v)) /\
    bv_unsigned (ew E 10) = mv_c v /\ bv_unsigned (ew E 11) = mv_t v /\
    bv_unsigned (ew E 34) = as_uar_cell B /\ bv_unsigned (ew E 35) = mc_gen (mv_mc v) /\
    bv_unsigned (ew E 36) = mf_b0 (mv_s v) /\ bv_unsigned (ew E 37) = mf_lptr (mv_lp v) (mv_lab v) /\
    U E MfBx = SHADOW_OFF /\ ew E 32 = Z_to_bv 64 SB).
Proof.
intros v CX HGEN HGEN0 HLP.
destruct v as [ly S W regs mem md ch c t lp mc s lab]. unfold mf_cx in CX.
cbn [mv_ly mv_S mv_W mv_regs mv_mem mv_md mv_ch mv_c mv_t mv_lp mv_mc mv_s mv_lab] in *.
destruct CX as (HPRE & HROOM & HROD & HLIT & HWD & HRL & HCAT & HSSPv & H10 & Hc64 & H11 & Ht64 & H12 & Hlp64
  & HMP & HEV).
destruct HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HMP as (Hc0 & Hc16 & HMC & HCH & HCA & HCT & Hgenb & Hrefb & Hovfb & Ht0 & HTS & Hslen & HTH & HTA
  & HTM & HTD & HOS & HLAB).
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity.
(* the premises this seed does not read: lia's cost grows with the context (AWALK-FORM 5.2) *)
clear HROOM HROD HLIT HWD HRL HCAT HSSPv HEV HMC HCT HTM Hrefb Hovfb Hslen HOS HLAB Hch HQT.
(* where c and t lie *)
destruct HCH as (bc & mcn & Hbcin & Hbclo & Hbchi).
destruct (al_blocks _ _ LAWS ly S W mem md bc mcn HAR Hbcin) as (Hbc16 & Hbc4096 & Hbcceil & Hbcapp & Hbcpres & _ & Hbcn).
pose proof (blk_off_imgP B ly S W mem md bc mcn HAR Hbcin) as Hbcimg.
pose proof (req_size_pos mcn ltac:(lia)) as [Hrq1 Hrq2].
destruct HTH as (bt & mtn & Hbtin & Hbtlo & Hbthi).
destruct (al_blocks _ _ LAWS ly S W mem md bt mtn HAR Hbtin) as (Hbt16 & Hbt4096 & Hbtceil & Hbtapp & Hbtpres & _ & Hbtn).
pose proof (blk_off_imgP B ly S W mem md bt mtn HAR Hbtin) as Hbtimg.
pose proof (req_size_pos mtn ltac:(lia)) as [Hrt1 Hrt2].
unfold in_app in Hbcapp, Hbtapp. unfold off_img in Hbcimg, Hbtimg. unfold kImgEnd in *.
(* lia's cost grows with every disjunction in the context (AWALK-FORM 5.2): the disjunctive address facts go
   under the opaque mf_nam at once, and only the steps that need them unfold it *)
assert (HcA : 4096 <= c /\ c + 9236 <= alloc_ceiling) by (unfold seg_spec.SEG_M_SIZE in *; lia).
assert (HtA : 4096 <= t /\ t + Z.of_nat (length s) + 1 <= alloc_ceiling) by lia.
assert (ZCi : mf_nam (c + 9236 <= 65536 \/ 6295552 <= c)) by (unfold mf_nam, seg_spec.SEG_M_SIZE in *; lia).
assert (ZTi : mf_nam (t + Z.of_nat (length s) + 1 <= 65536 \/ 6295552 <= t)) by (unfold mf_nam; lia).
assert (ZCa : mf_nam (c + 9236 <= 0x7fff7000 \/ 0x10007fff8000 <= c))
  by (unfold mf_nam, seg_spec.SEG_M_SIZE, kLowShadowBeg, kHighMemBeg in *; lia).
assert (ZTa : mf_nam (t + Z.of_nat (length s) + 1 <= 0x7fff7000 \/ 0x10007fff8000 <= t))
  by (unfold mf_nam, kLowShadowBeg, kHighMemBeg in *; lia).
assert (ZCT : mf_nam (t + 1 <= c \/ c + 9236 <= t)).
{ unfold mf_nam, sa_disj, seg_spec.cstr_span, seg_spec.SEG_M_SIZE in *.
  pose proof (Z.mod_pos_bound (- (t + Z.of_nat (length s) + 1)) 8 ltac:(lia)). lia. }
assert (HbcP : forall a, c <= a < c + 9236 -> apresent (w_H W) mem a)
  by (intros a Ha; exact (proj1 (Hbcpres a ltac:(unfold seg_spec.SEG_M_SIZE in *; lia)))).
clear Hbcimg Hbtimg Hbcapp Hbtapp HTD Hbcin Hbtin Hbc16 Hbt16 Hbc4096 Hbt4096 Hbcceil Hbtceil Hbcn Hbtn Hrq1 Hrq2
  Hrt1 Hrt2 Hbtpres Hbcpres Hbclo Hbchi Hbtlo Hbthi.
(* the use-after-return flag and the shadow cells *)
destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kgu).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite (palf_got_uar B TLF) in Kgu.
pose proof (palf_uar_img B TLF) as Huar. pose proof (palf_uar_al B TLF) as Huar4.
pose proof (pa_obj_img 12 ltac:(lia)) as HcellR.
pose proof (pa_obj_img 0 ltac:(lia)) as HgotR. pose proof (pa_obj_img 1 ltac:(lia)) as HguR.
pose proof (palf_sep B TLF) as Hsep. pose proof pa_B_ok as HBASE.
cbn [zseps zseps_from fst snd] in Hsep. lazymatch type of Hsep with ?T => change (mf_nam T) in Hsep end.
unfold kImgEnd in Huar, HcellR, HgotR, HguR.
(* s1 *)
destruct (mf_s1_bounds (spZ regs) Hal16) as (Hs1e & _ & Hs1a & Hs1b).
rewrite restrict_mkst_fx.
set (sp0 := spZ regs) in *.
set (E := MfE regs (as_uar_cell B) (mc_gen mc) (mf_b0 s) (mf_lptr lp lab)).
assert (EL : forall n, (n < A_TEXT)%nat ->
  ew E n = ew (Ereg regs (mf_extra sp0 (as_uar_cell B) (mc_gen mc) (mf_b0 s) (mf_lptr lp lab))) n)
  by (intros n Hn; subst E; unfold MfE; apply Eimg_low; exact Hn).
assert (EX : forall j, (j < 6)%nat ->
  ew E (32 + j) = nth j (mf_extra sp0 (as_uar_cell B) (mc_gen mc) (mf_b0 s) (mf_lptr lp lab)) (Z_to_bv 64 0))
  by (intros j Hj; rewrite EL by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
pose proof (EX 4%nat ltac:(lia)) as E36. pose proof (EX 5%nat ltac:(lia)) as E37.
cbn [Nat.add nth mf_extra map] in E32, E33, E34, E35, E36, E37.
assert (E2 : ew E 2 = getr regs 2)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 c)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 t)
  by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E0o : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
  by (subst E; unfold MfE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E1o : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
  by (subst E; unfold MfE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E12o : ew E (A_OBJ 12) = Z_to_bv 64 (VAL (A_OBJ 12)))
  by (subst E; unfold MfE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = sp0) by (rewrite E2; reflexivity).
assert (Uc : bv_unsigned (ew E 10) = c) by (rewrite E10; apply unsigned_lit_small; lia).
assert (Ut : bv_unsigned (ew E 11) = t) by (rewrite E11; apply unsigned_lit_small; lia).
assert (USB : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (Us1 : bv_unsigned (ew E 33) = mf_s1 sp0)
  by (rewrite E33; apply unsigned_lit_small; unfold mf_s1; lia).
assert (Uuc : bv_unsigned (ew E 34) = as_uar_cell B) by (rewrite E34; apply unsigned_lit_small; lia).
assert (Ugen : bv_unsigned (ew E 35) = mc_gen mc) by (rewrite E35; apply unsigned_lit_small; lia).
assert (Hb0 : 0 <= mf_b0 s < 256).
{ unfold mf_b0. destruct HTS as [HTZ _].
  pose proof (proj1 HTZ 0%nat ltac:(rewrite length_app; cbn [length]; lia)) as H0.
  rewrite Z.add_0_r in H0. exact (mf_aview_byte SEGS (w_H W) mem t _ H0). }
assert (Ub0 : bv_unsigned (ew E 36) = mf_b0 s) by (rewrite E36; apply unsigned_lit_small; lia).
assert (UBx : U E MfBx = SHADOW_OFF).
{ unfold MfBx. rewrite U_SOff, E32, Z.add_0_r, unsigned_lit_small by (unfold SB; lia).
  rewrite zcanon_id by (unfold SB, M64; lia). reflexivity. }
assert (U10 : U E (SOff 10 0) = c).
{ rewrite U_SOff, E10, Z.add_0_r, unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia. }
assert (U11 : U E (SOff 11 0) = t).
{ rewrite U_SOff, E11, Z.add_0_r, unsigned_lit_small by lia. apply zcanon_id. unfold M64. lia. }
assert (U0o : bv_unsigned (ew E (A_OBJ 0)) = VAL (A_OBJ 0))
  by (rewrite E0o; apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 0)); lia).
assert (U1o : bv_unsigned (ew E (A_OBJ 1)) = VAL (A_OBJ 1))
  by (rewrite E1o; apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 1)); lia).
assert (U12o : bv_unsigned (ew E (A_OBJ 12)) = VAL (A_OBJ 12))
  by (rewrite E12o; apply unsigned_lit_small; pose proof (pa_val_range (A_OBJ 12)); lia).
(* the numbers the pairwise disjointness of the regions needs, in one bundle each *)
pose proof YM05.alloc_ceiling_val as HAC.
assert (ZS : alloc_ceiling + 8560 <= sp0 /\ sp0 <= 2 ^ 47 /\
             sp0 - 304 <= mf_s1 sp0 /\ mf_s1 sp0 <= sp0 - 288)
  by (rewrite HSTK in *; unfold mf_s1 in *; lia).
assert (ZC : 4096 <= c /\ c + 9236 <= alloc_ceiling) by exact HcA.
assert (ZT : 4096 <= t /\ t + Z.of_nat (length s) + 1 <= alloc_ceiling) by exact HtA.
assert (ZU : 65536 <= as_uar_cell B /\ as_uar_cell B + 8 <= 6295552) by (unfold kImgEnd in Huar; lia).
assert (ZO : 65536 <= VAL (A_OBJ 0) /\ VAL (A_OBJ 0) + 8 <= 6295552 /\
             65536 <= VAL (A_OBJ 1) /\ VAL (A_OBJ 1) + 8 <= 6295552 /\
             65536 <= VAL (A_OBJ 12) /\ VAL (A_OBJ 12) + 8 <= 6295552) by lia.
assert (U37 : bv_unsigned (ew E 37) = mf_lptr lp lab) by (rewrite E37; apply unsigned_lit_small; lia).
split; [|split].
- unfold ss_mf0. apply pa_entry_st_ok_full.
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold mf_regions0, mf_r_probe, mf_r_saves, mf_r_slots, mf_r_gen, mf_r_txt, got_regionP, bcell_regionP,
      uar_got_regionP, uar_cell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite HSTK in *. lia.
    * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite HSTK in *. lia.
    * cbn [base_val]. rewrite Us1. split; [unfold mf_s1; lia|]. split; [unfold mf_s1; lia|].
      split; [|constructor]. intros o Ho. apply (apresent_writable SEGS). apply Hpres.
      rewrite HSTK in *. unfold mf_s1 in *. lia.
    * cbn [base_val]. rewrite Uc. unfold seg_spec.MC_GEN, seg_spec.SEG_M_SIZE in *.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ c seg_spec.MC_GEN 4 (SOff 35 0) (mc_gen mc));
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      apply mf_val_mem_of_sa. exact HGEN.
    * cbn [base_val]. rewrite Ut. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ t 0 1 (SOff 36 0) (mf_b0 s));
      [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. apply mf_val_mem_of_sa. apply (mf_sa_val_b0 SEGS (w_H W) mem). exact (proj1 HTS).
    * cbn [base_val]. rewrite E0o, unsigned_lit_small by (pose proof (pa_val_range (A_OBJ 0)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 12) 0) (VAL (A_OBJ 12)));
      [cbn [sv_denot]; rewrite E12o, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 12)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
    * cbn [base_val]. rewrite E12o, unsigned_lit_small by (pose proof (pa_val_range (A_OBJ 12)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 12)) 0 8 MfBx SB);
      [cbn [sv_denot MfBx]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
    * cbn [base_val]. rewrite E1o, unsigned_lit_small by (pose proof (pa_val_range (A_OBJ 1)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff 34 0) (as_uar_cell B));
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgu).
    * cbn [base_val]. rewrite E34, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) mem _ _ Kuar).
  + apply pairwise_disjoint_of_extents.
    unfold mf_regions0, mf_r_probe, mf_r_saves, mf_r_slots, mf_r_gen, mf_r_txt, got_regionP, bcell_regionP,
      uar_got_regionP, uar_cell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val].
    rewrite Usp, Us1, Uc, Ut, Uuc, U0o, U1o, U12o.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert HAC Hsep ZS ZC ZT ZCi ZTi ZCT ZU ZO. clear.
    unfold mf_nam, seg_spec.MC_GEN, seg_spec.SEG_M_SIZE, mf_s1. intros.
    repeat split; lia.
  + split; [|split; [exact I|]].
    * cbn [mf_facts0 f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
      rewrite Usp, Uc, Ut, USB, Us1, Uuc, Ugen, Ub0.
      change (2 ^ 4) with 16. change (2 ^ 2) with 4. change (2 ^ 5) with 32.
      rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold mf_s1 in *.
      repeat match goal with |- _ /\ _ => split end; try exact I; try (unfold SB; lia).
    * cbn [mf_facts0 f_alias alias_ok]. split; [|exact I].
      apply U_inj. rewrite U_SAlu, U_SOff, U_SLit, U_SOff. cbn [zalu_raw].
      rewrite Usp, E33, unsigned_lit_small by (unfold mf_s1; lia).
      rewrite (zcanon_id (sp0 + -288)) by (unfold M64; lia).
      change (zcanon (-32)) with (2 ^ 64 - 32).
      rewrite mf_land_m32 by lia.
      replace (sp0 + -288) with (sp0 - 288) by lia.
      rewrite !zcanon_id by (unfold M64, mf_s1; lia). unfold mf_s1. lia.
- unfold sh_ok, mf_SH0. repeat (apply Forall_cons); [| |apply Forall_nil].
  + unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
    rewrite UBx, U10. rewrite <- (aview_rd_of SEGS). split.
    * destruct HCA as (_ & _ & _ & HRA & _).
      intros x Hx. apply HRA. unfold seg_spec.MC_GEN, seg_spec.SEG_M_SIZE in *. lia.
    * intros a Ha. cbn [Z.min Z.max] in Ha. unfold mf_nam in ZCa.
      unfold SHADOW_OFF, seg_spec.MC_GEN, seg_spec.SEG_M_SIZE in *. lia.
  + unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
    rewrite UBx, U11. rewrite <- (aview_rd_of SEGS). split.
    * destruct HTA as (_ & _ & _ & HRA & _).
      replace (1 - 0) with 1 by lia. rewrite Z.add_0_r.
      intros x Hx. apply HRA. lia.
    * intros a Ha. cbn [Z.min Z.max] in Ha. rewrite Z.add_0_r in Ha. unfold mf_nam in ZTa.
      unfold SHADOW_OFF in *. lia.
- cbn zeta. split; [exact Usp|]. split; [exact Us1|]. split; [exact Uc|]. split; [exact Ut|].
  split; [exact Uuc|]. split; [exact Ugen|]. split; [exact Ub0|]. split; [exact U37|].
  split; [exact UBx | exact E32].
Qed.

End e.
End f.
End d.
