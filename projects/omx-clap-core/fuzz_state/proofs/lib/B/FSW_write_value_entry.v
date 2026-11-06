(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths, module names and numbers changed; 1266 of its 1332 lines of code are new or changed and 1014 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_dec_E.v, with its module paths and module names changed; 1282 of its 1392 lines of code are new or changed and 1222 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of the part of lib/A/FSW_write_value.v
   (a Theorem Labs lane, CTX-drop form a working branch 9e8a0cdbf33, the closed walk e64687560bd's
   structure) that precedes the number arm: same lemma names and statements, every address, frame, jump-table entry and
   return address re-measured on fs.asan-ubsan; imports point at lib/B's image files (YB1v, YB1w, FSH_Base, FSH_Rt,
   FSPstat) and lib/B's walk kit (FSW_K, FSW_K3, FSW_rres, FSW_ret, FSW_pj, a working branch 65632947036).
   rule 24: proves no function (kind: segment lemma) - the entry, the shared lemmas and the four leaf arms of
   write_value B, not the whole function. *)
(* write_value (fs.asan-ubsan 0x84010 .. 0x8449c, preset_file.c:525-575): the entry and the leaf arms of the ASan walk of
   fs's recursive value writer, image B, against lib/B/FSH_Fn_writer.v's write_value_spec_at (statement set
   a working branch 50968be8342). MEASURED on the pinned fs.asan-ubsan (sha256 5ac5ce09...,
   fuzz_state.objdump.txt): the prologue (frame 192, FRAME_write_value; ra, s0 .. s11 saved at 184 .. 88, a3 at 24), the
   two UBSan guards on the root node (0x8404c `beqz a1` and 0x84060 `bnez a0` after `andi a0,a1,7`, both to the trap
   `unimp` at 0x84444; ruled out by the node's atom fact, see wv_gf), the inline ASan check of v->type (shadow of the
   root node, atom 11, 0x84084), the type check `bltu 6, ty` (0x84094), the jump table at .rodata 0x21000 (seven 4-byte
   offsets, wv_jt) and `jr a1` at 0x840b0, and the arms: null (0x843d8), false (0x843e8) and true (0x8438c) load their
   literal (0x21120 / 0x21100 / 0x210e0) and TAIL-jump to put (0x8449c) with the entry ra (j at 0x84440); string
   (0x842e8) loads str (ASan check of v + 16), branches on it at 0x84304 and TAIL-jumps to put_string (0x85fc8, j at
   0x8434c); number (0x84398) is the Theorem Labs lane's, array / object (0x840b4, first put at 0x840d8 returning to 0x840dc)
   the Theorem Labs lane's. The other nine UBSan guards are in the container arms' loop (0x8418c .. 0x84268).
   Callees are Section hypotheses (put_spec, put_string_spec, indent_spec, astrlen_realizesU); the TAIL step
   (wvc_tail_otJ) and the raised-top after-call step (wvc_after_call_ot) are proved here from lib/B's FSW_K3 / FSW_rres.
   Port-from: the image-A walk above (structure, cuts, invariants); the bespoke image-B chain
   a working branch 4309d52a177 lib/B/Prog/write_value_entry.v (template only: the 192-byte frame and the
   entry's prologue on B's code).
   Rule 24 (proof-index, a Theorem Labs lane 04:2xZ, unpiped): write_value has RELEASED proofs for fs's PLAIN and UBSAN
   builds only (lib/Prog, lib/U/Prog), none for an ASan image; 0x84010 is not in the released set. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_rres FSW_ret FSW_pj FSH_Fn_writer.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSH_Fn_reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp WriterValue PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================= the decoded instruction table of fs.asan-ubsan's writer text ================= *)
(* The twin of lib/A/FSW_writer_tbl.v (a working branch) over image B, in the donor's form (build_table over
   the image's own bytes, table_ok by build_table_ok / build_table_ok0). The two ranges are RELOC-B's function extents
   (lib/B/YB1w.v:470-481):
     pj_write 0x83f94, write_value 0x84010, put 0x8449c, preset_base64_encode 0x84700,
     preset_base64_decode 0x84c4c .. 0x84e70                                       = 951 words
     put_string 0x85fc8, indent 0x86368 .. 0x863d8                                  = 260 words
   build_table steps pc + 4 (Reusable/YP02.v). MEASURED over fuzz_state.objdump.txt of the pinned fs.asan-ubsan
   (5ac5ce09): the two ranges hold 1211 instructions, every one 4 bytes (no compressed instruction), so every
   instruction the walks execute in them is a table entry. *)
Definition FSW_WR_LO1 : Z := tfib_A_pj_write.
Definition FSW_WR_N1 : nat := 951%nat.          (* (tfib_E_preset_base64_decode - tfib_A_pj_write) / 4 *)
Definition FSW_WR_LO2 : Z := tfib_A_put_string.
Definition FSW_WR_N2 : nat := 260%nat.          (* (tfib_E_indent - tfib_A_put_string) / 4 *)

Lemma fsw_wr_extents :
  tfib_A_pj_write + 4 * Z.of_nat FSW_WR_N1 = tfib_E_preset_base64_decode /\
  tfib_A_put_string + 4 * Z.of_nat FSW_WR_N2 = tfib_E_indent.
Proof. unfold FSW_WR_N1, FSW_WR_N2. cbv. split; reflexivity. Qed.

Definition fsw_wr_tbl_build : ctable :=
  build_table tfibsegs FSW_WR_LO2 FSW_WR_N2 (build_table tfibsegs FSW_WR_LO1 FSW_WR_N1 TEmpty).
Definition fsw_wr_tbl : ctable := Eval vm_compute in fsw_wr_tbl_build.
Lemma fsw_wr_tbl_eq : fsw_wr_tbl = fsw_wr_tbl_build.
Proof. vm_cast_no_check (eq_refl fsw_wr_tbl). Qed.
Lemma fsw_wr_tbl_ok : table_ok tfibsegs fsw_wr_tbl.
Proof.
  rewrite fsw_wr_tbl_eq. unfold fsw_wr_tbl_build.
  apply build_table_ok; [cbv; discriminate|].
  apply build_table_ok0. cbv. discriminate.
Qed.

(* every entry of the seven functions is in the table: the fetch at each entry pc is the image's own word *)
Lemma fsw_wr_tbl_entries :
  Forall (fun pc => clookup fsw_wr_tbl pc <> None)
    [tfib_A_pj_write; tfib_A_write_value; tfib_A_put; tfib_A_preset_base64_encode;
     tfib_A_preset_base64_decode; tfib_A_put_string; tfib_A_indent].
Proof. vm_compute. repeat constructor; discriminate. Qed.
(* write_value's two UBSan guards on the root node, its type dispatch and its trap, as the listing gives them:
   0x8404c beqz a1,0x84444; 0x84058 andi a0,a1,7; 0x84060 bnez a0,0x84444; 0x840b0 jr a1; 0x84444 unimp (a 4-byte
   word: c0001073) *)
Lemma fsw_wr_tbl_probe :
  clookup fsw_wr_tbl 0x8404c = Some 0x3e058c63 /\ clookup fsw_wr_tbl 0x84058 = Some 0x0075f513 /\
  clookup fsw_wr_tbl 0x84060 = Some 0x3e051263 /\ clookup fsw_wr_tbl 0x840b0 = Some 0x00058067 /\
  clookup fsw_wr_tbl 0x84444 = Some 0xc0001073.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* ================= the walk's constants and symbolic states ================= *)
Definition WV_F : Z := 192.                       (* the frame: lib/B/FSH_Base.FRAME_write_value (addi sp,sp,-192 at 0x84010) *)
Definition WV_CEIL : Z := 140737479966720.        (* 0x7fffff800000: alloc_ceiling's bound (YCbq.v asan_consts) *)
Definition WV_JT : Z := 0x21000.                  (* the type dispatch's jump table in .rodata (auipc / addi at 0x8409c) *)
Definition WV_PS : Z := 0x85fc8.                  (* put_string: lib/B/FSH_Base.A_put_string *)
Definition WV_R_OPEN : Z := 0x840dc.              (* the return address of the array / object arm's first put (jal at 0x840d8) *)

(* the root node v (atom 11, a1 at entry): read-only, the fields the arms load. The type is a literal per arm (the walk
   splits on the tree before the run), str / kids / keys / n are the walk's extra atoms xatom 0 .. 3 *)
Definition wv_node (ty : Z) : YP09.region :=
  YP09.mkRegion (Some 11%nat) 0 56 0 0
    [YP09.mkChunk 0 (CVal 4 (SLit ty)); YP09.mkChunk 16 (CVal 8 (SOff (xatom 0) 0));
     YP09.mkChunk 24 (CVal 8 (SOff (xatom 1) 0)); YP09.mkChunk 32 (CVal 8 (SOff (xatom 2) 0));
     YP09.mkChunk 40 (CVal 8 (SOff (xatom 3) 0))].
Definition wv_xs (str kids keys n : Z) : list word := [Z_to_bv 64 str; Z_to_bv 64 kids; Z_to_bv 64 keys; Z_to_bv 64 n].
(* the jump table (MEASURED: the bytes of fs.asan-ubsan's first PT_LOAD at 0x21000 .. 0x2101c, little-endian 32-bit
   offsets; 0x21000 + entry = null 0x843d8, false 0x843e8, true 0x8438c, number 0x84398, string 0x842e8, array and
   object 0x840b4) *)
Definition wv_jt : YP09.region :=
  YP09.mkRegion None 0x21000 0x2101c 0 0
    [YP09.mkChunk 0x21000 (CVal 4 (SLit 0x633d8)); YP09.mkChunk 0x21004 (CVal 4 (SLit 0x633e8));
     YP09.mkChunk 0x21008 (CVal 4 (SLit 0x6338c)); YP09.mkChunk 0x2100c (CVal 4 (SLit 0x63398));
     YP09.mkChunk 0x21010 (CVal 4 (SLit 0x632e8)); YP09.mkChunk 0x21014 (CVal 4 (SLit 0x630b4));
     YP09.mkChunk 0x21018 (CVal 4 (SLit 0x630b4))].
(* the atom facts: the node (8-aligned, below the ceiling) and str in [slo, shi].
   UBSan GUARDS 0x8404c and 0x84060 (fs.asan-ubsan is trap mode: both branch to the `unimp` at 0x84444). The node's
   fact mkAF 4096 (WV_CEIL - 56) 3 rules both out, so every run from wv_ss0 takes neither branch:
   - 0x8404c `beqz a1` (a1 = SOff 11 0, the root node pointer): YP0m.decide_eq answers false, because the atom's range
     [4096, WV_CEIL - 56] and the literal 0 are disjoint (ranges_disjoint). Premise: FSH_Fn_reader.pobj, 4096 <= v.
   - 0x84060 `bnez a0` after 0x84058 `andi a0,a1,7`: YP0m.s_and_ptr folds the mask 7 < 2 ^ 3 of the 2^3-aligned atom
     to the literal 0, so the branch is decided not taken. Premise: FSH_Fn_reader.pobj, v mod 8 = 0.
   wv_entry proves the fact from FSH_Fn_reader.pobj through wv_pobj (4096 <= v, v + 56 <= alloc_ceiling,
   v mod 8 = 0). *)
Definition wv_gf (slo shi : Z) : list (nat * afact) :=
  [(11%nat, mkAF 4096 (WV_CEIL - 56) 3); (xatom 0, mkAF slo shi 0)].
Definition wv_ss0 (ty slo shi : Z) : sstate := fss0T_args A_write_value WV_F [wv_node ty; wv_jt] (wv_gf slo shi).
(* the token engine's shadow entry: the node's 56 bytes are addressable *)
Definition wv_SH : list shent := [mkSHE 11 0 56].

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ---- read-only image bytes, from rom_view ---- *)
Lemma wv_in_rom_b : forall a,
  existsb (fun s => negb (seg_writable s) && (Z.of_N (seg_base s) <=? a) && (a <? Z.of_N (seg_base s) + Z.of_N (seg_size s)))
    tfibsegs = true -> in_rom tfibsegs a.
Proof.
intros a H. apply existsb_exists in H as (s & Hin & Hb).
apply andb_true_iff in Hb as [Hb H2]. apply andb_true_iff in Hb as [H0 H1].
exists s. split; [exact Hin|]. split; [destruct (seg_writable s); [discriminate | reflexivity]|]. lia.
Qed.
Lemma wv_rom_byte : forall (W : world tfibsegs) mem a b,
  rom_view tfibsegs W mem -> in_rom tfibsegs a -> seg_rom tfibsegs (Z_to_bv 64 a) = Some b ->
  mbyte tfibsegs (rdW W mem) a = Some b.
Proof.
intros W mem a b HR Ha Hb. pose proof (HR a Ha) as E. rewrite Hb in E. cbn [option_map] in E.
unfold aview in E. destruct (mbyte tfibsegs (rdW W mem) a) as [b'|] eqn:Eb; [|discriminate].
cbn [option_map] in E. injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Lemma wv_jt_ok : forall (W : world tfibsegs) mem E,
  rom_view tfibsegs W mem -> YP09.region_ok tfibsegs E (rdW W mem) wv_jt.
Proof.
intros W mem E HR. unfold YP09.region_ok, wv_jt.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
repeat constructor;
  (eapply (chunk_ok_val tfibsegs E _ 0 _ 4 _ _); [reflexivity | cbn; lia | cbn; lia |]);
  intros k Hk; cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Hk; rewrite Z.add_0_l;
  (destruct k as [|[|[|[|k]]]]; [| | | | lia]);
  (apply wv_rom_byte; [exact HR | apply wv_in_rom_b; vm_compute; reflexivity | vm_compute; reflexivity]).
Qed.
(* rom_view on the machine's own memory, from afn_preU's AR (over the unpoisoned memory) and arodata (fs_img_facts) *)
Lemma wv_rom_view : forall STK ly S U (W : world tfibsegs) regs mem md ch,
  fs_img_facts tfibsegs B ->
  afn_preU tfibsegs B STK ly S U W regs mem md ch -> arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) mem) ->
  rom_view tfibsegs W mem.
Proof.
intros STK ly S U W regs mem md ch IMG HPRE HRO.
pose proof (fsw_ARU B STK ly S U W regs mem md ch HPRE) as HARU.
pose proof HPRE as ((HAR & _) & _).
assert (LOW : forall a, 0 <= a < FS_IMG_END -> aview tfibsegs (w_H W) (unpoison U mem) a = aview tfibsegs (w_H W) mem a).
{ intros a Ha. apply (aview_eq_of tfibsegs). unfold mrestrict.
  rewrite (ARU_mem_low tfibsegs B ly S U W mem md (Z_to_bv 64 a) HARU)
    by (rewrite (wz a ltac:(unfold FS_IMG_END in Ha; lia)); unfold FS_IMG_END, SHADOW_OFF in *; lia).
  reflexivity. }
assert (HRO' : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) (unpoison U mem))).
{ intros a Ha Ho He. rewrite LOW; [exact (HRO a Ha Ho He)|].
  destruct Ha as [(s & Hs & _ & Hr) | Hr]; [apply fs_segs_img; exists s; split; [exact Hs | lia]|].
  unfold FS_RLO, FS_RHI, FS_IMG_END in *; lia. }
destruct IMG as (_ & IMG2).
destruct (IMG2 ly S W (unpoison U mem) md HAR HRO') as (HRV & _).
intros a Ha. rewrite <- LOW; [exact (HRV a Ha)|].
destruct Ha as (s & Hs & _ & Hr). apply fs_segs_img. exists s. split; [exact Hs | lia].
Qed.

(* ---- the root node's region: read-only, the field chunks from pj_hdr (FSW_pj's chunk lemmas) ---- *)
Lemma wv_node_ok : forall E m v ty num str kids keys n cap,
  PjStruct.pj_hdr tfibsegs m v ty num str kids keys n cap ->
  ew E 11 = Z_to_bv 64 v -> ew E (xatom 0) = Z_to_bv 64 str -> ew E (xatom 1) = Z_to_bv 64 kids ->
  ew E (xatom 2) = Z_to_bv 64 keys -> ew E (xatom 3) = Z_to_bv 64 n ->
  YP09.region_ok tfibsegs E m (wv_node ty).
Proof.
intros E m v ty num str kids keys n cap ((H8 & Hlo & Hhi & _) & Hty & _ & Hstr & Hkids & Hkeys & Hn & _) E11 E0 E1 E2 E3.
unfold YP09.region_ok, wv_node.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E11, (unsigned_lit_small v) by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
- apply (fsw_pj_chunk4 tfibsegs E m v 0 _ ty); [rewrite Z.add_0_r; exact Hty | reflexivity].
- apply (fsw_pj_chunk8 tfibsegs E m v 16 _ str); [exact Hstr | rewrite fsw_SOff0; exact E0].
- apply (fsw_pj_chunk8 tfibsegs E m v 24 _ kids); [exact Hkids | rewrite fsw_SOff0; exact E1].
- apply (fsw_pj_chunk8 tfibsegs E m v 32 _ keys); [exact Hkeys | rewrite fsw_SOff0; exact E2].
- apply (fsw_pj_chunk8 tfibsegs E m v 40 _ n); [exact Hn | rewrite fsw_SOff0; exact E3].
Qed.

(* ---- where the root node lies (FSH_Fn_reader.pobj): a live fake frame or a live heap block, so client bytes: not the
   image, below alloc_ceiling, addressable, and apart from the shadow band ---- *)
Lemma wv_pobj : forall ly S (W : world tfibsegs) memA md mem v,
  AR tfibsegs B ly S W memA md -> FSH_Fn_reader.pobj tfibsegs B ly S W mem v ->
  4096 <= v /\ v + 56 <= alloc_ceiling /\ v mod 8 = 0 /\
  (forall a, v <= a < v + 56 -> ~ in_img tfibsegs a) /\
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF v 56 /\
  (forall E, U E fs_Bx = SHADOW_OFF -> U E (SOff 11 0) = v -> app_apart fs_Bx E (mkSHE 11 0 56)).
Proof.
intros ly S W memA md mem v HAR (Hpl & _).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct Hpl as [((cid & pos & Hin & Hc0 & Hal & Hlo & Hhi) & H8 & HRA) | ((b & m & Hin & Hlo & Hhi) & H8 & HRA)].
- destruct (frames_bounds tfibsegs B LAWS ly S W memA md cid pos HAR Hin) as (Hf0 & Hfc & _).
  split; [lia|]. split; [lia|]. split; [exact H8|].
  split; [intros a Ha; apply (frm_img tfibsegs B LAWS ly S W memA md cid pos a HAR Hin); lia|].
  split; [exact HRA|].
  intros E HB Hv.
  destruct (shent_app_of_frame tfibsegs B LAWS ly S W memA md E fs_Bx 11 v cid pos 0 56 (rdW W mem) HAR Hin HB Hv
    ltac:(lia) ltac:(lia) ltac:(lia)) as [_ Happ].
  exact Happ.
- destruct (al_blocks _ _ LAWS ly S W memA md b m HAR Hin) as (_ & H4096 & Hceil & _).
  split; [unfold HEAD in Hlo; lia|]. split; [lia|]. split; [exact H8|].
  split; [intros a Ha; apply (blk_img tfibsegs B LAWS ly S W memA md b m a HAR Hin); unfold HEAD in Hlo; lia|].
  split; [exact HRA|].
  intros E HB Hv.
  destruct (shent_app_of_block tfibsegs B LAWS ly S W memA md E fs_Bx 11 v b m 0 56 (rdW W mem) HAR Hin HB Hv
    ltac:(unfold HEAD in Hlo; lia) ltac:(lia) ltac:(lia)) as [_ Happ].
  exact Happ.
Qed.

(* ---- an image range is apart from a range of non-image bytes ---- *)
Lemma wv_img_cover : forall c n,
  existsb (fun s => (Z.of_N (seg_base s) <=? c) && (c + n <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs = true ->
  forall a, c <= a < c + n -> in_img tfibsegs a.
Proof.
intros c n H a Ha. apply existsb_exists in H as (s & Hin & Hb). apply andb_true_iff in Hb as [H0 H1].
exists s. split; [exact Hin|]. lia.
Qed.
Lemma wv_apart_img : forall c n v k,
  0 < n -> 0 < k -> (forall a, c <= a < c + n -> in_img tfibsegs a) -> (forall a, v <= a < v + k -> ~ in_img tfibsegs a) ->
  v + k <= c \/ c + n <= v.
Proof.
intros c n v k Hn Hk Hc Hv. destruct (Z_le_gt_dec (v + k) c) as [L|L]; [left; exact L|].
destruct (Z_le_gt_dec (c + n) v) as [L2|L2]; [right; exact L2|]. exfalso.
apply (Hv (Z.max v c)); [lia|]. apply Hc. lia.
Qed.
End e.

(* ================= the C string of a tree node (proved by a part of a Theorem Labs lane, folded from its ZZwv_cstr.v) ================= *)
Section cs. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* a byte visible in the unpoisoned memory is visible in the machine memory: a user-poisoned shadow byte reads 0xf7 *)
Lemma wv_vis_of_unpoison : forall ly S U (W : world tfibsegs) mem md a,
  ARU tfibsegs B ly S U W mem md ->
  aview tfibsegs (w_H W) (unpoison U mem) a <> None -> aview tfibsegs (w_H W) mem a <> None.
Proof.
intros ly S U W mem md a H Hv.
destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:E.
- pose proof (ARU_poisoned tfibsegs B ly S U W mem md H _ E) as P.
  rewrite Z_to_bv_unsigned in P. unfold bv_wrap in P. change (bv_modulus 64) with (2 ^ 64) in P.
  rewrite aview_mod, P. discriminate.
- rewrite (aview_unpoison_out tfibsegs (w_H W) U mem a E) in Hv. exact Hv.
Qed.

(* under fs_heads, the shadow byte of a block's byte past its 16-byte head is not user-poisoned *)
Lemma wv_ush_user_out : forall ly S U (W : world tfibsegs) mem md q m x,
  ARU tfibsegs B ly S U W mem md -> fs_heads B ly S U ->
  In (q, m) (ablocks B ly S) -> q + 16 <= x < q + req_size m ->
  in_ush U (shadow_addr x) = false.
Proof.
intros ly S U W mem md q m x H FH Hb Hx.
destruct (in_ush U (shadow_addr x)) eqn:E; [|reflexivity]. exfalso.
apply in_ush_spec in E as (r & Hr & Hs).
destruct (FH r Hr) as (E16 & m' & Hm' & M16).
destruct (upoison_ok_In B ly S U r (ARU_ok tfibsegs B ly S U W mem md H) Hr) as (A8 & _).
destruct r as [h len]. cbn [fst snd] in *. subst len.
assert (Hhx : h <= x < h + 16).
{ apply Z.mod_divide in A8 as [t Ht]; [|lia]. subst h. unfold shadow_addr in Hs.
  rewrite Z.div_mul in Hs by lia. change (16 / 8) with 2 in Hs.
  pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia. }
pose proof (al_blocks tfibsegs B (AR_laws_ok tfibsegs B) ly S W (unpoison U mem) md q m
  (ARU_AR tfibsegs B ly S U W mem md H) Hb) as (_ & _ & _ & _ & _ & PW & _).
destruct (Z.eq_dec h q) as [->|NE]; [lia|].
assert (I1 : In (h, req_size m') (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)))
  by (apply (in_map (fun b => (fst b, req_size (snd b))) _ (h, m')); exact Hm').
assert (I2 : In (q, req_size m) (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)))
  by (apply (in_map (fun b => (fst b, req_size (snd b))) _ (q, m)); exact Hb).
destruct (pairwise_In2 zdisjoint _ _ _ PW I1 I2 ltac:(intros E'; injection E'; intros _ E''; exact (NE E'')))
  as [D|D]; unfold zdisjoint in D; cbn [fst snd] in D; lia.
Qed.

(* the 8-aligned shadow hull grows with the range *)
Lemma wv_hull_mono : forall a b, a <= b -> shadow_addr a / 8 * 8 <= shadow_addr b / 8 * 8.
Proof.
intros a b Hab. unfold shadow_addr. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|].
pose proof (Z.div_le_mono a b 8 ltac:(lia) Hab). lia.
Qed.

(* a NUL-terminated string at the start of a live reader block: cstr_ok on the machine memory *)
Lemma wv_cstr_ok_block : forall ly S U (W : world tfibsegs) mem md p k (s : list Z),
  ARU tfibsegs B ly S U W mem md -> FSupoisonU.fs_heads B ly S U ->
  fs_rblock tfibsegs B ly S W mem p k ->
  PjStruct.pj_cbytes tfibsegs (rdW W mem) p s -> Z.of_nat (length s) + 1 <= k ->
  cstr_ok tfibsegs W mem p s.
Proof.
intros ly S U W mem md p k s H FH (Hb & P16 & K0 & _) (HF & HBY) Hk.
unfold HEAD in Hb. unfold cstr_ok.
set (n := Z.of_nat (length s)) in *.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (ARU_AR tfibsegs B ly S U W mem md H) as HAR.
pose proof (proj1 HAR) as M.
assert (RQ : req_size (k + 16) = k + 16) by (unfold req_size; destruct (Z.eqb_spec (k + 16) 0); lia).
destruct (al_blocks tfibsegs B LAWS ly S W (unpoison U mem) md (p - 16) (k + 16) HAR Hb)
  as (A16 & A4096 & ACEIL & AAPP & APRES & _ & AMAX).
rewrite RQ in ACEIL, AAPP, APRES.
pose proof ASAN_CEIL_range as [CR _].
(* the chunk of the block *)
destruct (ablock_chunk B ly S (p - 16) (k + 16) Hb) as (ck & Hck & Hu & Hrq).
pose proof (chunk_facts B ly S _ ck M Hck) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
rewrite Hu in G4. rewrite Hrq, RQ in G8.
assert (CH : (ck_base B ly ck + ck_extent ck) mod 8 = 0 /\ p + n + 8 <= alloc_ceiling).
{ revert G9. destruct (ck_beg ck) as [|off|r o|cid pos]; intros G9; cbv beta iota zeta in G9;
    [contradiction | | | contradiction].
  - destruct G9 as (C1 & FP & CC & CX & CB & X0 & XM & XA & RA1 & RA2).
    pose proof (class_ok (prim_class off) ltac:(lia)) as (K1 & K2 & _).
    pose proof (region_in_prim ly (prim_class off) (am_layout B ly S _ M) ltac:(lia)) as (_ & _ & _ & R4 & R5).
    split.
    + apply Z.mod_divide; [lia|]. pose proof G3 as G3'. apply Z.mod_divide in G3' as [u Hu']; [|lia].
      apply Z.mod_divide in K2 as [v Hv]; [|lia]. exists (2 * u + 4 * v). rewrite CX. lia.
    + unfold kFreeArrayOffset in RA2. unfold ASAN_CEIL in R5. lia.
  - destruct G9 as (O & FP & CB & CX & IN & PA & RL).
    rewrite Hrq in CX, FP. unfold sec_map_size in CX.
    assert (RZ : ck_rz ck = rz_size (k + 16)) by (unfold ck_rz; rewrite Hrq; reflexivity).
    pose proof (round_up_ge (needed_size (k + 16)) kPage ltac:(unfold kPage; lia)) as ((RU1 & RU2) & RU3).
    assert (ND : needed_size (k + 16) = rounded_size (k + 16) + rz_size (k + 16) + rz_size (k + 16))
      by (unfold needed_size, needed_primary; rewrite FP; ring).
    pose proof (rounded_size_bounds (k + 16) ltac:(lia)) as ((RS1 & _) & _).
    pose proof (rz_size_bounds (k + 16)) as ((RZ1 & _) & _).
    pose proof (Z.le_max_l (k + 16) 8) as MX.
    split.
    + apply Z.mod_divide; [lia|]. pose proof G3 as G3'. apply Z.mod_divide in G3' as [u Hu']; [|lia].
      apply Z.mod_divide in RU3 as [v Hv]; [|unfold kPage; lia]. exists (2 * u + 512 * v). rewrite CX.
      unfold kPage in *. lia.
    + unfold ASAN_CEIL in G2. lia. }
unfold ASAN_CEIL in CR.
refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
- (* cstr: the bytes and the NUL, from pj_cbytes *)
  assert (FB : Forall (fun c => 0 <= c < 256) (s ++ [0])).
  { apply Forall_app. split; [eapply Forall_impl; [|exact HF]; intros c Hc; cbv beta in Hc |- *; lia | constructor; [cbv beta; lia | constructor]]. }
  destruct HBY as (_ & _ & BY). unfold cstr. split.
  + intros j Hj.
    assert (Hb8 : 0 <= nth j (s ++ [0]) 0 < 256) by (rewrite Forall_forall in FB; apply FB; apply nth_In; exact Hj).
    split; [|exact Hb8].
    intros i Hi. destruct i as [|i]; [| exfalso; apply Nat.succ_lt_mono in Hi; exact (Nat.nlt_0_r _ Hi)].
    pose proof (BY j ltac:(rewrite length_map; exact Hj)) as Bj.
    rewrite nth_error_map, (nth_error_nth' _ 0 Hj) in Bj. cbn [option_map] in Bj.
    change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
    assert (E : mbyte tfibsegs (rdW W mem) (p + Z.of_nat j) = Some (Z_to_bv 8 (nth j (s ++ [0]) 0))) by exact Bj.
    replace (YO0f.le_byte (nth j (s ++ [0]) 0) 1 0) with (nth j (s ++ [0]) 0); [exact E|].
    unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
    rewrite Z.shiftr_0_r. change (2 ^ 8) with 256.
    rewrite (Z.mod_small (nth j (s ++ [0]) 0) 256) by lia. rewrite Z.mod_small by lia. reflexivity.
  + eapply Forall_impl; [|exact HF]. intros c Hc. cbv beta in Hc |- *. lia.
- (* 4096 <= p *)
  lia.
- (* below the allocation ceiling (cstr_ok asks p + n + 1 since 2d9cdf6a160; the chunk gives p + n + 8) *)
  pose proof (proj2 CH) as CH2. lia.
- (* len < 2 ^ 32: a block is below MALLOC_MAX = 2 ^ 28 *)
  unfold MALLOC_MAX in AMAX. lia.
- (* amem_range: the block is in application memory *)
  unfold amem_range. unfold in_app in AAPP. unfold ASAN_CEIL in AAPP.
  destruct AAPP as [_ [AL | [AH1 AH2]]]; [left | right]; unfold kLowMemEnd, kLowShadowBeg, kHighMemBeg, kHighMemEnd in *; lia.
- (* range_addressable over len + 1, on the machine memory *)
  unfold range_addressable. intros x Hx.
  destruct (range_addressable_of_block tfibsegs B LAWS ly S W (unpoison U mem) md (p - 16) (k + 16) p (n + 1)
    HAR Hb ltac:(lia) ltac:(rewrite RQ; lia) x Hx) as (sv & Hsv & Hok).
  exists sv. split; [|exact Hok].
  assert (HU : in_ush U (bv_unsigned (Z_to_bv 64 (shadow_of_addr SHADOW_OFF x))) = false).
  { rewrite wz by (unfold shadow_of_addr, SHADOW_OFF; pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia));
      pose proof (Z.div_le_upper_bound x 8 x ltac:(lia) ltac:(lia)); lia).
    change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x).
    apply (wv_ush_user_out ly S U W mem md (p - 16) (k + 16) x H FH Hb). rewrite RQ. lia. }
  rewrite <- (aview_unpoison_out tfibsegs (w_H W) U mem _ HU). exact Hsv.
- (* shadow_hull_vis over len + 1: the block's hull, visible on the machine memory *)
  destruct (al_shadow tfibsegs B LAWS ly S W (unpoison U mem) md (p - 16) (k + 16) HAR Hb) as [_ HH].
  rewrite RQ in HH. unfold shadow_hull_vis in HH |- *. intros sa Hsa.
  apply (wv_vis_of_unpoison ly S U W mem md sa H). apply HH.
  pose proof (wv_hull_mono (p - 16) p ltac:(lia)).
  pose proof (wv_hull_mono (p + (n + 1) - 1) (p - 16 + (k + 16) - 1) ltac:(lia)). lia.
- (* the rest of the NUL's 8-byte word visible: block bytes, then the chunk's tail junk *)
  intros a Ha. apply (wv_vis_of_unpoison ly S U W mem md a H).
  destruct (Z_lt_le_dec a (p + k)) as [Lk|Lk].
  + apply aview_some_of_apresent. exact (proj1 (APRES a ltac:(lia))).
  + assert (AE : a < ck_base B ly ck + ck_extent ck).
    { destruct CH as [C8 _].
      pose proof (Z.div_mod (p + n) 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (p + n) 8 ltac:(lia)) as D2.
      pose proof (Z.div_mod (ck_base B ly ck + ck_extent ck) 8 ltac:(lia)) as D3. rewrite C8 in D3. lia. }
    assert (INJ : In (aoff (sptr_exp (ck_beg ck)) (ck_rz ck + ck_n ck), ck_extent ck - ck_rz ck - ck_n ck)
                     (ajunk B ly S)).
    { unfold ajunk. right. right. apply in_or_app. right. apply in_or_app. right. apply in_or_app. left.
      apply in_flat_map. exists ck. split; [exact Hck|].
      unfold chunk_junk. cbv zeta. apply in_or_app. right. apply in_or_app. right. apply in_or_app. right.
      left. reflexivity. }
    pose proof (proj1 (Forall_forall _ _) (am_junk B ly S _ M) _ INJ) as V.
    unfold range_vis in V. cbn [fst snd] in V.
    assert (NS : forall e', sptr_exp (ck_beg ck) <> ASh e') by (intros e'; destruct (ck_beg ck); cbn; discriminate).
    rewrite (aeval_aoff B ly _ _ NS) in V.
    change (aeval B ly (sptr_exp (ck_beg ck))) with (ck_base B ly ck) in V.
    assert (CKN : ck_n ck = k + 16) by (unfold ck_n; rewrite Hrq; exact RQ).
    specialize (V (a - (p + k)) ltac:(lia)).
    replace (ck_base B ly ck + (ck_rz ck + ck_n ck) + (a - (p + k))) with a in V by lia.
    exact V.
Qed.

(* the corollary for a string of a struct pj node: its block is one of the tree's reader blocks *)
Lemma wv_cstr_ok_node : forall ly S U (W : world tfibsegs) mem md UL str k s,
  ARU tfibsegs B ly S U W mem md -> FSupoisonU.fs_heads B ly S U ->
  ublocks_ok B tfibsegs ly S W mem UL ->
  PjStruct.pj_cstr tfibsegs (rdW W mem) (fun a k => In (a, k) UL) str k s ->
  cstr_ok tfibsegs W mem str s.
Proof.
intros ly S U W mem md UL str k s H FH HUL (HL & Hk & HC).
exact (wv_cstr_ok_block ly S U W mem md str k s H FH (HUL str k HL) HC Hk).
Qed.
End cs.

(* ---- the frame chain an allocator call reads at s0 = o: FSH_Fn_writer.v's ONE-NODE clause, word for word (statement
   head a working branch a369fd60e33), named once here ---- *)
Definition wv_chain_o {fx : YK11.FPState} {rc : YM05.RunCeil} (U : list (Z * Z)) (W : world tfibsegs)
    (mem : word -> option byte) (regs : bvmap 5 word) (o : Z) : Prop :=
  o = spZ regs + 8 /\ raZ regs < alloc_ceiling \/
  spZ regs + 16 <= o /\ exists ra nfp, rdword (aview tfibsegs (w_H W) (unpoison U mem)) (o - 8) = Some ra /\
    rdword (aview tfibsegs (w_H W) (unpoison U mem)) (o - 16) = Some nfp /\ (ra < 4096 \/ nfp < alloc_ceiling).

(* ================= the entry ================= *)
Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the shadow-base cells (FSH_Base.FsShadowSyms, S0's one named hypothesis for them; TfibLib discharges it) and the
   image facts (FSH_Rt.fs_img_facts, proved once for fs's TfibB) *)
Hypothesis HSS : FsShadowSyms B.
Hypothesis IMG : fs_img_facts tfibsegs B.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* the entry symbolic state (frame, shadow-base cells, the root node, the jump table) and the node's shadow entry.
   The atoms_ok goal below is where the two UBSan guards on the root node are discharged (see wv_gf): 0x8404c from
   4096 <= v (Hv4096), 0x84060 from v mod 8 = 0 (Hv8), both out of FSH_Fn_reader.pobj by wv_pobj. *)
Lemma wv_entry : forall STK ly S Uh (W : world tfibsegs) regs mem md ch v ty num str kids keys n cap slo shi,
  afn_preU tfibsegs B STK ly S Uh W regs mem md ch -> arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) mem) ->
  WV_F <= STK ->
  getr regs 11 = w64 v -> FSH_Fn_reader.pobj tfibsegs B ly S W mem v ->
  PjStruct.pj_hdr tfibsegs (rdW W mem) v ty num str kids keys n cap -> slo <= str <= shi ->
  st_ok tfibsegs (Ereg regs (fs_extraT ++ wv_xs str kids keys n)) (wv_ss0 ty slo shi)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 A_write_value) mem (seg_rom tfibsegs))) /\
  sh_ok tfibsegs fs_Bx wv_SH (Ereg regs (fs_extraT ++ wv_xs str kids keys n)) (rdW W mem).
Proof.
intros STK ly S Uh W regs mem md ch v ty num str kids keys n cap slo shi HPRE HRO HF H11 HPO HH Hs.
destruct HSS as [HBgot HBcell].
pose proof (fsw_sp B STK ly S Uh W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof HPRE as ((HAR & _) & _).
pose proof asan_consts as (C1 & _).
destruct (wv_pobj B ly S W (unpoison Uh mem) md mem v HAR HPO) as (Hv4096 & Hvceil & Hv8 & Hvimg & HRA & Happ).
pose proof HH as (_ & (Hty0 & _) & _ & (Hstr0 & _) & (Hkids0 & _) & (Hkeys0 & _) & (Hn0 & _) & _).
set (E := Ereg regs (fs_extraT ++ wv_xs str kids keys n)).
assert (E11 : ew E 11 = Z_to_bv 64 v)
  by (subst E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (EX : forall i, ew E (xatom i) = nth i (wv_xs str kids keys n) (Z_to_bv 64 0)) by (intros i; apply fsw_ew_xatom).
pose proof (EX 0%nat) as E0. pose proof (EX 1%nat) as E1. pose proof (EX 2%nat) as E2. pose proof (EX 3%nat) as E3.
cbn [nth wv_xs] in E0, E1, E2, E3.
assert (E2sp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (U32 : U E fs_Bx = SHADOW_OFF).
{ unfold fs_Bx. rewrite U_SOff. subst E. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. cbn [nth fs_extraT app].
  rewrite Z.add_0_r, unsigned_lit_small by (unfold SHADOW_OFF; lia). apply zcanon_id. unfold M64, SHADOW_OFF. lia. }
assert (U11 : U E (SOff 11 0) = v) by (apply U_atom; [exact E11 | lia]).
split.
- apply (fsw_entryT_argsX B STK WV_F ly S Uh W regs mem md ch A_write_value [wv_node ty; wv_jt] (wv_gf slo shi)
    (wv_xs str kids keys n) HBgot HBcell HPRE ltac:(unfold WV_F in *; lia)).
  + vm_compute. reflexivity.
  + constructor; [|constructor; [|constructor]].
    * exact (wv_node_ok E (rdW W mem) v ty num str kids keys n cap HH E11 E0 E1 E2 E3).
    * exact (wv_jt_ok W mem E (wv_rom_view B STK ly S Uh W regs mem md ch IMG HPRE HRO)).
  + apply pairwise_disjoint_of_extents.
    unfold fsT_regions_args, fsT_regions, fs_got_region, fs_bcell_region, fstk, wv_node, wv_jt, extent_of_region.
    cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val]. fold E. rewrite E2sp, E11, (unsigned_lit_small v) by lia.
    pose proof (wv_apart_img tfib_D_GOT_asan_shadow_memory_dynamic_address 8 v 56 ltac:(lia) ltac:(lia)
      (wv_img_cover tfib_D_GOT_asan_shadow_memory_dynamic_address 8 ltac:(vm_compute; reflexivity)) Hvimg) as D1.
    pose proof (wv_apart_img tfib_D_asan_shadow_memory_dynamic_address 8 v 56 ltac:(lia) ltac:(lia)
      (wv_img_cover tfib_D_asan_shadow_memory_dynamic_address 8 ltac:(vm_compute; reflexivity)) Hvimg) as D2.
    pose proof (wv_apart_img 0x21000 28 v 56 ltac:(lia) ltac:(lia)
      (wv_img_cover 0x21000 28 ltac:(vm_compute; reflexivity)) Hvimg) as D3.
    unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, WV_F in *.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
  + unfold wv_gf. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    fold E. rewrite E11, E0, !unsigned_lit_small by lia. change (2 ^ 3) with 8. rewrite Z.pow_0_r, Z.mod_1_r.
    unfold WV_CEIL in *. split; [split; [lia | split; [exact Hv8 | lia]]|]. split; [|exact I]. split; [lia | lia].
- constructor; [|constructor]. split.
  + cbn [she_m she_lo she_hi]. rewrite U11, Z.add_0_r.
    exact (obl_of_range tfibsegs (w_H W) mem E fs_Bx v 56 v 56 HRA U32 ltac:(lia) ltac:(lia)).
  + exact (Happ E U32 U11).
Qed.

(* ================= the spec's post, and the spec restricted to a class of trees ================= *)
(* write_value_spec_at's conclusion (FSH_Fn_writer.v, statement head a working branch efbff066c09), m = 2 - k *)
Definition wv_post (m : nat) (ot o v pretty d : Z) (t : PjTree.jv) (D UL : list (Z * Z)) (buf cap failed : Z)
    (text : list Z) (live peak cnt fail : Z) (regs : bvmap 5 word) (ly : alayout) (S : astate) (U : list (Z * Z))
    (W : world tfibsegs) (mem : word -> option byte) (md : Model) : world tfibsegs -> config -> Prop :=
  fun W' c' => exists (st' : WriterApp.wst) buf' U',
       st' = WriterApp.putN (WriterApp.mkW failed text cap cnt fail [])
               (WriterValue.wvpieces t (negb (pretty =? 0)) d) /\
       uswap U U' buf buf' cap /\
       wpost B tfibsegs (STK_write_value m) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) regs ly S U W mem md
         (wevk cap st') U'
         (fun ly' S' W' regs' mem' md' =>
            wout_ok B tfibsegs ly' S' W' mem' o buf' (WriterApp.w_cap st') (WriterApp.w_failed st')
              (WriterApp.w_text st') /\
            wbudget_kept S S' failed cap cnt (WriterApp.w_failed st') (WriterApp.w_cap st') (WriterApp.w_cnt st') /\
            bswap (ablocks B ly S) (ablocks B ly' S') buf buf' cap (WriterApp.w_cap st') /\
            wkeep tfibsegs W W' mem mem' (spZ regs) ot o 32 /\
            PjStruct.pj_node tfibsegs (rdW W' mem') (fun a k => In (a, k) UL) v t D /\
            (exists peak', peak <= peak' <= Z.max peak (live - cap + WriterApp.w_cap st') /\
               fs_glob tfibsegs W' mem' (live + WriterApp.w_cap st' - cap) peak'
                 (WriterApp.w_cnt st') (WriterApp.w_fail st')))
         W' c'.
(* write_value_spec_at's premises with the extra premise P t (an arm: one class of trees) *)
Definition wv_spec_on (P : PjTree.jv -> Prop) (k : nat) : Prop :=
  forall ly S U W regs mem md ch ot o v pretty d (t : PjTree.jv) D UL buf cap failed text live peak cnt fail,
  P t ->
  (PjTree.depth t <= 2 - k)%nat ->
  fpreU tfibsegs B (STK_write_value (2 - k)) ly S U W regs mem md ch -> fs_heads B ly S U ->
  Z.of_nat (length (frames S)) <= FRL_CRT_CALLEE ->
  getr regs 10 = w64 o -> getr regs 11 = w64 v -> getr regs 12 = w64 pretty -> getr regs 13 = w64 d ->
  0 <= pretty < alloc_ceiling -> 0 <= d < 2 ^ 31 -> d + Z.of_nat (PjTree.depth t) <= 2 ^ 31 - 1 ->
  (s0Z regs < alloc_ceiling \/ s0Z regs = o \/ o + 48 <= s0Z regs) ->
  wout_ok B tfibsegs ly S W mem o buf cap failed text -> fs_glob tfibsegs W mem live peak cnt fail ->
  (cap <> 0 -> In (buf - HEAD, HEAD) U) ->
  spZ regs <= o -> o + 32 <= ot -> ot mod 16 = 0 -> ot <= ly_top ly ->
  wv_chain_o U W mem regs o ->
  (forall a, spZ regs <= a < ot -> apresent (w_H W) mem a) ->
  PjStruct.pj_node tfibsegs (rdW W mem) (fun a k => In (a, k) UL) v t D ->
  FSH_Fn_reader.pobj tfibsegs B ly S W mem v ->
  ublocks_ok B tfibsegs ly S W mem UL -> (forall a k, In (a, k) D -> In (a, k) UL /\ a <> buf) ->
  (cap <> 0 -> v + 56 <= buf - HEAD \/ buf + cap <= v) ->
  jv_plain t ->
  (forall x, o <= x < ot -> ~ PjStruct.pj_foot v D x) ->
  Z.of_nat (length text)
    + Z.of_nat (length (concat (WriterValue.wvpieces t (negb (pretty =? 0)) d))) + 1 <= WMAX ->
  cap <= WMAX -> cap <= live ->
  wbudget_pre S cap cnt live
    (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) (WriterValue.wvpieces t (negb (pretty =? 0)) d)) ->
  SRr tfibsegs W (cfg_at tfibsegs A_write_value regs mem md)
    (wv_post (2 - k) ot o v pretty d t D UL buf cap failed text live peak cnt fail regs ly S U W mem md).
(* the arms cover every tree *)
Lemma wv_spec_of_arms : forall (P1 P2 : PjTree.jv -> Prop) k,
  (forall t, P1 t \/ P2 t) -> wv_spec_on P1 k -> wv_spec_on P2 k ->
  write_value_spec_at B tfibsegs k.
Proof.
intros P1 P2 k Hcov H1 H2. unfold write_value_spec_at.
intros ly S U W regs mem md ch ot o v pretty d t D UL buf cap failed text live peak cnt fail.
destruct (Hcov t) as [Ht|Ht]; [exact (H1 ly S U W regs mem md ch ot o v pretty d t D UL buf cap failed text live peak
  cnt fail Ht) | exact (H2 ly S U W regs mem md ch ot o v pretty d t D UL buf cap failed text live peak cnt fail Ht)].
Qed.

(* ================= after a callee: its journal over the node, the buffer and the window ================= *)
(* fpostU's Q, weakened with the journal and the heads in hand *)
Lemma wv_fpostU_mono : forall STK sp0 FP regs ly S U (W : world tfibsegs) mem md k U'
    (Q Q' : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) W' c',
  fpostU tfibsegs B STK sp0 FP regs ly S U W mem md k U' Q W' c' ->
  (forall ly' S' regs' mem' md',
     ajournal tfibsegs B STK sp0 FP ly S W (unpoison U mem) md [] ly' S' W' (unpoison U' mem') md' k ->
     upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' -> aregs_preserved regs regs' ->
     Q ly' S' W' regs' mem' md' -> Q' ly' S' W' regs' mem' md') ->
  fpostU tfibsegs B STK sp0 FP regs ly S U W mem md k U' Q' W' c'.
Proof.
intros STK sp0 FP regs ly S U W mem md k U' Q Q' W' c' (ly' & S' & regs' & mem' & md' & Ec & HJ & OK & PO & HP & HQ) H.
exists ly', S', regs', mem', md'. split; [exact Ec|]. split; [exact HJ|]. split; [exact OK|]. split; [exact PO|].
split; [exact HP|]. exact (H ly' S' regs' mem' md' HJ OK PO HP HQ).
Qed.
(* a byte off the image that the journal keeps, on the raw restricted memory *)
Lemma wv_raw_of_aview : forall H H' (m m' : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ in_img tfibsegs a ->
  aview tfibsegs H' m' a = aview tfibsegs H m a -> mrestrict H' m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a).
Proof.
intros H H' m m' a Ha Hn E. pose proof (mbyte_of_aview tfibsegs H H' m m' a E) as Eb.
unfold mbyte in Eb. rewrite (seg_rom_none tfibsegs a Ha Hn) in Eb.
destruct (mrestrict H' m' (Z_to_bv 64 a)), (mrestrict H m (Z_to_bv 64 a)); congruence.
Qed.
(* an application byte is no user-poisoned shadow byte *)
Lemma wv_unpoison_app : forall ly S U (W : world tfibsegs) mem md a,
  ARU tfibsegs B ly S U W mem md -> app_addr a -> unpoison U mem (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Proof.
intros ly S U W mem md a HARU Ha. pose proof (app_addr_below_ceil a Ha) as Hc. pose proof ASAN_CEIL_range as (CR & _).
unfold unpoison. destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:E; [|reflexivity].
exfalso. destruct (ush_facts tfibsegs B ly S U W mem md _ HARU E) as (_ & L1 & L2).
rewrite (wz a ltac:(unfold ASAN_CEIL in *; lia)) in L1, L2.
unfold app_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
Lemma wv_kept_byte : forall ly S U (W : world tfibsegs) mem md ly' S' U' W' mem' md' a,
  ARU tfibsegs B ly S U W mem md -> ARU tfibsegs B ly' S' U' W' mem' md' -> app_addr a -> ~ in_img tfibsegs a ->
  aview tfibsegs (w_H W') (unpoison U' mem') a = aview tfibsegs (w_H W) (unpoison U mem) a ->
  rdW W' mem' (Z_to_bv 64 a) = rdW W mem (Z_to_bv 64 a).
Proof.
intros ly S U W mem md ly' S' U' W' mem' md' a HARU HARU' Ha Hn E.
pose proof (app_addr_below_ceil a Ha) as Hc. pose proof ASAN_CEIL_range as (CR & _).
pose proof (wv_raw_of_aview _ _ _ _ a ltac:(unfold ASAN_CEIL in *; lia) Hn E) as R.
unfold mrestrict in R |- *.
rewrite (wv_unpoison_app ly S U W mem md a HARU Ha), (wv_unpoison_app ly' S' U' W' mem' md' a HARU' Ha) in R.
exact R.
Qed.
(* fs's alloc.c statics are image bytes *)
Lemma wv_pstat_img : forall a, inFP FS_PSTAT_FP a -> in_img tfibsegs a.
Proof.
intros a (r & Hr & Hlo & Hhi). cbv [FS_PSTAT_FP In] in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in *.
- apply (wv_img_cover 0xa41c0 8 ltac:(vm_compute; reflexivity)). lia.
- apply (wv_img_cover 0x5daac0 8 ltac:(vm_compute; reflexivity)). lia.
- apply (wv_img_cover 0x5daae0 8 ltac:(vm_compute; reflexivity)). lia.
- apply (wv_img_cover 0x5dab00 8 ltac:(vm_compute; reflexivity)). lia.
Qed.
(* the tree survives a journal whose footprint FP is the statics and the writer's buffer: the root node (a live fake
   frame or a live block other than the buffer's) and every block of D (live reader blocks other than the buffer) are
   outside FP, so their bytes, and the blocks themselves, are kept *)
Lemma wv_node_kept : forall STK sp0 FP ly S U (W : world tfibsegs) mem md own ly' S' U' W' mem' md' k
    v t D UL buf cap,
  ajournal tfibsegs B STK sp0 FP ly S W (unpoison U mem) md own ly' S' W' (unpoison U' mem') md' k ->
  ARU tfibsegs B ly S U W mem md -> ARU tfibsegs B ly' S' U' W' mem' md' ->
  (forall a, inFP FP a -> inFP FS_PSTAT_FP a \/ (cap <> 0 /\ buf - HEAD <= a < buf + cap)) ->
  (cap <> 0 -> In (buf - HEAD, cap + HEAD) (ablocks B ly S)) -> 0 <= cap ->
  PjStruct.pj_node tfibsegs (rdW W mem) (fun a k => In (a, k) UL) v t D ->
  FSH_Fn_reader.pobj tfibsegs B ly S W mem v ->
  ublocks_ok B tfibsegs ly S W mem UL -> (forall a k, In (a, k) D -> In (a, k) UL /\ a <> buf) ->
  (cap <> 0 -> v + 56 <= buf - HEAD \/ buf + cap <= v) ->
  PjStruct.pj_node tfibsegs (rdW W' mem') (fun a k => In (a, k) UL) v t D.
Proof.
intros STK sp0 FP ly S U W mem md own ly' S' U' W' mem' md' k v t D UL buf cap
  HJ HARU HARU' HFP Hbuf Hcap0 HN HPO HUL HD Hroot.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof HARU as (HAR & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _ & F4 & Hgone & _).
assert (Hdec : forall x y : Z * Z, {x = y} + {x <> y}) by (decide equality; apply Z.eq_dec).
(* a byte of a block live at the start, outside FP, is kept *)
assert (BLK : forall p n a, In (p, n) (ablocks B ly S) -> p <= a < p + req_size n -> ~ inFP FP a ->
  rdW W' mem' (Z_to_bv 64 a) = rdW W mem (Z_to_bv 64 a)).
{ intros p n a Hin Hr Hnf.
  destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md p n HAR Hin) as (_ & _ & _ & [Hh1 Hh2] & _).
  assert (Hin' : In (p, n) (ablocks B ly' S')).
  { destruct (in_dec Hdec (p, n) (ablocks B ly' S')) as [H|H]; [exact H|].
    exfalso. apply Hnf. replace a with (p + (a - p)) by lia. apply (Hgone p n (a - p) Hin H). lia. }
  apply (wv_kept_byte ly S U W mem md ly' S' U' W' mem' md' a HARU HARU'
    (in_app_addr _ _ _ (conj Hh1 Hh2) Hr) (blk_img tfibsegs B LAWS ly S W (unpoison U mem) md p n a HAR Hin Hr)).
  replace a with (p + (a - p)) by lia. apply (F2 p n (a - p) Hin Hin'); [lia|]. replace (p + (a - p)) with a by lia.
  exact Hnf. }
(* the buffer's range *)
assert (NFP : forall a, ~ in_img tfibsegs a -> (cap <> 0 -> a < buf - HEAD \/ buf + cap <= a) -> ~ inFP FP a).
{ intros a Hn Hb Hf. destruct (HFP a Hf) as [Hs | (Hc & H1 & H2)]; [exact (Hn (wv_pstat_img a Hs))|].
  destruct (Hb Hc); lia. }
apply (PjStruct.pj_node_frame tfibsegs t (rdW W mem) _ (rdW W' mem') _ v D HN); [intros a0 k0 H; exact (proj1 (HD a0 k0 H))|].
intros x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). pose proof (bv_unsigned_in_range 64 x) as Rx.
change (bv_modulus 64) with (2 ^ 64) in Rx. set (a := bv_unsigned x) in *.
destruct Hx as [Hv | ((a0 & k0) & Hb & Hh)].
- (* the root node *)
  destruct HPO as ([((cid & pos & Hin & Hc0 & Hal & Hlo & Hhi) & _ & _) | ((b & m & Hin & Hlo & Hhi) & _ & _)] & _).
  + destruct (frames_bounds tfibsegs B LAWS ly S W (unpoison U mem) md cid pos HAR Hin) as (Hf0 & Hfc & Happ).
    assert (Hni : ~ in_img tfibsegs a) by (apply (frm_img tfibsegs B LAWS ly S W (unpoison U mem) md cid pos a HAR Hin); lia).
    apply (wv_kept_byte ly S U W mem md ly' S' U' W' mem' md' a HARU HARU' (in_app_addr _ _ a Happ ltac:(lia)) Hni).
    apply (F4 cid pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia|].
    apply NFP; [exact Hni|]. intros Hc. destruct (Hroot Hc); lia.
  + apply (BLK b m a Hin); [unfold HEAD in Hlo; lia|].
    apply NFP; [apply (blk_img tfibsegs B LAWS ly S W (unpoison U mem) md b m a HAR Hin); unfold HEAD in Hlo; lia|].
    intros Hc. destruct (Hroot Hc); lia.
- (* a block of D *)
  destruct (HD a0 k0 Hb) as [HinUL Hne]. destruct (HUL a0 k0 HinUL) as (Hin & H16 & Hk0 & _).
  unfold PjStruct.pj_holds in Hh. cbn [fst snd] in Hh.
  pose proof (req_size_pos (k0 + HEAD) ltac:(unfold HEAD; lia)) as (RQ1 & RQ2).
  assert (Hr : a0 - HEAD <= a < a0 - HEAD + req_size (k0 + HEAD)) by (unfold HEAD in *; lia).
  apply (BLK (a0 - HEAD) (k0 + HEAD) a Hin Hr).
  apply NFP; [exact (blk_img tfibsegs B LAWS ly S W (unpoison U mem) md _ _ a HAR Hin Hr)|].
  intros Hc. pose proof (Hbuf Hc) as Hbin.
  assert (Hneq : (a0 - HEAD, k0 + HEAD) <> (buf - HEAD, cap + HEAD)) by (intros E; injection E as E1 _; lia).
  pose proof (sep_blocks tfibsegs B LAWS ly S W (unpoison U mem) md _ _ _ _ HAR Hin Hbin Hneq) as Hsep.
  pose proof (req_size_pos (cap + HEAD) ltac:(unfold HEAD; lia)) as (RQ3 & RQ4).
  unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. unfold HEAD in *. lia.
Qed.

(* a byte that keeps its value keeps its writability (wview reads the memory only at the address asked) *)
Lemma wv_writable_eq : forall (m m' : word -> option byte) a,
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> (writable_at tfibsegs m a <-> writable_at tfibsegs m' a).
Proof. intros m m' a H. unfold writable_at, wview. rewrite H. reflexivity. Qed.
(* write_value's stack covers put's, put_string's and indent's *)
Lemma wv_stk_callees : forall m,
  STK_put <= STK_write_value m /\ STK_put_string <= STK_write_value m /\ STK_indent <= STK_write_value m.
Proof. intros m. destruct m as [|m]; cbn [STK_write_value]; unfold zmaxl, FRAME_write_value; cbn [fold_right]; lia. Qed.
Lemma wv_stk_frame : forall m, WV_F <= STK_write_value m.
Proof. intros m. destruct m as [|m]; cbn [STK_write_value]; unfold zmaxl, FRAME_write_value, WV_F; cbn [fold_right]; lia. Qed.
(* the writer's footprint is the statics and the buffer *)
Lemma wv_fp_cases : forall buf cap a, inFP (FS_PSTAT_FP ++ wbuf_fp buf cap) a ->
  inFP FS_PSTAT_FP a \/ (cap <> 0 /\ buf - HEAD <= a < buf + cap).
Proof.
intros buf cap a H. apply inFP_app in H as [H|H]; [left; exact H|right].
unfold wbuf_fp in H. destruct (Z.eqb_spec cap 0) as [E|E]; [exact (False_ind _ (inFP_nil a H))|].
destruct H as (r & [<-|[]] & H1 & H2). cbn [fst snd] in *. split; [exact E | lia].
Qed.

(* ================= the callees and the kit gaps, as Section hypotheses ================= *)
(* the leaf arms' tail callees (put, put_string) *)
Hypothesis HPUT : put_spec B tfibsegs.
Hypothesis HPS : put_string_spec B tfibsegs.

(* ---- the container arms' callees and kit gaps (array / object: put of the brackets, separators and commas,
   indent, put_string of the keys, write_value at the next level) ---- *)
Hypothesis HIND : indent_spec B tfibsegs.
(* the number arm's strlen interceptor (S0's FSH_Gen.astrlen_realizesU at fs.asan-ubsan's PC_strlen 0x426c4); the number
   arm (a Theorem Labs lane, lib/B/FSW_write_value_num.v) uses it, as A's walk does *)
Hypothesis HSLEN : astrlen_realizesU tfibsegs B PC_strlen.
(* the container arms wv_arr / wv_obj are the Theorem Labs lane's (lib/B), and the closing theorem the Theorem Labs lane's
   (lib/B/FSW_write_value.v); neither is a hypothesis of this file *)
(* the callee-footprint relation of the FP-keyed ajournal_sub is FSW_K3.fsw_fp_sub (S0's kit) *)
(* the TAIL step and the raised-top after-call step: proved by a part of a Theorem Labs lane (a working branch
   72cacaf9a57, ZZwv_defs.v), folded here; they compose through FSW_K3.fsw_ajournal_sub5, whose premise is S0's
   five-arm fsw_fp_sub (kit b04db294041) word for word *)
(* KIT ITEM (the arms' TAIL step, proved here from fsw_ajournal_sub5): the caller's journal from entry to the
   jump may already hold the calls the container arm made (k > 0, the state and the buffer moved); the callee,
   entered at the jump with the caller's ra and callee-saved registers, returns to the caller's caller. *)
Lemma wvc_tail_otJ : forall STK STKc sp0 FP FP1 ly S U (W0 W : world tfibsegs) mem md lyc Sc Uc memJ mdJ
    (regs regsJ : bvmap 5 word) k kc U'
    (Q : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) W' c',
  ajournal tfibsegs B STK sp0 FP ly S W0 (unpoison U mem) md [] lyc Sc W (unpoison Uc memJ) mdJ k ->
  ARU tfibsegs B lyc Sc Uc W memJ mdJ ->
  0 <= STKc <= STK ->
  getr regsJ 1 = getr regs 1 -> aregs_preserved regs regsJ ->
  fsw_fp_sub B ly S lyc Sc [] FP FP1 ->
  fpostU tfibsegs B STKc sp0 FP1 regsJ lyc Sc Uc W memJ mdJ kc U' Q W' c' ->
  fpostU tfibsegs B STK sp0 FP regs ly S U W0 mem md (k + kc) U' Q W' c'.
Proof.
intros STK STKc sp0 FP FP1 ly S U W0 W mem md lyc Sc Uc memJ mdJ regs regsJ k kc U' Q W' c'
  HJ HARU HSTK R1 HP HFP (ly' & S' & regs' & mem' & md' & Ec & HJc & OK' & PO' & HPc & HQ).
exists ly', S', regs', mem', md'.
split; [rewrite Ec, R1; reflexivity|].
split.
{ assert (H : ajournal tfibsegs B STK sp0 FP ly S W0 (unpoison U mem) md ([] ++ [])
    ly' S' W' (unpoison U' mem') md' (k + kc)).
  { apply (fsw_ajournal_sub5 B STK sp0 FP ly S W0 (unpoison U mem) md [] lyc Sc W (unpoison Uc memJ) mdJ k
      STKc sp0 FP1 [] ly' S' W' (unpoison U' mem') md' kc HJ HJc); [lia | lia | exact HFP]. }
  cbn [app] in H. exact H. }
split; [exact OK'|]. split; [exact PO'|].
split; [|exact HQ].
intros rr Hrr. rewrite (HPc rr Hrr). exact (HP rr Hrr).
Qed.
(* KIT ITEM (the container arms' after-call step; proved here from FSW_K3.fsw_ajournal_sub5 and
   FSW_rres.fsw_resume_after_rtU_args_chunks, so no hypothesis is taken): resume after a PROGRAM call whose post has
   a RAISED window top ot (FSH_Fn_FORM.md 3a: the callee writes the caller's pj_out above its sp), in the T resumed
   state fss_retT (the shadow-base cells, the extra regions rs and their atom facts gf). It is
   FSW_K3.fsw_after_callFPU_ot with FSW_rres's _args_chunks resume in place of the plain one; a Theorem Labs lane may lift it
   into FSW_K3 as fsw_after_callFPU_args_ot. *)
Lemma wvc_after_call_ot : forall STK sp0 FP own ly S U (W0 W : world tfibsegs) mem md lyc Sc Uc memC mdC k
    STKc FP1 ot f regsC ly' S' U' W' regs' mem' md' kc xs cs rs gf r,
  ajournal tfibsegs B STK sp0 FP ly S W0 (unpoison U mem) md own lyc Sc W (unpoison Uc memC) mdC k ->
  ARU tfibsegs B lyc Sc Uc W memC mdC ->
  ajournal tfibsegs B (STKc + (ot - spZ regsC)) ot FP1 lyc Sc W (unpoison Uc memC) mdC []
    ly' S' W' (unpoison U' mem') md' kc ->
  fsw_fp_sub B ly S lyc Sc own FP FP1 ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  aregs_preserved regsC regs' ->
  spZ regsC = sp0 - f -> 0 < f -> 0 <= STKc -> STKc + f <= STK -> f mod 16 = 0 ->
  spZ regsC <= ot -> ot <= sp0 ->
  regions_wf (fsT_ret_regions f cs rs) = true ->
  Forall (fun c => 0 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= f) cs ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs' (fs_extraT ++ xs)) (rdW W' mem') (sp0 - f)) cs ->
  Forall (region_ok tfibsegs (Ereg regs' (fs_extraT ++ xs)) (rdW W' mem')) rs ->
  pairwise_disjoint (Ereg regs' (fs_extraT ++ xs)) (fsT_ret_regions f cs rs) ->
  atoms_ok (Ereg regs' (fs_extraT ++ xs)) gf ->
  ajournal tfibsegs B STK sp0 FP ly S W0 (unpoison U mem) md own ly' S' W' (unpoison U' mem') md' (k + kc) /\
  ARU tfibsegs B ly' S' U' W' mem' md' /\
  st_ok tfibsegs (Ereg regs' (fs_extraT ++ xs)) (fss_retT r f cs rs gf)
    (restrict (w_H W') (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))).
Proof.
intros STK sp0 FP own ly S U W0 W mem md lyc Sc Uc memC mdC k STKc FP1 ot f regsC ly' S' U' W' regs' mem' md' kc
  xs cs rs gf r HJ HARU HJc HFP OK' PO' HP Hsp Hf HSc Hbud Hal Hot1 Hot2 Hwf Hin Hcs Hrs Hpd Hgf.
destruct HSS as [HBgot HBcell].
assert (HJ2 : ajournal tfibsegs B STK sp0 FP ly S W0 (unpoison U mem) md ([] ++ own)
  ly' S' W' (unpoison U' mem') md' (k + kc)).
{ apply (fsw_ajournal_sub5 B STK sp0 FP ly S W0 (unpoison U mem) md own lyc Sc W (unpoison Uc memC) mdC k
    (STKc + (ot - spZ regsC)) ot FP1 [] ly' S' W' (unpoison U' mem') md' kc HJ HJc); [lia | lia | exact HFP]. }
cbn [app] in HJ2.
assert (HARU' : ARU tfibsegs B ly' S' U' W' mem' md')
  by (pose proof HJ2 as (HAR2 & _); split; [exact HAR2 | split; [exact OK' | exact PO']]).
split; [exact HJ2|]. split; [exact HARU'|].
assert (Esp : spZ regs' = sp0 - f).
{ unfold spZ. rewrite (fsw_pres regsC regs' 2%bv HP ltac:(unfold acallee_saved; vm_compute; lia)). exact Hsp. }
exact (fsw_resume_after_rtU_args_chunks B STK sp0 FP ly S W0 (unpoison U mem) md own ly' S' U' W' mem' md' (k + kc)
  regs' f xs cs rs gf r HBgot HBcell HJ2 HARU' Esp Hf ltac:(lia) Hal Hwf Hcs Hrs Hpd Hgf).
Qed.
(* the writer's footprint against itself, while no block has moved *)
Lemma wv_fp_sub_self : forall ly S buf cap,
  (cap <> 0 -> In (buf - HEAD, cap + HEAD) (ablocks B ly S)) -> 0 <= cap ->
  fsw_fp_sub B ly S ly S [] (FS_PSTAT_FP ++ wbuf_fp buf cap) (FS_PSTAT_FP ++ wbuf_fp buf cap).
Proof.
intros ly S buf cap Hb Hc a Ha. pose proof Ha as Ha'.
destruct (wv_fp_cases buf cap a Ha) as [Hs | (Hc0 & H1 & H2)].
- right; right; left. split; [exact Ha' | exact (wv_pstat_img a Hs)].
- left. split; [exact Ha'|]. exists (buf - HEAD), (cap + HEAD). split; [exact (Hb Hc0)|].
  pose proof (req_size_pos (cap + HEAD) ltac:(unfold HEAD; lia)) as (RQ1 & RQ2). unfold HEAD in *. lia.
Qed.


(* ---- the memory a runtime callee leaves: its contracts keep the RESTRICTED view (aview / mrestrict) outside its stack
   window, not the raw memory at hidden addresses; the facts the arms carry all read through mrestrict ---- *)
Definition rsame (W : world tfibsegs) (m m' : word -> option byte) : Prop :=
  forall x, 0 <= x < alloc_ceiling -> mbyte tfibsegs (rdW W m') x = mbyte tfibsegs (rdW W m) x.
Lemma rsame_of_below : forall (W : world tfibsegs) m m', same_below m m' alloc_ceiling -> rsame W m m'.
Proof. intros W m m' H x Hx. unfold mbyte, mrestrict. rewrite (H x Hx). reflexivity. Qed.
Lemma rsame_mbyte : forall (W : world tfibsegs) m m' a, rsame W m m' -> 0 <= a < alloc_ceiling ->
  mbyte tfibsegs (rdW W m') a = mbyte tfibsegs (rdW W m) a.
Proof. intros W m m' a H Ha. exact (H a Ha). Qed.
(* off the image, a byte read through mbyte is the memory's own *)
Lemma wv_raw_of_mbyte : forall (m m' : word -> option byte) a, 0 <= a < 2 ^ 64 -> ~ in_img tfibsegs a ->
  mbyte tfibsegs m' a = mbyte tfibsegs m a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
intros m m' a Ha Hn E. unfold mbyte in E. rewrite (seg_rom_none tfibsegs a Ha Hn) in E.
destruct (m' (Z_to_bv 64 a)), (m (Z_to_bv 64 a)); congruence.
Qed.
Lemma rsame_aview : forall (W : world tfibsegs) m m' a, rsame W m m' -> 0 <= a < alloc_ceiling ->
  aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a.
Proof. intros W m m' a H Ha. unfold aview. rewrite (rsame_mbyte W m m' a H Ha). reflexivity. Qed.
Lemma rsame_val_mem : forall (W : world tfibsegs) m m' a (n : nat) v, rsame W m m' ->
  0 <= a -> a + Z.of_nat n <= alloc_ceiling -> val_mem tfibsegs (rdW W m) a n v -> val_mem tfibsegs (rdW W m') a n v.
Proof. intros W m m' a n v H H0 Hn Hv k Hk. rewrite (rsame_mbyte W m m' (a + Z.of_nat k) H ltac:(lia)). exact (Hv k Hk). Qed.
Lemma rsame_glob : forall (W : world tfibsegs) m m' live peak cnt fail,
  rsame W m m' -> fs_glob tfibsegs W m live peak cnt fail -> fs_glob tfibsegs W m' live peak cnt fail.
Proof.
intros W m m' live peak cnt fail Hs (G1 & G2 & G3 & G4 & R). pose proof asan_consts as (C1 & _).
unfold fs_glob, fs_glob_at. unfold G_LIVE, G_PEAK, G_COUNT, G_FAIL in *.
split; [apply (rsame_val_mem W m m'); [exact Hs | lia | lia | exact G1]|].
split; [apply (rsame_val_mem W m m'); [exact Hs | lia | lia | exact G2]|].
split; [apply (rsame_val_mem W m m'); [exact Hs | lia | lia | exact G3]|].
split; [apply (rsame_val_mem W m m'); [exact Hs | lia | lia | exact G4]|].
exact R.
Qed.
Lemma rsame_arodata : forall (W : world tfibsegs) m m', rsame W m m' ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) m) -> arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) m').
Proof.
intros W m m' Hs HR a Ha Ho He. pose proof asan_consts as (C1 & _).
assert (Hb : 0 <= a < alloc_ceiling).
{ destruct Ha as [(sg & Hin & Hw & Hr) | Hr]; [|unfold FS_RLO, FS_RHI in Hr; lia].
  assert (Hi : in_img tfibsegs a) by (exists sg; split; [exact Hin | exact Hr]).
  pose proof (fs_segs_img a Hi) as Hl. unfold FS_IMG_END in Hl. lia. }
rewrite (rsame_aview W m m' a Hs Hb). exact (HR a Ha Ho He).
Qed.
Lemma rsame_cstr_ok : forall (W : world tfibsegs) m m' p l,
  rsame W m m' -> cstr_ok tfibsegs W m p l -> cstr_ok tfibsegs W m' p l.
Proof.
intros W m m' p l Hs H. pose proof asan_consts as (C1 & _).
assert (AV : forall a, 0 <= a < alloc_ceiling -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a)
  by (intros a Ha; exact (rsame_aview W m m' a Hs Ha)).
unfold cstr_ok, cstr in H |- *.
repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
repeat match goal with |- _ /\ _ => split end; try assumption; lazymatch goal with
  | Hg : garr8 _ (mrestrict _ m) p (l ++ [0]) |- garr8 _ _ p (l ++ [0]) =>
      apply (garr8_frame tfibsegs _ _ p (l ++ [0]) Hg); intros a Ha; rewrite length_app in Ha; cbn [length] in Ha;
      apply (rsame_mbyte W m m' a Hs); lia
  | Hra : range_addressable (aview _ _ m) ?o ?q ?n |- range_addressable (aview _ _ m') ?o ?q ?n =>
      intros x Hx; destruct (Hra x Hx) as (s & Hs1 & Hs2); exists s; split; [|exact Hs2];
      rewrite AV; [exact Hs1|]; unfold shadow_of_addr, SHADOW_OFF; lia
  | Hhv : shadow_hull_vis (aview _ _ m) ?q ?n |- shadow_hull_vis (aview _ _ m') ?q ?n =>
      intros s Hsr; rewrite AV; [exact (Hhv s Hsr)|]; unfold shadow_addr, SHADOW_OFF in Hsr; lia
  | Htl : forall a, _ -> aview _ _ m a <> None |- forall a, _ -> aview _ _ m' a <> None =>
      (* the word holding the NUL ends at or below alloc_ceiling: p + |l| + 1 <= alloc_ceiling and alloc_ceiling is
         4096-aligned (YM05.alloc_ceiling_value), so (p + |l|) / 8 * 8 + 8 <= alloc_ceiling (FSW_K.cstr_ok_below's
         step, 60d0985773d) *)
      intros a Ha; rewrite AV; [exact (Htl a Ha)|];
      pose proof (Z.mod_pos_bound (p + Z.of_nat (length l)) 8 ltac:(lia));
      pose proof (Z.div_mod (p + Z.of_nat (length l)) 8 ltac:(lia));
      pose proof (Z.div_mod alloc_ceiling 4096 ltac:(lia));
      pose proof (proj2 YM05.alloc_ceiling_value); lia
  end.
Qed.
Lemma rsame_zbytes : forall (W : world tfibsegs) m m' s (l : list Z), rsame W m m' ->
  0 <= s -> s + Z.of_nat (length l) <= alloc_ceiling -> zbytes_at tfibsegs W m s l -> zbytes_at tfibsegs W m' s l.
Proof.
intros W m m' s l Hs H0 H1 H. unfold zbytes_at in *. apply (garr8_frame tfibsegs _ _ s l H).
intros a Ha. apply (rsame_mbyte W m m' a Hs). lia.
Qed.

(* ================= a TAIL call: the leaf arms' last step ================= *)
(* the jump state: write_value's frame popped, its callee-saved registers and ra restored (aregs_preserved); the memory
   differs from the entry's only below sp (the popped frame, a runtime callee's stack); the facts a tail callee's
   premises need, at the jump, for any callee stack STKc within write_value's *)
Lemma wv_jump : forall m ly S U (W : world tfibsegs) regs mem md ch ot o buf cap failed text live peak cnt fail
    regsJ memJ mdJ STKc,
  fpreU tfibsegs B (STK_write_value m) ly S U W regs mem md ch ->
  wout_ok B tfibsegs ly S W mem o buf cap failed text -> fs_glob tfibsegs W mem live peak cnt fail ->
  spZ regs <= o -> o + 32 <= ot -> ot mod 16 = 0 -> ot <= ly_top ly ->
  wv_chain_o U W mem regs o ->
  (forall a, spZ regs <= a < ot -> apresent (w_H W) mem a) ->
  ajournal tfibsegs B (STK_write_value m + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S W (unpoison U mem) md []
    ly S W (unpoison U memJ) mdJ 0 ->
  ARU tfibsegs B ly S U W memJ mdJ ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_write_value m <= a < spZ regs) ->
     mbyte tfibsegs (rdW W memJ) a = mbyte tfibsegs (rdW W mem) a) ->
  aregs_preserved regs regsJ -> getr regsJ 1 = getr regs 1 ->
  0 <= STKc <= STK_write_value m ->
  fpreU tfibsegs B STKc ly S U W regsJ memJ mdJ ch /\ spZ regsJ = spZ regs /\
  wout_ok B tfibsegs ly S W memJ o buf cap failed text /\ fs_glob tfibsegs W memJ live peak cnt fail /\
  wv_chain_o U W memJ regsJ o /\
  (forall a, spZ regsJ <= a < ot -> apresent (w_H W) memJ a) /\
  rsame W mem memJ /\
  (forall a, spZ regs <= a < 2 ^ 64 -> rdW W memJ (Z_to_bv 64 a) = rdW W mem (Z_to_bv 64 a)).
Proof.
intros m ly S U W regs mem md ch ot o buf cap failed text live peak cnt fail regsJ memJ mdJ STKc
  HPRE HOUT HGLOB Hspo Hoot Hot16 Hottop HCHO HPRESENT HJ HARUJ HMJ HP R1 HSTKc.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HPRE as (HPREU & HRO).
pose proof HPREU as (HAP & HUOK & HUPO).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (wv_stk_frame m) as HSTKw.
(* ---- the memory at the jump: the entry's (restricted view) at and above sp, and below alloc_ceiling ---- *)
assert (MB : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_write_value m <= a < spZ regs) ->
  mbyte tfibsegs (rdW W memJ) a = mbyte tfibsegs (rdW W mem) a) by exact HMJ.
assert (MWE : forall a, spZ regs <= a < 2 ^ 64 -> rdW W memJ (Z_to_bv 64 a) = rdW W mem (Z_to_bv 64 a)).
{ intros a Ha. apply wv_raw_of_mbyte; [lia | | apply MB; lia].
  intros Hi. pose proof (fs_segs_img a Hi) as Hl. unfold FS_IMG_END in Hl. lia. }
assert (MEQ : forall a, spZ regs <= a < 2 ^ 64 ->
  w_H W (Z_to_bv 64 a) = false -> memJ (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
{ intros a Ha Hh. pose proof (MWE a Ha) as E. unfold mrestrict in E. rewrite Hh in E. exact E. }
assert (SB : rsame W mem memJ) by (intros x Hx; apply MB; lia).
assert (MVH : forall a k v0, spZ regs <= a -> a + Z.of_nat k <= 2 ^ 64 ->
  val_mem tfibsegs (rdW W mem) a k v0 -> val_mem tfibsegs (rdW W memJ) a k v0)
  by (intros a k v0 Ha Hk Hv i Hi; rewrite (MB (a + Z.of_nat i) ltac:(lia) ltac:(lia)); exact (Hv i Hi)).
assert (AV : forall a, spZ regs <= a < 2 ^ 64 ->
  aview tfibsegs (w_H W) (unpoison U memJ) a = aview tfibsegs (w_H W) (unpoison U mem) a).
{ intros a Ha. apply (aview_eq_of tfibsegs). unfold mrestrict, unpoison.
  destruct (w_H W (Z_to_bv 64 a)) eqn:Eh; [reflexivity|].
  destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))); [reflexivity|]. apply MEQ; [lia | exact Eh]. }
(* ---- the registers at the jump ---- *)
assert (PR : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regsJ r = getr regs r)
  by (intros r Hr; exact (fsw_pres regs regsJ r HP Hr)).
assert (R2 : getr regsJ 2%bv = getr regs 2%bv) by (apply PR; unfold acallee_saved; vm_compute; lia).
assert (R3 : getr regsJ 3%bv = getr regs 3%bv) by (apply PR; unfold acallee_saved; vm_compute; lia).
assert (R4 : getr regsJ 4%bv = getr regs 4%bv) by (apply PR; unfold acallee_saved; vm_compute; lia).
assert (R8 : getr regsJ 8%bv = getr regs 8%bv) by (apply PR; unfold acallee_saved; vm_compute; lia).
assert (Esp : spZ regsJ = spZ regs) by (unfold spZ; rewrite R2; reflexivity).
(* ---- the out-object at the jump ---- *)
destruct HOUT as (Ho8 & Ho0 & Hotop & HOW & Hbuf64 & Hcap64 & Vbuf & Vlen & Vcap & Vfail & Hf01 & Htok & Hcase).
assert (HOUTJ : wout_ok B tfibsegs ly S W memJ o buf cap failed text).
{ unfold wout_ok. split; [exact Ho8|]. split; [exact Ho0|]. split; [exact Hotop|]. split.
  { intros i Hi. destruct (HOW i Hi) as [Hw Hpr]. split.
    - exact (proj1 (wv_writable_eq (rdW W mem) (rdW W memJ) (o + i) (MWE (o + i) ltac:(lia))) Hw).
    - destruct Hpr as (Hh & b & Hb). split; [exact Hh|]. exists b. rewrite (MEQ (o + i) ltac:(lia) Hh). exact Hb. }
  split; [exact Hbuf64|]. split; [exact Hcap64|].
  split; [exact (MVH o 8%nat buf ltac:(lia) ltac:(lia) Vbuf)|].
  split; [exact (MVH (o + 8) 8%nat (Z.of_nat (length text)) ltac:(lia) ltac:(lia) Vlen)|].
  split; [exact (MVH (o + 16) 8%nat cap ltac:(lia) ltac:(lia) Vcap)|].
  split; [exact (MVH (o + 24) 4%nat failed ltac:(lia) ltac:(lia) Vfail)|].
  split; [exact Hf01|]. split; [exact Htok|].
  destruct Hcase as [Hz | (Hj & HRB & Hlt & HZB')]; [left; exact Hz | right].
  pose proof HRB as (Hin & Hb16 & Hcap0 & Vhead).
  destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md (buf - HEAD) (cap + HEAD) HAR Hin)
    as (_ & Hb4096 & Hbceil & _ & _ & _ & _).
  pose proof (req_size_pos (cap + HEAD) ltac:(unfold HEAD; lia)) as (RQ1 & RQ2).
  split; [exact Hj|]. split; [|split; [exact Hlt|]].
  - unfold fs_rblock. split; [exact Hin|]. split; [exact Hb16|]. split; [exact Hcap0|].
    exact (rsame_val_mem W mem memJ (buf - HEAD) 8%nat cap SB
             ltac:(unfold HEAD in *; lia) ltac:(unfold HEAD in *; lia) Vhead).
  - unfold zbytes_at in HZB' |- *. apply (garr8_frame tfibsegs _ _ buf (text ++ [0]) HZB').
    intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
    apply (rsame_mbyte W mem memJ a SB). unfold HEAD in *. lia. }
split.
{ (* the callee's premise at the jump *)
  split; [|exact (rsame_arodata W mem memJ SB HRO)].
  apply (fsw_fpreU_atFP B (STK_write_value m + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S U W
    (unpoison U mem) md [] ly S W memJ mdJ 0 regsJ STKc (spZ regs - ot) ch HJ HARUJ (rsame_arodata W mem memJ SB HRO)).
  - lia.
  - rewrite Zminus_mod, Hsp16, Hot16. reflexivity.
  - lia.
  - lia.
  - lia.
  - rewrite R1. exact Hra.
  - unfold raZ. rewrite R1. exact Hra4.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - unfold s0Z. rewrite Esp, R8.
    apply (achain_kept ly (aview tfibsegs (w_H W) (unpoison U mem)) _ (spZ regs) (s0Z regs) ch (spZ regs) Hch
      ltac:(lia) ltac:(lia)).
    exact AV. }
split; [exact Esp|]. split; [exact HOUTJ|].
split; [exact (rsame_glob W mem memJ live peak cnt fail SB HGLOB)|].
split.
{ unfold wv_chain_o in *. rewrite Esp. unfold raZ. rewrite R1.
  destruct HCHO as [HCHO | (H16 & ra & nfp & Hra8 & Hnfp & Hend)]; [left; exact HCHO | right].
  split; [exact H16|]. exists ra, nfp.
  rewrite !(rdword_ext (aview tfibsegs (w_H W) (unpoison U mem)) (aview tfibsegs (w_H W) (unpoison U memJ)))
    by (intros kk Hkk; apply AV; lia).
  auto. }
split.
{ intros a Ha. rewrite Esp in Ha. destruct (HPRESENT a Ha) as (Hh & b & Hb). split; [exact Hh|]. exists b.
  rewrite (MEQ a ltac:(lia) Hh). exact Hb. }
split; [exact SB|].
intros a Ha. apply MWE; lia.
Qed.

(* a tail callee's post, at the jump's memory, is write_value's post at the entry's: the journal is composed by
   fsw_tailU_ot, wkeep is carried over the popped frame, and the tree is kept (wv_node_kept) *)
Lemma wv_tail_post : forall m ly S U (W : world tfibsegs) regs mem md ch ot o v t D UL buf cap failed text live peak
    cnt regsJ memJ mdJ STKc kk U' (st' : WriterApp.wst) buf'
    (Qc : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop) W' c',
  fpreU tfibsegs B (STK_write_value m) ly S U W regs mem md ch ->
  wout_ok B tfibsegs ly S W mem o buf cap failed text ->
  spZ regs <= o -> o + 32 <= ot -> ot <= ly_top ly ->
  PjStruct.pj_node tfibsegs (rdW W mem) (fun a k => In (a, k) UL) v t D ->
  FSH_Fn_reader.pobj tfibsegs B ly S W mem v ->
  ublocks_ok B tfibsegs ly S W mem UL -> (forall a k, In (a, k) D -> In (a, k) UL /\ a <> buf) ->
  (cap <> 0 -> v + 56 <= buf - HEAD \/ buf + cap <= v) ->
  ajournal tfibsegs B (STK_write_value m + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S W (unpoison U mem) md []
    ly S W (unpoison U memJ) mdJ 0 ->
  ARU tfibsegs B ly S U W memJ mdJ ->
  (forall a, spZ regs <= a < 2 ^ 64 -> rdW W memJ (Z_to_bv 64 a) = rdW W mem (Z_to_bv 64 a)) ->
  aregs_preserved regs regsJ -> getr regsJ 1 = getr regs 1 -> spZ regsJ = spZ regs ->
  0 <= STKc <= STK_write_value m ->
  (forall ly' S' W'' regs' mem' md', Qc ly' S' W'' regs' mem' md' ->
     wout_ok B tfibsegs ly' S' W'' mem' o buf' (WriterApp.w_cap st') (WriterApp.w_failed st') (WriterApp.w_text st') /\
     wbudget_kept S S' failed cap cnt (WriterApp.w_failed st') (WriterApp.w_cap st') (WriterApp.w_cnt st') /\
     bswap (ablocks B ly S) (ablocks B ly' S') buf buf' cap (WriterApp.w_cap st') /\
     wkeep tfibsegs W W'' memJ mem' (spZ regsJ) ot o 32 /\
     (exists peak', peak <= peak' <= Z.max peak (live - cap + WriterApp.w_cap st') /\
        fs_glob tfibsegs W'' mem' (live + WriterApp.w_cap st' - cap) peak' (WriterApp.w_cnt st') (WriterApp.w_fail st'))) ->
  fpostU tfibsegs B (STKc + (ot - spZ regsJ)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) regsJ ly S U W memJ mdJ kk U' Qc W' c' ->
  fpostU tfibsegs B (STK_write_value m + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) regs ly S U W mem md kk U'
    (fun ly' S' W'' regs' mem' md' =>
       wout_ok B tfibsegs ly' S' W'' mem' o buf' (WriterApp.w_cap st') (WriterApp.w_failed st') (WriterApp.w_text st') /\
       wbudget_kept S S' failed cap cnt (WriterApp.w_failed st') (WriterApp.w_cap st') (WriterApp.w_cnt st') /\
       bswap (ablocks B ly S) (ablocks B ly' S') buf buf' cap (WriterApp.w_cap st') /\
       wkeep tfibsegs W W'' mem mem' (spZ regs) ot o 32 /\
       PjStruct.pj_node tfibsegs (rdW W'' mem') (fun a k => In (a, k) UL) v t D /\
       (exists peak', peak <= peak' <= Z.max peak (live - cap + WriterApp.w_cap st') /\
          fs_glob tfibsegs W'' mem' (live + WriterApp.w_cap st' - cap) peak' (WriterApp.w_cnt st') (WriterApp.w_fail st')))
    W' c'.
Proof.
intros m ly S U W regs mem md ch ot o v t D UL buf cap failed text live peak cnt regsJ memJ mdJ STKc kk U' st' buf'
  Qc W' c' (HPREU & _) HOUT Hspo Hoot Hottop HN HPO HUL HD Hroot HJ HARUJ MWE HP R1 Esp HSTKc HQc Hwp.
pose proof (fsw_ARU B _ ly S U W regs mem md ch HPREU) as HARU0.
pose proof HPREU as ((_ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & H47 & _ & _ & Htop2) & _) & _).
pose proof HOUT as (_ & _ & _ & _ & _ & Hcap64 & _ & _ & _ & _ & _ & _ & Hcase).
eapply wv_fpostU_mono.
{ rewrite <- (Z.add_0_l kk).
  apply (wvc_tail_otJ (STK_write_value m + (ot - spZ regs)) (STKc + (ot - spZ regsJ)) ot
    (FS_PSTAT_FP ++ wbuf_fp buf cap) (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S U W W mem md ly S U memJ mdJ regs regsJ
    0 kk U' Qc W' c' HJ HARUJ ltac:(rewrite Esp; lia) R1 HP).
  - apply wv_fp_sub_self; [|lia].
    intros Hc0. destruct Hcase as [(Hz & _) | (_ & (Hbin & _) & _)]; [exfalso; exact (Hc0 Hz) | exact Hbin].
  - exact Hwp. }
cbv beta. intros ly' S' regs' mem' md' HJ' OK' PO' HP' HQ.
destruct (HQc _ _ _ _ _ _ HQ) as (Q1 & Q2 & Q3 & Q4 & Q5).
assert (HARU' : ARU tfibsegs B ly' S' U' W' mem' md') by (split; [exact (proj1 HJ') | split; [exact OK' | exact PO']]).
split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|].
split.
{ intros a Ha Hno. rewrite Esp in Q4. destruct (Q4 a Ha Hno) as [E1 E2]. split.
  - rewrite E1. unfold mbyte. rewrite (MWE a ltac:(lia)). reflexivity.
  - rewrite <- E2. apply wv_writable_eq. apply MWE. lia. }
split; [|exact Q5].
destruct Hcase as [(Hc0 & _ & _) | (_ & (Hbin & _ & _ & _) & _ & _)].
- apply (wv_node_kept _ _ _ ly S U W mem md [] ly' S' U' W' mem' md' _ v t D UL buf cap HJ' HARU0 HARU'
    (wv_fp_cases buf cap) ltac:(intros Hc; exfalso; exact (Hc Hc0)) (proj1 Hcap64) HN HPO HUL HD Hroot).
- apply (wv_node_kept _ _ _ ly S U W mem md [] ly' S' U' W' mem' md' _ v t D UL buf cap HJ' HARU0 HARU'
    (wv_fp_cases buf cap) (fun _ => Hbin) (proj1 Hcap64) HN HPO HUL HD Hroot).
Qed.

(* the tail call of put: a0 = o, a1 = s, a2 = n *)
Lemma wv_tail_put : forall m ly S U (W : world tfibsegs) regs mem md ch ot o v pretty d (t : PjTree.jv) D UL
    buf cap failed text live peak cnt fail regsJ memJ mdJ s (bs : list Z),
  fpreU tfibsegs B (STK_write_value m) ly S U W regs mem md ch -> fs_heads B ly S U ->
  Z.of_nat (length (frames S)) <= FRL_CRT_CALLEE ->
  wout_ok B tfibsegs ly S W mem o buf cap failed text -> fs_glob tfibsegs W mem live peak cnt fail ->
  (cap <> 0 -> In (buf - HEAD, HEAD) U) ->
  spZ regs <= o -> o + 32 <= ot -> ot mod 16 = 0 -> ot <= ly_top ly ->
  wv_chain_o U W mem regs o ->
  (forall a, spZ regs <= a < ot -> apresent (w_H W) mem a) ->
  PjStruct.pj_node tfibsegs (rdW W mem) (fun a k => In (a, k) UL) v t D ->
  FSH_Fn_reader.pobj tfibsegs B ly S W mem v ->
  ublocks_ok B tfibsegs ly S W mem UL -> (forall a k, In (a, k) D -> In (a, k) UL /\ a <> buf) ->
  (cap <> 0 -> v + 56 <= buf - HEAD \/ buf + cap <= v) ->
  WriterValue.wvpieces t (negb (pretty =? 0)) d = [bs] ->
  Z.of_nat (length text) + Z.of_nat (length bs) + 1 <= WMAX ->
  cap <= WMAX -> cap <= live -> wbudget_pre S cap cnt live
    (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) (WriterValue.wvpieces t (negb (pretty =? 0)) d)) ->
  zbytes_at tfibsegs W mem s bs -> wsrc_kept B tfibsegs ly S U W mem buf s bs -> WriterSpec.bytes_ok bs ->
  0 <= s -> s + Z.of_nat (length bs) <= alloc_ceiling ->
  ajournal tfibsegs B (STK_write_value m + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S W (unpoison U mem) md []
    ly S W (unpoison U memJ) mdJ 0 ->
  ARU tfibsegs B ly S U W memJ mdJ ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_write_value m <= a < spZ regs) ->
     mbyte tfibsegs (rdW W memJ) a = mbyte tfibsegs (rdW W mem) a) ->
  aregs_preserved regs regsJ -> getr regsJ 1 = getr regs 1 ->
  getr regsJ 10 = w64 o -> getr regsJ 11 = w64 s -> getr regsJ 12 = w64 (Z.of_nat (length bs)) ->
  SRr tfibsegs W (cfg_at tfibsegs A_put regsJ memJ mdJ)
    (wv_post m ot o v pretty d t D UL buf cap failed text live peak cnt fail regs ly S U W mem md).
Proof.
intros m ly S U W regs mem md ch ot o v pretty d t D UL buf cap failed text live peak cnt fail regsJ memJ mdJ s bs
  HPRE HHEADS HFRL HOUT HGLOB HUH Hspo Hoot Hot16 Hottop HCHO HPRESENT HN HPO HUL HD Hroot HWV HROOM HCAP HCL HBUD HZB HSRC HBOK Hs0 Hsn HJ HARUJ HMJ HP R1 G10 G11 G12.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof HPRE as ((HAP & _) & _). pose proof HAP as (HAR & _).
destruct (wv_stk_callees m) as (SKp & _ & _).
assert (SKp0 : 0 <= STK_put) by (vm_compute; discriminate).
destruct (wv_jump m ly S U W regs mem md ch ot o buf cap failed text live peak cnt fail regsJ memJ mdJ STK_put
  HPRE HOUT HGLOB Hspo Hoot Hot16 Hottop HCHO HPRESENT HJ HARUJ HMJ HP R1 ltac:(lia))
  as (HPREJ & Esp & HOUTJ & HGLOBJ & HCHOJ & HPRJ & SB & MWE).
(* the source at the jump: below alloc_ceiling, so the entry's *)
assert (HZBJ : zbytes_at tfibsegs W memJ s bs).
{ unfold zbytes_at in HZB |- *. apply (garr8_frame tfibsegs _ _ s bs HZB).
  intros a Ha. apply (rsame_mbyte W mem memJ a SB). lia. }
assert (HSRCJ : wsrc_kept B tfibsegs ly S U W memJ buf s bs).
{ destruct HSRC as [H0 | [(p & k & Hp & (Hin & H16 & Hk & Vh) & Hr) | [H2 | H3]]]; [left; exact H0| | right; right; left; exact H2
  | right; right; right; exact H3].
  right; left. exists p, k. split; [exact Hp|]. split; [|exact Hr].
  destruct (al_blocks _ _ LAWS ly S W _ md (p - HEAD) (k + HEAD) HAR Hin) as (_ & Hp4096 & Hpceil & _).
  pose proof (req_size_pos (k + HEAD) ltac:(unfold HEAD; lia)) as (RQ1 & RQ2).
  split; [exact Hin|]. split; [exact H16|]. split; [exact Hk|].
  exact (rsame_val_mem W mem memJ (p - HEAD) 8%nat k SB
           ltac:(unfold HEAD in *; lia) ltac:(unfold HEAD in *; lia) Vh). }
eapply SRr_mono.
{ pose proof HPRE as (((_ & _ & _ & _ & _ & (_ & _ & Hc & Hsl & _) & _) & _) & _).
  apply (HPUT ly S U W regsJ memJ mdJ ch ot o s (Z.of_nat (length bs)) buf cap failed text bs live peak cnt fail
    HPREJ HHEADS).
  - unfold FRL_CRT_CALLEE in *. lia.
  - exact G10.
  - exact G11.
  - exact G12.
  - exact HOUTJ.
  - exact HGLOBJ.
  - exact HUH.
  - rewrite Esp. exact Hspo.
  - exact Hoot.
  - exact Hot16.
  - exact Hottop.
  - exact HCHOJ.
  - exact HPRJ.
  - exact HZBJ.
  - exact HSRCJ.
  - reflexivity.
  - exact HBOK.
  - split; [exact Hs0 | exact Hsn].
  - left. lia.
  - exact HROOM.
  - exact HCAP.
  - exact HCL.
  - rewrite HWV in HBUD. exact HBUD. }
cbv beta. intros W' c' Hle (st' & buf' & U' & Est & Hus & Hwp).
exists st', buf', U'. split; [rewrite HWV; exact Est|]. split; [exact Hus|].
unfold wpost in *.
refine (wv_tail_post m ly S U W regs mem md ch ot o v t D UL buf cap failed text live peak cnt regsJ memJ mdJ
  STK_put _ U' st' buf' _ W' c' HPRE HOUT Hspo Hoot Hottop HN HPO HUL HD Hroot HJ HARUJ MWE HP R1 Esp ltac:(lia) _ Hwp).
intros ly' S' W'' regs' mem' md' (Q1 & Q2 & Q3 & Q4 & Q5 & _). auto.
Qed.

(* ================= the literal arms: null / false / true ================= *)
(* the bytes of a read-only literal, from rom_view, checked against the image by computation *)
Lemma wv_rom_zbytes : forall (W : world tfibsegs) mem s (l : list Z),
  rom_view tfibsegs W mem ->
  forallb (fun j => existsb (fun sg => negb (seg_writable sg) && (Z.of_N (seg_base sg) <=? s + Z.of_nat j)
                       && (s + Z.of_nat j <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) tfibsegs
            && match seg_rom tfibsegs (Z_to_bv 64 (s + Z.of_nat j)) with
               | Some b => bv_unsigned b =? nth j l 0 | None => false end
            && (0 <=? nth j l 0) && (nth j l 0 <? 256)) (seq 0 (length l)) = true ->
  zbytes_at tfibsegs W mem s l.
Proof.
intros W mem s l HR Hb j Hj.
rewrite forallb_forall in Hb. specialize (Hb j (proj2 (in_seq _ _ _) (conj (Nat.le_0_l j) Hj))).
apply andb_true_iff in Hb as [Hb H4]. apply andb_true_iff in Hb as [Hb H3]. apply andb_true_iff in Hb as [H1 H2].
apply Z.ltb_lt in H4. apply Z.leb_le in H3.
destruct (seg_rom tfibsegs (Z_to_bv 64 (s + Z.of_nat j))) as [b|] eqn:Eb; [|discriminate]. apply Z.eqb_eq in H2.
split; [|lia].
intros k Hk. assert (k = 0%nat) as -> by lia. rewrite Z.add_0_r.
apply wv_rom_byte; [exact HR | exact (wv_in_rom_b _ H1) |]. rewrite Eb. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned, H2. unfold bv_wrap. change (bv_modulus 8) with 256.
try unfold le_byte. try unfold YO0f.le_byte. cbn [Z.of_nat Pos.of_succ_nat Z.mul]. rewrite Z.shiftr_0_r.
rewrite !(Z.mod_small (nth j l 0)) by (cbn; lia). reflexivity.
Qed.

(* ---- the arms' shared steps ---- *)
(* the entry: the symbolic state, the shadow entry, the journal at the raised top ot (FP = [] up to the jump), ARU *)
Lemma wv_start : forall k ly S U (W : world tfibsegs) regs mem md ch ot v ty num str kids keys n cap0 slo shi buf cap,
  fpreU tfibsegs B (STK_write_value (2 - k)) ly S U W regs mem md ch ->
  getr regs 11 = w64 v -> FSH_Fn_reader.pobj tfibsegs B ly S W mem v ->
  PjStruct.pj_hdr tfibsegs (rdW W mem) v ty num str kids keys n cap0 -> slo <= str <= shi ->
  spZ regs <= ot -> ot mod 16 = 0 -> ot <= ly_top ly -> (forall a, spZ regs <= a < ot -> apresent (w_H W) mem a) ->
  st_ok tfibsegs (Ereg regs (fs_extraT ++ wv_xs str kids keys n)) (wv_ss0 ty slo shi)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 A_write_value) mem (seg_rom tfibsegs))) /\
  sh_ok tfibsegs fs_Bx wv_SH (Ereg regs (fs_extraT ++ wv_xs str kids keys n)) (rdW W mem) /\
  ajournal tfibsegs B (STK_write_value (2 - k) + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S W (unpoison U mem) md []
    ly S W (unpoison U mem) md 0 /\
  ARU tfibsegs B ly S U W mem md /\
  bv_unsigned (ew (Ereg regs (fs_extraT ++ wv_xs str kids keys n)) 2) = spZ regs.
Proof.
intros k ly S U W regs mem md ch ot v ty num str kids keys n cap0 slo shi buf cap (HPREU & HRO) G11 HPO HH Hs Hot Hot16
  Hottop HPRESENT.
assert (HSTKw : WV_F <= STK_write_value (2 - k))
  by (destruct (2 - k)%nat as [|m']; cbn [STK_write_value]; unfold zmaxl, FRAME_write_value, WV_F; cbn [fold_right]; lia).
destruct (wv_entry _ ly S U W regs mem md ch v ty num str kids keys n cap0 slo shi HPREU HRO HSTKw G11 HPO HH Hs)
  as [HS SHOK].
split; [exact HS|]. split; [exact SHOK|].
split; [exact (fsw_ajournal_init_ot B _ _ ly S U W regs mem md ch ot HPREU Hot Hot16 Hottop HPRESENT)|].
split; [exact (fsw_ARU B _ ly S U W regs mem md ch HPREU)|].
rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity.
Qed.
(* the first run writes only write_value's own frame, inside the journal's window *)
Lemma wv_awr0 : forall E ty slo shi STK ot sp FP bl0 blc lyc own fr0,
  bv_unsigned (ew E 2) = sp -> sp <= ot -> WV_F <= STK ->
  awr_ok tfibsegs B E (ss_mem (wv_ss0 ty slo shi)) (STK + (ot - sp)) ot FP bl0 blc lyc own fr0.
Proof.
intros E ty slo shi STK ot sp FP bl0 blc lyc own fr0 E2 Hot HF.
cbv [wv_ss0 fss0T_args fsT_regions_args fsT_regions ss_mem app].
eapply awr_ok_cons_stack_off with (n := 2%nat) (d := sp - ot);
  [reflexivity | rewrite E2; lia | cbv [fstk YP09.r_wlo]; unfold WV_F in *; lia | cbv [fstk YP09.r_whi]; lia |].
apply awr_ok_cons_ro; [cbv [fs_got_region YP09.r_wlo YP09.r_whi]; lia|].
apply awr_ok_cons_ro; [cbv [fs_bcell_region YP09.r_wlo YP09.r_whi]; lia|].
apply awr_ok_cons_ro; [cbv [wv_node YP09.r_wlo YP09.r_whi]; lia|].
apply awr_ok_cons_ro; [cbv [wv_jt YP09.r_wlo YP09.r_whi]; lia|].
apply awr_ok_nil.
Qed.
(* at a jump out of the first run: the memory differs from the entry's only in the frame *)
Lemma wv_frame0 : forall E ty slo shi (mem mem' : word -> option byte) sp,
  frame_of E (ss_mem (wv_ss0 ty slo shi)) mem mem' -> bv_unsigned (ew E 2) = sp ->
  forall x : word, ~ (sp - WV_F <= bv_unsigned x < sp) -> mem' x = mem x.
Proof.
intros E ty slo shi mem mem' sp HF E2 x Hx. apply HF. intros (r & Hin & Hr).
cbv [wv_ss0 fss0T_args fsT_regions_args fsT_regions ss_mem app In] in Hin.
destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]];
  cbv [fstk fs_got_region fs_bcell_region wv_node wv_jt YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
  try (rewrite E2 in Hr); unfold WV_F in *; lia.
Qed.
(* the callee-saved registers a run left as their entry atoms are the entry's *)
Definition wv_cs_kept (ss : sstate) : bool :=
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CALLEE_SAVED.
Lemma wv_preserved : forall (H : word -> bool) regs xs ss ms,
  st_ok tfibsegs (Ereg regs xs) ss (restrict H ms) -> wv_cs_kept ss = true -> aregs_preserved regs (ms_regs ms).
Proof.
intros H regs xs ss ms HS Hk.
apply (fsw_preserved H (Ereg regs xs) ss ms regs (fun r : bv 5 => SOff (Z.to_nat (bv_unsigned r)) 0) HS Hk).
intros r Hr; cbv [CALLEE_SAVED In] in Hr; repeat (destruct Hr as [<-|Hr]); [..|destruct Hr];
  rewrite fsw_SOff0; apply ew_Ereg_nat; vm_compute; reflexivity.
Qed.

(* a literal arm after its run, at the jump to put: a0 = o, a1 = SA (the literal LB in .rodata), a2 = its length *)
Lemma wv_lit_after : forall k ly S U (W : world tfibsegs) regs mem md ch ot o v pretty d (t : PjTree.jv) D UL
    buf cap failed text live peak cnt fail ty slo shi str kids keys n ssJ ms mdJ SA (LB : list Z),
  fpreU tfibsegs B (STK_write_value (2 - k)) ly S U W regs mem md ch -> fs_heads B ly S U ->
  Z.of_nat (length (frames S)) <= FRL_CRT_CALLEE ->
  getr regs 10 = w64 o ->
  wout_ok B tfibsegs ly S W mem o buf cap failed text -> fs_glob tfibsegs W mem live peak cnt fail ->
  (cap <> 0 -> In (buf - HEAD, HEAD) U) ->
  spZ regs <= o -> o + 32 <= ot -> ot mod 16 = 0 -> ot <= ly_top ly ->
  wv_chain_o U W mem regs o ->
  (forall a, spZ regs <= a < ot -> apresent (w_H W) mem a) ->
  PjStruct.pj_node tfibsegs (rdW W mem) (fun a k => In (a, k) UL) v t D ->
  FSH_Fn_reader.pobj tfibsegs B ly S W mem v ->
  ublocks_ok B tfibsegs ly S W mem UL -> (forall a k, In (a, k) D -> In (a, k) UL /\ a <> buf) ->
  (cap <> 0 -> v + 56 <= buf - HEAD \/ buf + cap <= v) ->
  WriterValue.wvpieces t (negb (pretty =? 0)) d = [LB] ->
  Z.of_nat (length text) + Z.of_nat (length LB) + 1 <= WMAX ->
  cap <= WMAX -> cap <= live -> wbudget_pre S cap cnt live
    (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) (WriterValue.wvpieces t (negb (pretty =? 0)) d)) ->
  In (SA, LB) FS_RO_STRS ->
  forallb (fun j => existsb (fun sg => negb (seg_writable sg) && (Z.of_N (seg_base sg) <=? SA + Z.of_nat j)
                       && (SA + Z.of_nat j <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) tfibsegs
            && match seg_rom tfibsegs (Z_to_bv 64 (SA + Z.of_nat j)) with
               | Some b => bv_unsigned b =? nth j LB 0 | None => false end
            && (0 <=? nth j LB 0) && (nth j LB 0 <? 256)) (seq 0 (length LB)) = true ->
  4096 <= SA -> SA + Z.of_nat (length LB) <= 2 ^ 32 ->
  st_ok tfibsegs (Ereg regs (fs_extraT ++ wv_xs str kids keys n)) ssJ (restrict (w_H W) ms) ->
  frame_of (Ereg regs (fs_extraT ++ wv_xs str kids keys n)) (ss_mem (wv_ss0 ty slo shi)) mem (ms_mem ms) ->
  bv_unsigned (ew (Ereg regs (fs_extraT ++ wv_xs str kids keys n)) 2) = spZ regs ->
  ajournal tfibsegs B (STK_write_value (2 - k) + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S W (unpoison U mem) md []
    ly S W (unpoison U (ms_mem ms)) mdJ 0 ->
  ARU tfibsegs B ly S U W (ms_mem ms) mdJ ->
  ss_pc ssJ = A_put -> ss_resv ssJ = None ->
  sr_get (ss_regs ssJ) 1%bv = SOff 1 0 -> sr_get (ss_regs ssJ) 10%bv = SOff 10 0 ->
  sr_get (ss_regs ssJ) 11%bv = SLit SA -> sr_get (ss_regs ssJ) 12%bv = SLit (Z.of_nat (length LB)) ->
  wv_cs_kept ssJ = true ->
  SRr tfibsegs W (mkCfg ms mdJ)
    (wv_post (2 - k) ot o v pretty d t D UL buf cap failed text live peak cnt fail regs ly S U W mem md).
Proof.
intros k ly S U W regs mem md ch ot o v pretty d t D UL buf cap failed text live peak cnt fail ty slo shi str kids keys n
  ssJ ms mdJ SA LB HPRE HHEADS HFRL G10 HOUT HGLOB HUH Hspo Hoot Hot16 Hottop HCHO HPRESENT HN HPO HUL HD Hroot HWV HROOM
  HCAP HCL HBUD HRO_IN HROM HSA HSAn HS HF E2 HJ HARUJ Hpc Hrv S1 S10 S11 S12 HCS.
pose proof HPRE as (HPREU & HRO).
pose proof asan_consts as (C1 & _).
set (E := Ereg regs (fs_extraT ++ wv_xs str kids keys n)) in *.
assert (R1 : getr (ms_regs ms) 1%bv = getr regs 1%bv)
  by exact (fsw_reg_atom (w_H W) regs _ ssJ ms 1%bv 1%bv 1%nat HS S1 eq_refl).
assert (R10 : getr (ms_regs ms) 10%bv = w64 o)
  by (rewrite (fsw_reg_atom (w_H W) regs _ ssJ ms 10%bv 10%bv 10%nat HS S10 eq_refl); exact G10).
assert (R11 : getr (ms_regs ms) 11%bv = w64 SA) by exact (fsw_reg_lit (w_H W) E ssJ ms 11%bv SA HS S11 ltac:(lia)).
assert (R12 : getr (ms_regs ms) 12%bv = w64 (Z.of_nat (length LB)))
  by exact (fsw_reg_lit (w_H W) E ssJ ms 12%bv _ HS S12 ltac:(lia)).
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms HS Hrv), Hpc.
apply (wv_tail_put (2 - k) ly S U W regs mem md ch ot o v pretty d t D UL buf cap failed text live peak
  cnt fail (ms_regs ms) (ms_mem ms) mdJ SA LB HPRE HHEADS HFRL HOUT HGLOB HUH Hspo Hoot Hot16
  Hottop HCHO HPRESENT HN HPO HUL HD Hroot HWV HROOM HCAP HCL HBUD).
- exact (wv_rom_zbytes W mem SA LB (wv_rom_view B _ ly S U W regs mem md ch IMG HPREU HRO) HROM).
- right; right; right. exists LB. split; [exact HRO_IN | apply Nat.le_succ_diag_r].
- unfold WriterSpec.bytes_ok. apply Forall_forall. intros c Hc.
  apply (In_nth LB c 0) in Hc as (j & Hj & <-).
  rewrite forallb_forall in HROM. specialize (HROM j (proj2 (in_seq _ _ _) (conj (Nat.le_0_l j) Hj))).
  apply andb_true_iff in HROM as [HROM H4]. apply andb_true_iff in HROM as [_ H3].
  apply Z.leb_le in H3. apply Z.ltb_lt in H4. lia.
- lia.
- lia.
- exact HJ.
- exact HARUJ.
- intros a Ha Hn. unfold mbyte, mrestrict.
  rewrite (wv_frame0 E ty slo shi mem (ms_mem ms) (spZ regs) HF E2); [reflexivity|].
  rewrite (wz a Ha). pose proof (wv_stk_frame (2 - k)) as Hw. lia.
- exact (wv_preserved (w_H W) regs _ ssJ ms HS HCS).
- exact R1.
- exact R10.
- exact R11.
- exact R12.
Qed.

(* ---- the literal arms (each run passes 0x8404c and 0x84060 untaken, by the node's fact in wv_gf) ---- *)
Lemma wv_null : forall k, wv_spec_on (fun t => t = PjTree.JNull) k.
Proof.
intros k ly S U W regs mem md ch ot o v pretty d t D UL buf cap failed text live peak cnt fail -> Hdep HPRE HHEADS
  HFRL G10 G11 G12 G13 Hpr Hd Hdd HS0w HOUT HGLOB HUH Hspo Hoot Hot16 Hottop HCHO HPRESENT HN HPO HUL HD Hroot Hplain Hfoot HROOM
  HCAP HCL
  HBUD.
pose proof HN as Hn'. cbn [PjStruct.pj_node] in Hn'. destruct Hn' as (_ & _ & num & str & kids & keys & n & cap0 & HH & _).
pose proof HH as (_ & _ & _ & (Hstr0 & _) & _).
destruct (wv_start k ly S U W regs mem md ch ot v _ num str kids keys n cap0 0 (2 ^ 64 - 1) buf cap HPRE G11 HPO HH ltac:(lia)
  ltac:(lia) Hot16 Hottop HPRESENT) as (HS & SHOK & HJ & HARU0 & E2).
cbn [PjTree.tag] in HS. unfold cfg_at. change (w64 A_write_value) with (Z_to_bv 64 A_write_value).
fsw_aj_run_to_tokU fsw_wr_tbl_ok HS HJ HARU0 SHOK fs_Bspan A_put.
- apply wv_awr0; [exact E2 | lia | apply wv_stk_frame].
- eapply (wv_lit_after k ly S U W regs mem md ch ot o v pretty d _ D UL buf cap failed text live peak cnt fail
    _ 0 (2 ^ 64 - 1) str kids keys n _ ms _ 0x21120 [110; 117; 108; 108] HPRE HHEADS HFRL G10 HOUT HGLOB HUH Hspo Hoot
    Hot16 Hottop HCHO HPRESENT HN HPO HUL HD Hroot eq_refl ltac:(cbn in HROOM |- *; lia) HCAP HCL HBUD
    ltac:(cbn; tauto) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia) HS HF E2 HJ HARU0);
    vm_compute; reflexivity.
Qed.
Lemma wv_false : forall k, wv_spec_on (fun t => t = PjTree.JFalse) k.
Proof.
intros k ly S U W regs mem md ch ot o v pretty d t D UL buf cap failed text live peak cnt fail -> Hdep HPRE HHEADS
  HFRL G10 G11 G12 G13 Hpr Hd Hdd HS0w HOUT HGLOB HUH Hspo Hoot Hot16 Hottop HCHO HPRESENT HN HPO HUL HD Hroot Hplain Hfoot HROOM
  HCAP HCL
  HBUD.
pose proof HN as Hn'. cbn [PjStruct.pj_node] in Hn'. destruct Hn' as (_ & _ & num & str & kids & keys & n & cap0 & HH & _).
pose proof HH as (_ & _ & _ & (Hstr0 & _) & _).
destruct (wv_start k ly S U W regs mem md ch ot v _ num str kids keys n cap0 0 (2 ^ 64 - 1) buf cap HPRE G11 HPO HH ltac:(lia)
  ltac:(lia) Hot16 Hottop HPRESENT) as (HS & SHOK & HJ & HARU0 & E2).
cbn [PjTree.tag] in HS. unfold cfg_at. change (w64 A_write_value) with (Z_to_bv 64 A_write_value).
fsw_aj_run_to_tokU fsw_wr_tbl_ok HS HJ HARU0 SHOK fs_Bspan A_put.
- apply wv_awr0; [exact E2 | lia | apply wv_stk_frame].
- eapply (wv_lit_after k ly S U W regs mem md ch ot o v pretty d _ D UL buf cap failed text live peak cnt fail
    _ 0 (2 ^ 64 - 1) str kids keys n _ ms _ 0x21100 [102; 97; 108; 115; 101] HPRE HHEADS HFRL G10 HOUT HGLOB HUH Hspo Hoot
    Hot16 Hottop HCHO HPRESENT HN HPO HUL HD Hroot eq_refl ltac:(cbn in HROOM |- *; lia) HCAP HCL HBUD
    ltac:(cbn; tauto) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia) HS HF E2 HJ HARU0);
    vm_compute; reflexivity.
Qed.
Lemma wv_true : forall k, wv_spec_on (fun t => t = PjTree.JTrue) k.
Proof.
intros k ly S U W regs mem md ch ot o v pretty d t D UL buf cap failed text live peak cnt fail -> Hdep HPRE HHEADS
  HFRL G10 G11 G12 G13 Hpr Hd Hdd HS0w HOUT HGLOB HUH Hspo Hoot Hot16 Hottop HCHO HPRESENT HN HPO HUL HD Hroot Hplain Hfoot HROOM
  HCAP HCL
  HBUD.
pose proof HN as Hn'. cbn [PjStruct.pj_node] in Hn'. destruct Hn' as (_ & _ & num & str & kids & keys & n & cap0 & HH & _).
pose proof HH as (_ & _ & _ & (Hstr0 & _) & _).
destruct (wv_start k ly S U W regs mem md ch ot v _ num str kids keys n cap0 0 (2 ^ 64 - 1) buf cap HPRE G11 HPO HH ltac:(lia)
  ltac:(lia) Hot16 Hottop HPRESENT) as (HS & SHOK & HJ & HARU0 & E2).
cbn [PjTree.tag] in HS. unfold cfg_at. change (w64 A_write_value) with (Z_to_bv 64 A_write_value).
fsw_aj_run_to_tokU fsw_wr_tbl_ok HS HJ HARU0 SHOK fs_Bspan A_put.
- apply wv_awr0; [exact E2 | lia | apply wv_stk_frame].
- eapply (wv_lit_after k ly S U W regs mem md ch ot o v pretty d _ D UL buf cap failed text live peak cnt fail
    _ 0 (2 ^ 64 - 1) str kids keys n _ ms _ 0x210e0 [116; 114; 117; 101] HPRE HHEADS HFRL G10 HOUT HGLOB HUH Hspo Hoot
    Hot16 Hottop HCHO HPRESENT HN HPO HUL HD Hroot eq_refl ltac:(cbn in HROOM |- *; lia) HCAP HCL HBUD
    ltac:(cbn; tauto) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia) HS HF E2 HJ HARU0);
    vm_compute; reflexivity.
Qed.

(* ================= the string arm: a tail call of put_string ================= *)
(* wv_str's run passes the UBSan guards 0x8404c and 0x84060 untaken by the node's fact in wv_gf (pobj: 4096 <= v,
   v mod 8 = 0), and the branch on str at 0x84304 taken (str <> 0) by str's fact [4096 + HEAD, WV_CEIL] (a live
   reader block, wv_rblock_low). *)

(* a live reader block lies in [4096 + HEAD, alloc_ceiling) *)
Lemma wv_rblock_low : forall ly S (W : world tfibsegs) mx md m p n, AR tfibsegs B ly S W mx md ->
  fs_rblock tfibsegs B ly S W m p n -> 4096 + HEAD <= p /\ p + n <= alloc_ceiling.
Proof.
intros ly S W mx md m p n HAR (Hin & _ & Hn & _). pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct (al_blocks _ _ LAWS ly S W mx md (p - HEAD) (n + HEAD) HAR Hin) as (_ & H4096 & Hc & _).
pose proof (req_size_pos (n + HEAD) ltac:(unfold HEAD; lia)) as (RQ1 & RQ2). unfold HEAD in *. lia.
Qed.
Lemma wv_rblock_r : forall ly S (W : world tfibsegs) mx md m m' p n, AR tfibsegs B ly S W mx md ->
  rsame W m m' -> fs_rblock tfibsegs B ly S W m p n -> fs_rblock tfibsegs B ly S W m' p n.
Proof.
intros ly S W mx md m m' p n HAR SB HB. pose proof (wv_rblock_low ly S W mx md m p n HAR HB) as (L1 & L2).
destruct HB as (Hin & H16 & Hn & Vh). split; [exact Hin|]. split; [exact H16|]. split; [exact Hn|].
exact (rsame_val_mem W m m' (p - HEAD) 8%nat n SB ltac:(unfold HEAD in *; lia)
  ltac:(unfold HEAD in *; lia) Vh).
Qed.

(* put_string's entry-chain clause at the string arm's tail call, where s0 and the chain are write_value's own entry
   ones: every frame pointer fpchain VISITS (s0, and each record's nfp that bad_next lets it follow) is <= o or
   >= o + 48. From write_value's gap-3 premise: s0 < alloc_ceiling forces ch = [] (achain's second disjunct needs
   sp + 16 <= s0, and sp >= alloc_ceiling); s0 = o gives the one-node chain at o (wv_chain_o; at o = sp + 8 achain is its
   first disjunct), whose record's nfp < alloc_ceiling <= o; o + 48 <= s0: the records' fps rise from s0
   (YCbq.fpchain_fps_increase), and a followed nfp lies above its record's fp. *)
Lemma wv_ps_chain : forall STK ly S U (W : world tfibsegs) regs mem md ch o,
  fpreU tfibsegs B STK ly S U W regs mem md ch -> spZ regs <= o ->
  (s0Z regs < alloc_ceiling \/ s0Z regs = o \/ o + 48 <= s0Z regs) ->
  wv_chain_o U W mem regs o ->
  forall fp, fp = s0Z regs \/ (exists r, In r ch /\ snd r = fp /\ bad_next (fst (fst r)) (ly_top ly) fp = false) ->
  fp <= o \/ o + 48 <= fp.
Proof.
intros STK ly S U W regs mem md ch o ((HAP & _) & _) Hspo HS0w HCHO fp Hfp.
pose proof HAP as (_ & _ & _ & _ & _ & Hstk & _ & Hch & _).
pose proof Hstk as (_ & HSTK0 & Hceil & Hslo & _).
destruct Hch as [(_ & ->) | (H16 & Htopv & Hal & Hfc & _)].
- destruct Hfp as [-> | (r & [] & _)]. lia.
- destruct HS0w as [Hlo | [Ho | Hhi]].
  + lia.
  + destruct HCHO as [(Ho8 & _) | (_ & ra & nfp & Hra8 & Hnfp & Hend)]; [lia|].
    destruct Hfp as [-> | (r & Hin & Hsnd & _)]; [lia|].
    destruct ch as [|[[fp1 ra1] nfp1] rest]; [destruct Hin|].
    cbn [fpchain] in Hfc. destruct Hfc as (E1 & _ & H8 & H16' & Hra1 & Hrest).
    subst fp1. rewrite Ho in H8, H16'. rewrite Hra8 in H8. rewrite Hnfp in H16'.
    injection H8 as Era. injection H16' as Enfp.
    assert (Hbn : bad_next (s0Z regs) (ly_top ly) nfp1 = true).
    { unfold bad_next. apply Bool.orb_true_iff. left. apply Bool.orb_true_iff. left. apply Z.leb_le. lia. }
    rewrite Hbn in Hrest. subst rest.
    destruct Hin as [<- | []]. cbn [snd] in Hsnd. left. lia.
  + destruct Hfp as [-> | (r & Hin & _ & Hbn)]; [right; lia|].
    pose proof (fpchain_fps_increase _ _ _ _ Hfc) as Hinc.
    rewrite Forall_forall in Hinc. specialize (Hinc r Hin).
    unfold bad_next in Hbn. apply Bool.orb_false_elim in Hbn as [Hbn _]. apply Bool.orb_false_elim in Hbn as [Hbn _].
    apply Z.leb_gt in Hbn. right. lia.
Qed.

Lemma wv_tail_ps : forall m ly S U (W : world tfibsegs) regs mem md ch ot o v pretty d D UL
    buf cap failed text live peak cnt fail regsJ memJ mdJ str kk (s : list Z),
  fpreU tfibsegs B (STK_write_value m) ly S U W regs mem md ch -> fs_heads B ly S U ->
  Z.of_nat (length (frames S)) <= FRL_CRT_CALLEE ->
  (s0Z regs < alloc_ceiling \/ s0Z regs = o \/ o + 48 <= s0Z regs) ->
  wout_ok B tfibsegs ly S W mem o buf cap failed text -> fs_glob tfibsegs W mem live peak cnt fail ->
  (cap <> 0 -> In (buf - HEAD, HEAD) U) ->
  spZ regs <= o -> o + 32 <= ot -> ot mod 16 = 0 -> ot <= ly_top ly ->
  wv_chain_o U W mem regs o ->
  (forall a, spZ regs <= a < ot -> apresent (w_H W) mem a) ->
  PjStruct.pj_node tfibsegs (rdW W mem) (fun a k => In (a, k) UL) v (PjTree.JStr s) D ->
  FSH_Fn_reader.pobj tfibsegs B ly S W mem v ->
  ublocks_ok B tfibsegs ly S W mem UL -> (forall a k, In (a, k) D -> In (a, k) UL /\ a <> buf) ->
  (cap <> 0 -> v + 56 <= buf - HEAD \/ buf + cap <= v) ->
  jv_plain (PjTree.JStr s) ->
  PjStruct.pj_cstr tfibsegs (rdW W mem) (fun a k => In (a, k) UL) str kk s -> In (str, kk) D ->
  Z.of_nat (length text)
    + Z.of_nat (length (concat (WriterValue.wvpieces (PjTree.JStr s) (negb (pretty =? 0)) d))) + 1 <= WMAX ->
  cap <= WMAX -> cap <= live -> wbudget_pre S cap cnt live
    (WriterApp.putN (WriterApp.mkW failed text cap cnt fail []) (WriterValue.wvpieces (PjTree.JStr s) (negb (pretty =? 0)) d)) ->
  ajournal tfibsegs B (STK_write_value m + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S W (unpoison U mem) md []
    ly S W (unpoison U memJ) mdJ 0 ->
  ARU tfibsegs B ly S U W memJ mdJ ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_write_value m <= a < spZ regs) ->
     mbyte tfibsegs (rdW W memJ) a = mbyte tfibsegs (rdW W mem) a) ->
  aregs_preserved regs regsJ -> getr regsJ 1 = getr regs 1 ->
  getr regsJ 10 = w64 o -> getr regsJ 11 = w64 str ->
  SRr tfibsegs W (cfg_at tfibsegs A_put_string regsJ memJ mdJ)
    (wv_post m ot o v pretty d (PjTree.JStr s) D UL buf cap failed text live peak cnt fail regs ly S U W mem md).
Proof.
intros m ly S U W regs mem md ch ot o v pretty d D UL buf cap failed text live peak cnt fail regsJ memJ mdJ str kk s
  HPRE HHEADS HFRL HS0w HOUT HGLOB HUH Hspo Hoot Hot16 Hottop HCHO HPRESENT HN HPO HUL HD Hroot Hplain HCS HinD HROOM HCAP
  HCL HBUD HJ HARUJ HMJ HP R1 G10 G11.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof HPRE as (((HAR & _ & _ & _ & _ & (_ & _ & Hc & Hsl & _) & _) & _) & _).
pose proof (fsw_ARU B _ ly S U W regs mem md ch (proj1 HPRE)) as HARU0.
destruct (wv_stk_callees m) as (_ & SKps & _).
assert (SKps0 : 0 <= STK_put_string) by (vm_compute; discriminate).
destruct (wv_jump m ly S U W regs mem md ch ot o buf cap failed text live peak cnt fail regsJ memJ mdJ STK_put_string
  HPRE HOUT HGLOB Hspo Hoot Hot16 Hottop HCHO HPRESENT HJ HARUJ HMJ HP R1 ltac:(lia))
  as (HPREJ & Esp & HOUTJ & HGLOBJ & HCHOJ & HPRJ & SB & MWE).
assert (S0J : s0Z regsJ = s0Z regs)
  by (unfold s0Z; rewrite (fsw_pres regs regsJ 8%bv HP ltac:(unfold acallee_saved; vm_compute; lia)); reflexivity).
(* the string: a live reader block of the tree, other than the buffer *)
destruct (HD str kk HinD) as [HinUL Hne].
pose proof (HUL str kk HinUL) as HRB.
pose proof (wv_rblock_low ly S W _ md mem str kk HAR HRB) as (Hs1 & Hs2).
pose proof HCS as (_ & Hlen & (Hbytes & _)).
assert (HCSOK : cstr_ok tfibsegs W memJ str s)
  by exact (rsame_cstr_ok W mem memJ str s SB (wv_cstr_ok_node B ly S U W mem md UL str kk s HARU0 HHEADS HUL HCS)).
eapply SRr_mono.
{ apply (HPS ly S U W regsJ memJ mdJ ch ot o str buf cap failed text s live peak cnt fail HPREJ HHEADS).
  - exact HFRL.
  - exact G10.
  - exact G11.
  - exact HOUTJ.
  - exact HGLOBJ.
  - exact HUH.
  - rewrite Esp. exact Hspo.
  - exact Hoot.
  - exact Hot16.
  - exact Hottop.
  - exact HCHOJ.
  - rewrite S0J. exact (wv_ps_chain _ ly S U W regs mem md ch o HPRE Hspo HS0w HCHO).
  - exact HPRJ.
  - exact HCSOK.
  - right; left. exists str, kk. split; [exact Hne|].
    split; [exact (wv_rblock_r ly S W _ md mem memJ str kk HAR SB HRB)|].
    rewrite length_app. cbn [length]. lia.
  - unfold WriterSpec.bytes_ok. eapply Forall_impl; [|exact Hbytes]. intros c Hc'. cbn beta in Hc'. lia.
  - unfold WriterSpec.no_zero. eapply Forall_impl; [|exact Hbytes]. intros c Hc'. cbn beta in Hc'. lia.
  - exact Hplain.
  - left. lia.
  - exact HROOM.
  - exact HCAP.
  - exact HCL.
  - exact HBUD. }
cbv beta. intros W' c' Hle (st' & buf' & U' & Est & Hus & Hwp).
exists st', buf', U'. split; [exact Est|]. split; [exact Hus|].
unfold wpost in *.
refine (wv_tail_post m ly S U W regs mem md ch ot o v (PjTree.JStr s) D UL buf cap failed text live peak cnt regsJ memJ mdJ
  STK_put_string _ U' st' buf' _ W' c' HPRE HOUT Hspo Hoot Hottop HN HPO HUL HD Hroot HJ HARUJ MWE HP R1 Esp ltac:(lia)
  _ Hwp).
intros ly' S' W'' regs' mem' md' (Q1 & Q2 & Q3 & Q4 & _ & Q5). auto.
Qed.

Lemma wv_str : forall k, wv_spec_on (fun t => exists s, t = PjTree.JStr s) k.
Proof.
intros k ly S U W regs mem md ch ot o v pretty d t D UL buf cap failed text live peak cnt fail (s & ->) Hdep HPRE HHEADS
  HFRL G10 G11 G12 G13 Hpr Hd Hdd HS0w HOUT HGLOB HUH Hspo Hoot Hot16 Hottop HCHO HPRESENT HN HPO HUL HD Hroot Hplain Hfoot
  HROOM HCAP HCL HBUD.
pose proof asan_consts as (C1 & _).
pose proof HPRE as (((HAR & _) & _) & _).
pose proof HN as Hn'. cbn [PjStruct.pj_node] in Hn'.
destruct Hn' as (_ & _ & num & str & kids & keys & n & cap0 & HH & (_ & _ & _ & _ & kk & HCS & ED)).
assert (HinD : In (str, kk) D) by (rewrite ED; left; reflexivity).
pose proof (wv_rblock_low ly S W _ md mem str kk HAR (HUL str kk (proj1 (HD str kk HinD)))) as (Hs1 & Hs2).
pose proof (HUL str kk (proj1 (HD str kk HinD))) as (_ & _ & Hkk & _).
destruct (wv_start k ly S U W regs mem md ch ot v _ num str kids keys n cap0 (4096 + HEAD) WV_CEIL buf cap HPRE G11 HPO HH
  ltac:(unfold WV_CEIL; lia) ltac:(lia) Hot16 Hottop HPRESENT) as (HS & SHOK & HJ & HARU0 & E2).
cbn [PjTree.tag] in HS. unfold cfg_at. change (w64 A_write_value) with (Z_to_bv 64 A_write_value).
fsw_aj_run_to_tokU fsw_wr_tbl_ok HS HJ HARU0 SHOK fs_Bspan A_put_string.
- apply wv_awr0; [exact E2 | lia | apply wv_stk_frame].
- lazymatch goal with HS : st_ok _ _ ?ssf _ |- _ => set (ssJ := ssf) in HS end.
  assert (R1 : getr (ms_regs ms) 1%bv = getr regs 1%bv)
    by exact (fsw_reg_atom (w_H W) regs _ ssJ ms 1%bv 1%bv 1%nat HS ltac:(vm_compute; reflexivity) eq_refl).
  assert (R10 : getr (ms_regs ms) 10%bv = w64 o)
    by (rewrite (fsw_reg_atom (w_H W) regs _ ssJ ms 10%bv 10%bv 10%nat HS ltac:(vm_compute; reflexivity) eq_refl);
        exact G10).
  assert (R11 : getr (ms_regs ms) 11%bv = w64 str)
    by exact (fsw_reg_extra (w_H W) regs _ ssJ ms 11%bv 1 HS ltac:(vm_compute; reflexivity)).
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms HS eq_refl).
  change (ss_pc ssJ) with A_put_string.
  apply (wv_tail_ps (2 - k) ly S U W regs mem md ch ot o v pretty d D UL buf cap failed text live peak cnt fail
    (ms_regs ms) (ms_mem ms) _ str kk s HPRE HHEADS HFRL HS0w HOUT HGLOB HUH Hspo Hoot Hot16 Hottop HCHO HPRESENT HN HPO
    HUL HD Hroot Hplain HCS HinD HROOM HCAP HCL HBUD HJ HARU0).
  + intros a Ha Hn. unfold mbyte, mrestrict.
    rewrite (wv_frame0 _ _ _ _ mem (ms_mem ms) (spZ regs) HF E2); [reflexivity|].
    rewrite (wz a Ha). pose proof (wv_stk_frame (2 - k)) as Hw. lia.
  + exact (wv_preserved (w_H W) regs _ ssJ ms HS ltac:(vm_compute; reflexivity)).
  + exact R1.
  + exact R10.
  + exact R11.
Qed.
End W.
