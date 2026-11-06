(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v; 1536 of its 1692 lines of code are new or changed and 1217 lines of the source are left out. *)
(* write_value (fs.asan 0x83d84, preset_file.c:525-575): the ASan walk of fs's recursive value writer, image A, against
   lib/A/FSH_Fn_writer.v's write_value_spec_at (statement head a working branch efbff066c09, S0 aaf2c4ec41f's kit).
   MEASURED with the engine on the original fs.asan (a build machine, sha256 64b53ff8...): the prologue (frame 176, FRAME_write_value),
   the inline ASan check of v->type (shadow of the root node, atom 11), the type check `bltu 6, ty`, the jump table at
   .rodata 0x21000 (seven 4-byte offsets), and the arms: null / false / true load their literal and TAIL-jump to put
   (0x8418c) with the entry ra; number branches on str at 0x83f44 and calls strlen; string branches on str at 0x83e94 and
   TAIL-jumps to put_string (0x85ad8); array / object call put (0x8418c) at 0x83e38, returning to 0x83e3c.
   Callees are Section hypotheses (put_spec, put_string_spec, indent_spec, astrlen_realizesU; no CTX list since the
   statement head a working branch dda8331bd25, which also fixes put_string's visited-frame clause); the
   TAIL step (wvc_tail_otJ) and the raised-top after-call step (wvc_after_call_ot) are PROVED here from FSW_K3 /
   FSW_rres (by a part of a Theorem Labs lane). The container arms wv_arr / wv_obj are Section hypotheses, proved by the Theorem Labs lane
   (lib/A/ZZwv_cont.v); write_value_holds is the closing theorem over all seven arms and every level.
   Port-from: the generation-N image-A proof (211ff3e9df0 lib/A/Prog/write_value_blocks.v, write_value.v: stage cuts and
   case split), a Theorem Labs lane's lib/A/FMW_check_reject_clean.v (run / call shape), the checks lane's FSW_caw_tail.v (token runs).
   Rule 24 (proof-index v5 built 2026-10-28T21:58:24Z, exit 0): write_value has RELEASED proofs for fs's PLAIN and
   UBSAN builds only (lib/Prog, lib/U/Prog), none for ASan; they are templates, not drop-ins. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_rres FSW_ret FSW_writer_tbl FSW_pj FSH_Fn_writer.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSH_Fn_reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp WriterValue PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ================= the walk's constants and symbolic states ================= *)
Definition WV_F : Z := 176.                       (* the frame: FSH_Base.FRAME_write_value *)
Definition WV_CEIL : Z := 140737479966720.        (* 0x7fffff800000: alloc_ceiling's bound (YCbq.v asan_consts) *)
Definition WV_JT : Z := 0x21000.                  (* the type dispatch's jump table in .rodata *)
Definition WV_PS : Z := 0x85ad8.                  (* put_string: FSH_Base.A_put_string *)
Definition WV_R_OPEN : Z := 0x83e3c.              (* the return address of the array / object arm's first put *)

(* the root node v (atom 11, a1 at entry): read-only, the fields the arms load. The type is a literal per arm (the walk
   splits on the tree before the run), str / kids / keys / n are the walk's extra atoms xatom 0 .. 3 *)
Definition wv_node (ty : Z) : YP09.region :=
  YP09.mkRegion (Some 11%nat) 0 56 0 0
    [YP09.mkChunk 0 (CVal 4 (SLit ty)); YP09.mkChunk 16 (CVal 8 (SOff (xatom 0) 0));
     YP09.mkChunk 24 (CVal 8 (SOff (xatom 1) 0)); YP09.mkChunk 32 (CVal 8 (SOff (xatom 2) 0));
     YP09.mkChunk 40 (CVal 8 (SOff (xatom 3) 0))].
Definition wv_xs (str kids keys n : Z) : list word := [Z_to_bv 64 str; Z_to_bv 64 kids; Z_to_bv 64 keys; Z_to_bv 64 n].
(* the jump table (MEASURED: seg_rom of fs.asan at 0x21000 .. 0x2101c, little-endian 32-bit offsets) *)
Definition wv_jt : YP09.region :=
  YP09.mkRegion None 0x21000 0x2101c 0 0
    [YP09.mkChunk 0x21000 (CVal 4 (SLit 0x62f68)); YP09.mkChunk 0x21004 (CVal 4 (SLit 0x62f78));
     YP09.mkChunk 0x21008 (CVal 4 (SLit 0x62f1c)); YP09.mkChunk 0x2100c (CVal 4 (SLit 0x62f28));
     YP09.mkChunk 0x21010 (CVal 4 (SLit 0x62e78)); YP09.mkChunk 0x21014 (CVal 4 (SLit 0x62e14));
     YP09.mkChunk 0x21018 (CVal 4 (SLit 0x62e14))].
(* the atom facts: the node (8-aligned, below the ceiling) and str in [slo, shi] *)
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

(* the entry symbolic state (frame, shadow-base cells, the root node, the jump table) and the node's shadow entry *)
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
- apply (wv_img_cover 0xa3ca0 8 ltac:(vm_compute; reflexivity)). lia.
- apply (wv_img_cover 0x5da5c0 8 ltac:(vm_compute; reflexivity)). lia.
- apply (wv_img_cover 0x5da5e0 8 ltac:(vm_compute; reflexivity)). lia.
- apply (wv_img_cover 0x5da600 8 ltac:(vm_compute; reflexivity)). lia.
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
(* the container arms, proved by the Theorem Labs lane (a working branch, lib/A/ZZwv_cont.v); text agreed
   with it 2026-10-29 and fixed. The recursive call is write_value at level S k; at k = 2 the arms are vacuous
   (depth (JArr _) >= 1), and the guard k < 2 keeps level 2 from asking for itself (2 - 3 = 2 - 2 in nat). *)
Hypothesis wv_arr : forall k, ((k < 2)%nat -> write_value_spec_at B tfibsegs (S k)) ->
  wv_spec_on (fun t => exists items, t = PjTree.JArr items) k.
Hypothesis wv_obj : forall k, ((k < 2)%nat -> write_value_spec_at B tfibsegs (S k)) ->
  wv_spec_on (fun t => exists members, t = PjTree.JObj members) k.
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

(* ---- the literal arms ---- *)
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

(* ================= the number arm: strlen of the text, then a tail call of put ================= *)
(* the strlen interceptor's contract (S0's FSH_Gen.astrlen_realizesU at fs.asan's PC_strlen; FSH_Rt.FsRt.fr_strlen) *)
Hypothesis HSLEN : astrlen_realizesU tfibsegs B PC_strlen.

(* aview / presence through unpoison follow the raw memory's *)
Lemma wv_aview_unpoison_eq : forall (H : word -> bool) U (m m' : word -> option byte) a,
  aview tfibsegs H m' a = aview tfibsegs H m a -> aview tfibsegs H (unpoison U m') a = aview tfibsegs H (unpoison U m) a.
Proof.
intros H U m m' a E. unfold aview, mbyte, mrestrict, unpoison in *.
destruct (H (Z_to_bv 64 a)); [reflexivity|].
destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))); [reflexivity | exact E].
Qed.
Lemma wv_apresent_unpoison : forall (H : word -> bool) U (m m' : word -> option byte),
  (forall a, apresent H m a -> apresent H m' a) ->
  forall a, apresent H (unpoison U m) a -> apresent H (unpoison U m') a.
Proof.
intros H U m m' Hp a (Hh & b & Hb). split; [exact Hh|]. unfold unpoison in *.
destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))); [exists (Z_to_bv 8 0); reflexivity|].
destruct (Hp a (conj Hh (ex_intro _ b Hb))) as (_ & b' & Hb'). exists b'. exact Hb'.
Qed.
(* a runtime callee's ARU-form post (FSH_Gen.rt_post_roU) in the shape FSW_K.fsw_intrin_atU takes *)
Lemma wv_rt_post_conv : forall K ly S U (W : world tfibsegs) regs mem md (R : Z -> Prop) W' c',
  upoison_ok B ly S U ->
  rt_post_roU tfibsegs B K ly S U W regs mem md R W' c' ->
  W' = W /\ exists regs' mem' md',
    c' = mkCfg (mkst regs' (w64 (raZ regs)) mem' (seg_rom tfibsegs)) md' /\
    ARU tfibsegs B ly S U W mem' md' /\ same_but_materialized md md' /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - K <= a < spZ regs) ->
       aview tfibsegs (w_H W) (unpoison U mem') a = aview tfibsegs (w_H W) (unpoison U mem) a) /\
    (forall a, apresent (w_H W) (unpoison U mem) a -> apresent (w_H W) (unpoison U mem') a) /\
    (aregs_preserved regs regs' /\ (exists v, getr regs' 10 = w64 v /\ 0 <= v < 2 ^ 64 /\ R v) /\
     (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - K <= a < spZ regs) ->
        aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a)).
Proof.
intros K ly S U W regs mem md R W' c' OK (-> & regs' & mem' & md' & v & Ec & HAR & PO & HP & Hs & G10 & Hv & HR & Hfr & Hpr).
split; [reflexivity|]. exists regs', mem', md'.
split; [exact Ec|]. split; [split; [exact HAR | split; [exact OK | exact PO]]|]. split; [exact Hs|].
split; [intros a Ha Hn; apply wv_aview_unpoison_eq; exact (Hfr a Ha Hn)|].
split; [exact (wv_apresent_unpoison (w_H W) U mem mem' Hpr)|].
split; [exact HP|]. split; [exists v; auto | exact Hfr].
Qed.
(* a chunk read at one base / env, re-read at another base / env holding the same value *)
Lemma wv_chunk_move : forall E E2 m base base2 off off2 e e2,
  YP09.chunk_ok tfibsegs E m base (YP09.mkChunk off (CVal 8 e)) -> base + off = base2 + off2 ->
  sv_denot E2 e2 = sv_denot E e -> YP09.chunk_ok tfibsegs E2 m base2 (YP09.mkChunk off2 (CVal 8 e2)).
Proof.
intros E E2 m base base2 off off2 e e2 H Hb He i Hi. destruct (H i Hi) as (b & Hc & Hm). exists b.
cbn [YP09.c_off YP09.c_val YP09.cbyte] in *. rewrite He. split; [exact Hc|].
replace (base2 + off2 + i) with (base + off + i) by lia. exact Hm.
Qed.

(* the frame slots the prologue wrote, as the epilogue reloads them after a call: 64 the shadow base, 72 .. 168 the
   thirteen saved entry registers (s11 .. s2, s1, s0, ra), each an extra atom xatom (5 + k) of the resumed env
   (the layout of wvc_cs0 / wvc_xs of a part of a Theorem Labs lane, ZZwv_defs.v 72cacaf9a57) *)
Definition wv_saved : list (bv 5) := [27; 26; 25; 24; 23; 22; 21; 20; 19; 18; 9; 8; 1]%bv.
Definition wv_xsR (regs : bvmap 5 word) (str kids keys n d : Z) : list word :=
  wv_xs str kids keys n ++ [Z_to_bv 64 d] ++ map (fun r => YK11.getr regs r) wv_saved.
Definition wv_cs0 : list YP09.chunk :=
  YP09.mkChunk 64 (CVal 8 (SOff 32 0))
  :: map (fun k => YP09.mkChunk (72 + 8 * Z.of_nat k) (CVal 8 (SOff (xatom (5 + k)) 0))) (seq 0 13).
(* a run from a resumed state with no extra region writes only the frame [sp - 176, sp) *)
Lemma wv_frameR : forall E r cs (m m' : word -> option byte) sp,
  frame_of E (ss_mem (fss_retT r 176 cs [] [])) m m' -> bv_unsigned (ew E 2) = sp - 176 ->
  forall x : word, ~ (sp - 176 <= bv_unsigned x < sp) -> m' x = m x.
Proof.
intros E r cs m m' sp HF E2 x Hx. apply HF. intros (rg & Hin & Hr).
cbv [fss_retT fsT_ret_regions ss_mem app In] in Hin.
destruct Hin as [<-|[<-|[<-|[]]]];
  cbv [fstk_ret fs_got_region fs_bcell_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
  try (rewrite E2 in Hr); lia.
Qed.
Lemma wv_garr8_prefix : forall m p (l l' : list Z), garr8 tfibsegs m p (l ++ l') -> garr8 tfibsegs m p l.
Proof.
intros m p l l' H j Hj. destruct (H j ltac:(rewrite length_app; lia)) as [Hv Hr].
rewrite app_nth1 in Hv, Hr by exact Hj. split; assumption.
Qed.

Lemma wv_num : forall k, wv_spec_on (fun t => exists txt bits, t = PjTree.JNum txt bits) k.
Proof.
intros k ly S U W regs mem md ch ot o v pretty d t D UL buf cap failed text live peak cnt fail (txt & bits & ->) Hdep
  HPRE HHEADS HFRL G10 G11 G12 G13 Hpr Hd Hdd HS0w HOUT HGLOB HUH Hspo Hoot Hot16 Hottop HCHO HPRESENT HN HPO HUL HD Hroot
  Hplain Hfoot HROOM HCAP HCL HBUD.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof HPRE as (HPREU & HRO).
pose proof HPREU as ((HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT) & HUOK & HUPO).
pose proof Hstk as (Hsp16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (wv_stk_frame (2 - k)) as HSF.
assert (HSTR : WV_F + STK_RT_STR <= STK_write_value (2 - k))
  by (destruct (2 - k)%nat; cbn [STK_write_value]; unfold zmaxl, FRAME_write_value, WV_F; cbn [fold_right]; lia).
assert (HRS : STK_RT_STR = ltac:(let v := eval vm_compute in STK_RT_STR in exact v)) by reflexivity.
assert (HWF : WV_F = 176) by reflexivity.
pose proof HN as Hn'. cbn [PjStruct.pj_node] in Hn'.
destruct Hn' as (_ & _ & num & str & kids & keys & n & cap0 & HH & (_ & _ & _ & _ & _ & kk & HCS & ED)).
assert (HinD : In (str, kk) D) by (rewrite ED; left; reflexivity).
destruct (HD str kk HinD) as [HinUL Hne].
pose proof (HUL str kk HinUL) as HRB. pose proof HRB as (_ & _ & Hkk & _).
pose proof (wv_rblock_low ly S W _ md mem str kk HAR HRB) as (Hs1 & Hs2).
destruct (wv_start k ly S U W regs mem md ch ot v _ num str kids keys n cap0 (4096 + HEAD) WV_CEIL buf cap HPRE G11 HPO HH
  ltac:(unfold WV_CEIL; lia) ltac:(lia) Hot16 Hottop HPRESENT) as (HS & SHOK & HJ & HARU0 & E2).
cbn [PjTree.tag] in HS. unfold cfg_at. change (w64 A_write_value) with (Z_to_bv 64 A_write_value).
set (E := Ereg regs (fs_extraT ++ wv_xs str kids keys n)) in *.
fsw_aj_run_to_tokU fsw_wr_tbl_ok HS HJ HARU0 SHOK fs_Bspan PC_strlen.
- apply wv_awr0; [exact E2 | lia | exact HSF].
- (* ---- at the strlen call ---- *)
  lazymatch goal with HS : st_ok _ _ ?ssf _ |- _ => set (ssT := ssf) in HS end.
  set (mdT := with_vm_backing (m_vm_lazy md) mat md) in *.
  assert (HES : ESTACK = 4096) by reflexivity.
  assert (M16 : forall a b c, a mod 16 = 0 -> b mod 16 = 0 -> c mod 16 = 0 -> (a - b - c) mod 16 = 0)
    by (intros a0 b0 c0 Ha Hb Hc; rewrite Zminus_mod, (Zminus_mod a0 b0), Ha, Hb, Hc; reflexivity).
  assert (R1T : getr (ms_regs ms) 1%bv = Z_to_bv 64 0x83f58)
    by exact (fsw_reg_lit (w_H W) E ssT ms 1%bv 0x83f58 HS ltac:(vm_compute; reflexivity) ltac:(lia)).
  assert (SPT : spZ (ms_regs ms) = spZ regs - 176)
    by (unfold spZ; exact (fsw_reg_off (w_H W) E ssT ms 2%bv 2 (-176) (spZ regs) HS ltac:(vm_compute; reflexivity) E2
          ltac:(lia))).
  assert (R3T : getr (ms_regs ms) 3%bv = getr regs 3%bv)
    by exact (fsw_reg_atom (w_H W) regs _ ssT ms 3%bv 3%bv 3%nat HS ltac:(vm_compute; reflexivity) eq_refl).
  assert (R4T : getr (ms_regs ms) 4%bv = getr regs 4%bv)
    by exact (fsw_reg_atom (w_H W) regs _ ssT ms 4%bv 4%bv 4%nat HS ltac:(vm_compute; reflexivity) eq_refl).
  assert (R10T : getr (ms_regs ms) 10%bv = w64 str)
    by (rewrite (fsw_reg_extra (w_H W) regs _ ssT ms 10%bv 1 HS ltac:(vm_compute; reflexivity)); reflexivity).
  pose proof (fsw_ARU B _ ly S U W regs mem md ch HPREU) as HARUe.
  assert (SB1 : rsame W mem (ms_mem ms)).
  { intros x Hx. unfold mbyte, mrestrict.
    rewrite (wv_frame0 E _ _ _ mem (ms_mem ms) (spZ regs) HF E2); [reflexivity|].
    rewrite (wz x ltac:(lia)). unfold WV_F in *. lia. }
  assert (HROMT : rom_view tfibsegs W (ms_mem ms)).
  { intros a Ha. pose proof Ha as (sg & Hin & Hw & Hr).
    assert (Hi : in_img tfibsegs a) by (exists sg; split; [exact Hin | lia]).
    pose proof (fs_segs_img a Hi) as Hl. unfold FS_IMG_END in Hl.
    rewrite (rsame_aview W mem (ms_mem ms) a SB1 ltac:(lia)).
    exact (wv_rom_view B _ ly S U W regs mem md ch IMG HPREU HRO a Ha). }
  assert (HCSOKT : cstr_ok tfibsegs W (ms_mem ms) str txt)
    by exact (rsame_cstr_ok W mem (ms_mem ms) str txt SB1 (wv_cstr_ok_node B ly S U W mem md UL str kk txt HARUe HHEADS
      HUL HCS)).
  assert (HPRET : ecall_preU_k tfibsegs B STK_RT_STR ly S U W (ms_regs ms) (ms_mem ms) mdT).
  { apply (fsw_ecall_preU_k_at B (STK_write_value (2 - k) + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S W
      (unpoison U mem) md [] ly S U W (ms_mem ms) mdT 0 (ms_regs ms) (spZ regs - 176 - ot) STK_RT_STR HJ HARU0).
    - rewrite SPT. lia.
    - exact (M16 (spZ regs) 176 ot Hsp16 eq_refl Hot16).
    - lia.
    - lia.
    - lia.
    - lia.
    - rewrite R1T. apply ret_ok_even. rewrite unsigned_lit_small by lia. reflexivity.
    - rewrite R3T. exact Hgp.
    - rewrite R4T. exact Htp. }
  pose proof HSS as [HBgot HBcell].
  pose proof (wv_cstr_ok_node B ly S U W mem md UL str kk txt HARUe HHEADS HUL HCS) as HCSOK0.
  (* the call state's registers the resume and the jump read *)
  assert (R8T : getr (ms_regs ms) 8%bv = getr regs 10%bv)
    by exact (fsw_reg_atom (w_H W) regs _ ssT ms 8%bv 10%bv 10%nat HS ltac:(vm_compute; reflexivity) eq_refl).
  assert (R9T : getr (ms_regs ms) 9%bv = w64 str)
    by (rewrite (fsw_reg_extra (w_H W) regs _ ssT ms 9%bv 1 HS ltac:(vm_compute; reflexivity)); reflexivity).
  (* the frame region of the call state: its chunks, read on the call memory *)
  lazymatch eval vm_compute in (nth_error (ss_mem ssT) 0) with
  | Some ?r0 => pose proof (fsw_region_nth E ssT _ 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0
  end.
  cbn [ms_mem restrict] in HR0. unfold YP09.region_ok in HR0.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in HR0.
  rewrite E2 in HR0. destruct HR0 as (_ & _ & _ & HC0).
  pose proof (proj1 (Forall_forall _ _) HC0) as CK. clear HC0.
  rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms HS eq_refl). change (ss_pc ssT) with PC_strlen.
  eapply SRr_bind.
  { apply (fsw_intrin_atU B (STK_write_value (2 - k) + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S W
      (unpoison U mem) md [] ly S U W (ms_mem ms) mdT 0 U (fun a => spZ regs - 176 - STK_RT_STR <= a < spZ regs - 176)
      (w64 (raZ (ms_regs ms))) _
      (fun regs' mem' md' => aregs_preserved (ms_regs ms) regs' /\
         (exists v0, getr regs' 10 = w64 v0 /\ 0 <= v0 < 2 ^ 64 /\ v0 = Z.of_nat (length txt)) /\
         (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (ms_regs ms) - STK_RT_STR <= a < spZ (ms_regs ms)) ->
            aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) (ms_mem ms) a)) HJ).
    - eapply SRr_mono; [exact (HSLEN ly S U W (ms_regs ms) (ms_mem ms) mdT str txt HPRET HROMT R10T HCSOKT)|].
      intros W' c' _ Hp.
      destruct (wv_rt_post_conv STK_RT_STR ly S U W (ms_regs ms) (ms_mem ms) mdT _ W' c' HUOK Hp)
        as (-> & regs' & mem' & md' & Ec & HARU' & Hsbm & Hfr & Hprs & HQ).
      split; [reflexivity|]. exists regs', mem', md'. split; [exact Ec|]. split; [exact HARU'|]. split; [exact Hsbm|].
      split; [intros a Ha Hn; apply Hfr; [exact Ha | rewrite SPT; exact Hn]|].
      split; [exact Hprs | exact HQ].
    - intros a Ha. left. left. lia. }
  intros W2 c2 Hle2 (-> & regs2 & mem2 & md2 & -> & HJ2 & HARU2 & HP2 & (v2 & G10' & Hv2 & Ev2) & Hfr2).
  (* ---- the resume at 0x83f58: a sub-journal at the entry sp, the frame reloaded from the call memory ---- *)
  pose proof (ajournal_sub_init tfibsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (STK_write_value (2 - k)) (spZ regs) []
    (spZ regs - ot) HJ2 ltac:(lia) ltac:(rewrite Zminus_mod, Hsp16, Hot16; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia))
    as J3.
  assert (SP2 : spZ regs2 = spZ regs - 176).
  { unfold spZ. rewrite (fsw_pres _ _ 2%bv HP2 ltac:(unfold acallee_saved; vm_compute; lia)). exact SPT. }
  assert (E3sp : bv_unsigned (ew (Ereg regs2 (fs_extraT ++ wv_xsR regs str kids keys n d)) 2) = spZ regs - 176)
    by (rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl); exact SP2).
  assert (HS3 : st_ok tfibsegs (Ereg regs2 (fs_extraT ++ wv_xsR regs str kids keys n d))
    (fss_retT 0x83f58 176 wv_cs0 [] []) (restrict (w_H W) (mkst regs2 (Z_to_bv 64 0x83f58) mem2 (seg_rom tfibsegs)))).
  { apply (fsw_resume_after_rtU_args B (STK_write_value (2 - k)) (spZ regs) [] ly S W (unpoison U mem2) md2 [] ly S U W
      mem2 md2 0 (ms_regs ms) regs2 (ms_mem ms) 176 (wv_xsR regs str kids keys n d) wv_cs0 [] [] 0x83f58 HBgot HBcell J3
      HARU2 HP2).
    - exact SPT.
    - lia.
    - lia.
    - reflexivity.
    - vm_compute. reflexivity.
    - cbv [wv_cs0 map seq Nat.add]. repeat constructor; cbn; lia.
    - cbv [wv_cs0 map seq Nat.add].
      repeat match goal with
      | |- Forall _ [] => constructor
      | |- Forall _ (YP09.mkChunk ?off2 (CVal 8 ?e2) :: _) =>
          let o1 := eval vm_compute in (off2 - 176) in
          constructor;
          [ eapply (wv_chunk_move E _ _ (spZ regs) (spZ regs - 176) o1 off2 _ e2);
            [ apply CK; cbn [In]; repeat (first [left; reflexivity | right])
            | lia
            | lazymatch goal with
              | |- sv_denot _ (SOff 32 0) = _ =>
                  rewrite !fsw_SOff0; change 32%nat with (32 + 0)%nat; subst E; rewrite !ew_Ereg_extra; reflexivity
              | |- sv_denot _ (SOff (xatom ?j) 0) = sv_denot _ (SOff ?r 0) =>
                  rewrite !fsw_SOff0, fsw_ew_xatom; subst E;
                  cbn [nth wv_xsR wv_xs app map wv_saved];
                  symmetry; apply ew_Ereg_nat; vm_compute; reflexivity
              end ]
          | ]
      end.
    - intros a Ha. apply (mbyte_of_aview tfibsegs). apply Hfr2; [lia|]. rewrite SPT. lia.
    - constructor.
    - apply pairwise_disjoint_of_extents.
      unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, extent_of_region.
      cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E3sp.
      unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address in *.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      repeat match goal with |- _ /\ _ => split end; try exact I; lia.
    - exact I. }
  assert (ER : w64 (raZ (ms_regs ms)) = Z_to_bv 64 0x83f58)
    by (unfold raZ, w64; rewrite R1T; apply Z_to_bv_bv_unsigned).
  rewrite ER.
  fsw_aj_run_toU fsw_wr_tbl_ok HS3 J3 HARU2 A_put.
  + (* the epilogue writes only the frame *)
    cbv [fss_retT fsT_ret_regions ss_mem app].
    eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -176);
      [reflexivity | first [exact E3sp | match goal with |- ?g => idtac "AWRG" g end; fail]
      | cbv [fstk_ret YP09.r_wlo]; lia | cbv [fstk_ret YP09.r_whi]; lia |].
    apply awr_ok_cons_ro; [cbv [fs_got_region YP09.r_wlo YP09.r_whi]; lia|].
    apply awr_ok_cons_ro; [cbv [fs_bcell_region YP09.r_wlo YP09.r_whi]; lia|].
    apply awr_ok_nil.
  + (* ---- at the tail jump to put ---- *)
    lazymatch goal with HS3 : st_ok _ _ ?ssf (restrict _ ?m) |- _ => set (ssJ2 := ssf) in HS3; rename m into msJ end.
    lazymatch goal with HFJ0 : frame_of _ (ss_mem (fss_retT _ _ _ _ _)) mem2 (ms_mem msJ) |- _ => rename HFJ0 into HFJ end.
    lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (mdJ := mdx) in * end.
    pose proof HARU2 as (_ & OK3 & PO3).
    destruct (fsw_rt_atU B (STK_write_value (2 - k) + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S W
      (unpoison U mem) md [] ly S U W mem2 md2 0 (STK_write_value (2 - k)) (spZ regs) [] [] ly S U W (ms_mem msJ) mdJ 0
      HJ2 J3 OK3 PO3 ltac:(lia) ltac:(lia) ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha))) as [HJJ _].
    cbn [app] in HJJ. rewrite Z.add_0_r in HJJ.
    assert (HMJ : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - STK_write_value (2 - k) <= a < spZ regs) ->
      mbyte tfibsegs (rdW W (ms_mem msJ)) a = mbyte tfibsegs (rdW W mem) a).
    { intros a Ha Hn.
      assert (EA : mbyte tfibsegs (rdW W (ms_mem msJ)) a = mbyte tfibsegs (rdW W mem2) a).
      { unfold mbyte, mrestrict.
        rewrite (wv_frameR _ 0x83f58 wv_cs0 mem2 (ms_mem msJ) (spZ regs) HFJ E3sp); [reflexivity|].
        rewrite (wz a Ha). lia. }
      assert (EB : mbyte tfibsegs (rdW W mem2) a = mbyte tfibsegs (rdW W (ms_mem ms)) a).
      { apply (mbyte_of_aview tfibsegs). apply Hfr2; [exact Ha|]. rewrite SPT. lia. }
      assert (EC : mbyte tfibsegs (rdW W (ms_mem ms)) a = mbyte tfibsegs (rdW W mem) a).
      { unfold mbyte, mrestrict. rewrite (wv_frame0 E _ _ _ mem (ms_mem ms) (spZ regs) HF E2); [reflexivity|].
        rewrite (wz a Ha). lia. }
      rewrite EA, EB, EC. reflexivity. }
    assert (HPJ : aregs_preserved regs (ms_regs msJ)).
    { apply (fsw_preserved (w_H W) _ ssJ2 msJ regs (sr_get (ss_regs ssJ2)) HS3); [vm_compute; reflexivity|].
      fsw_cs_cases (sr_get (ss_regs ssJ2)) HS HP2 E3sp. }
    assert (R1J : getr (ms_regs msJ) 1%bv = getr regs 1%bv).
    { rewrite (fsw_reg_extra (w_H W) regs2 _ ssJ2 msJ 1%bv 18 HS3 ltac:(vm_compute; reflexivity)).
      cbn [nth fs_extraT app wv_xsR wv_xs map wv_saved]. reflexivity. }
    assert (G10J : getr (ms_regs msJ) 10%bv = w64 o).
    { rewrite (fsw_reg_atom (w_H W) regs2 _ ssJ2 msJ 10%bv 8%bv 8%nat HS3 ltac:(vm_compute; reflexivity) eq_refl).
      rewrite (fsw_pres _ _ 8%bv HP2 ltac:(unfold acallee_saved; vm_compute; lia)), R8T. exact G10. }
    assert (G11J : getr (ms_regs msJ) 11%bv = w64 str).
    { rewrite (fsw_reg_atom (w_H W) regs2 _ ssJ2 msJ 11%bv 9%bv 9%nat HS3 ltac:(vm_compute; reflexivity) eq_refl).
      rewrite (fsw_pres _ _ 9%bv HP2 ltac:(unfold acallee_saved; vm_compute; lia)), R9T. reflexivity. }
    assert (G12J : getr (ms_regs msJ) 12%bv = w64 (Z.of_nat (length txt))).
    { rewrite (fsw_reg_atom (w_H W) regs2 _ ssJ2 msJ 12%bv 10%bv 10%nat HS3 ltac:(vm_compute; reflexivity) eq_refl).
      rewrite G10', Ev2. reflexivity. }
    rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ msJ HS3 eq_refl).
    change (ss_pc ssJ2) with A_put.
    pose proof HCS as (_ & Hlen & (Hbytes & _)).
    pose proof HCSOK0 as ((Hg & _) & _ & Hceil' & _).
    apply (wv_tail_put (2 - k) ly S U W regs mem md ch ot o v pretty d (PjTree.JNum txt bits) D UL buf cap failed text
      live peak cnt fail (ms_regs msJ) (ms_mem msJ) mdJ str txt HPRE HHEADS HFRL HOUT HGLOB HUH Hspo Hoot Hot16 Hottop
      HCHO HPRESENT HN HPO HUL HD Hroot eq_refl).
    * cbn [WriterValue.wvpieces concat] in HROOM. rewrite app_nil_r in HROOM. exact HROOM.
    * exact HCAP.
    * exact HCL.
    * exact HBUD.
    * exact (wv_garr8_prefix _ _ _ _ Hg).
    * right; left. exists str, kk. split; [exact Hne|]. split; [exact HRB|]. split; [lia | lia].
    * unfold WriterSpec.bytes_ok. eapply Forall_impl; [|exact Hbytes]. intros c Hc'. cbn beta in Hc'. lia.
    * (* 0 <= str: Hs1 reads 4096 + HEAD <= str, and lia keeps the constant HEAD opaque *)
      cbv [HEAD] in Hs1. lia.
    * lia.
    * exact HJJ.
    * exact HARU2.
    * exact HMJ.
    * exact HPJ.
    * exact R1J.
    * exact G10J.
    * exact G11J.
    * exact G12J.
Qed.

(* ================= the closing theorem: all seven arms, every level ================= *)
Lemma wv_spec_or : forall (P1 P2 : PjTree.jv -> Prop) k,
  wv_spec_on P1 k -> wv_spec_on P2 k -> wv_spec_on (fun t => P1 t \/ P2 t) k.
Proof.
intros P1 P2 k H1 H2 ly S U W regs mem md ch ot o v pretty d t D UL buf cap failed text live peak cnt fail [Ht|Ht];
  [exact (H1 ly S U W regs mem md ch ot o v pretty d t D UL buf cap failed text live peak cnt fail Ht)
  |exact (H2 ly S U W regs mem md ch ot o v pretty d t D UL buf cap failed text live peak cnt fail Ht)].
Qed.
(* one level: the leaf arms, and the container arms over the next level *)
Lemma wv_level : forall k, ((k < 2)%nat -> write_value_spec_at B tfibsegs (S k)) ->
  write_value_spec_at B tfibsegs k.
Proof.
intros k IH.
apply (wv_spec_of_arms
  (fun t => t = PjTree.JNull \/ t = PjTree.JFalse \/ t = PjTree.JTrue \/ (exists txt bits, t = PjTree.JNum txt bits))
  (fun t => (exists s, t = PjTree.JStr s) \/ (exists items, t = PjTree.JArr items) \/
            (exists members, t = PjTree.JObj members))
  k).
- intros t. destruct t as [| | |txt bits|s|items|members].
  + left. left. reflexivity.
  + left. right. left. reflexivity.
  + left. right. right. left. reflexivity.
  + left. right. right. right. exists txt, bits. reflexivity.
  + right. left. exists s. reflexivity.
  + right. right. left. exists items. reflexivity.
  + right. right. right. exists members. reflexivity.
- refine (wv_spec_or (fun t => t = PjTree.JNull)
    (fun t => t = PjTree.JFalse \/ t = PjTree.JTrue \/ (exists txt bits, t = PjTree.JNum txt bits)) k (wv_null k) _).
  refine (wv_spec_or (fun t => t = PjTree.JFalse)
    (fun t => t = PjTree.JTrue \/ (exists txt bits, t = PjTree.JNum txt bits)) k (wv_false k) _).
  exact (wv_spec_or (fun t => t = PjTree.JTrue) (fun t => exists txt bits, t = PjTree.JNum txt bits) k
    (wv_true k) (wv_num k)).
- refine (wv_spec_or (fun t => exists s, t = PjTree.JStr s)
    (fun t => (exists items, t = PjTree.JArr items) \/ (exists members, t = PjTree.JObj members)) k (wv_str k) _).
  exact (wv_spec_or (fun t => exists items, t = PjTree.JArr items) (fun t => exists members, t = PjTree.JObj members)
    k (wv_arr k IH) (wv_obj k IH)).
Qed.
(* write_value_spec_at at every level: level 2 (leaves only), then 1, then 0 *)
Theorem write_value_holds : forall k, write_value_spec_at B tfibsegs k.
Proof.
assert (H2 : forall k, (2 <= k)%nat -> write_value_spec_at B tfibsegs k).
{ intros k Hk. apply wv_level. intros Hlt. exfalso. lia. }
assert (H1 : write_value_spec_at B tfibsegs 1).
{ apply wv_level. intros _. apply H2. lia. }
intros k. destruct k as [|[|k]].
- apply wv_level. intros _. exact H1.
- exact H1.
- apply H2. lia.
Qed.
End W.
