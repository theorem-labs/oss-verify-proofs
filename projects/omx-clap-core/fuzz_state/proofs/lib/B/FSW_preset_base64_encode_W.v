(* Modified by Theorem Labs, 2026-10: lib/B (fs.asan-ubsan) twin of lib/A/FSW_preset_base64_encode.v's image layer
   (a working branch 402eb5565fc), the same names over image B's numerals and lib/B's files. *)
(*   rule 24: proves function preset_base64_encode (part W; reuse search: proof-index preset_base64_encode,
   ported from a working branch 402eb5565fc + donor a working branch b96980d72d1).
   Port-from: lib/A/FSW_preset_base64_encode.v at 402eb5565fc lines 1-733 (the definitions before Section W and
   Section W up to `Section R.`); old-B donor a working branch 7676bbb0e23
   lib/B/Prog/preset_base64_encode_blocks.v:11-17 (ENC_KMAGIC 0x10320, ENC_MAGIC, ENC_TABLE 0x21060) and
   lib/B/Prog/preset_base64_encode.v:55-73 (enc_tab_bytes, enc_kmagic_bytes: the table and the magic word are
   read-only image bytes), 140-150 (enc_img_lo). *)
(* preset_base64_encode 0x84700 (preset_file.c:577-608) on fs.asan-ubsan (B A_preset_base64_encode, size 0x54c, 339
   instructions, ret 0x84b54): the IMAGE LAYER of the walk of lib/B/FSH_Fn_writer.v's encode_spec. What this file
   proves: the facts the walk needs about image B and about the allocator's blocks at any state of the walk; no
   instruction is stepped here (the walk is lib/B/FSW_preset_base64_encode_R.v and later files).
   - the user-poisoned shadow bytes are heads of live blocks, so the client bytes of a live block, the image bytes and
     their shadow read the same on the machine's memory and on the allocator's (enc_ush_cover, enc_ra_block,
     enc_mem_img, enc_view_img_shadow, enc_unp_apart, enc_blk_present);
   - g_b64 (B G_B64 = 0x21060, sym g_b64; B listing 0x84758/0x8475c `auipc a2; addi a4,a2,-1784`) holds b64c v at
     G_B64 + v and its 65 bytes are addressable (enc_table), from fs_img_facts' cstr_ok for FS_RO_STRS;
   - the .rodata word the size arithmetic multiplies by sits at 0x10320 in B as well (B listing 0x84728 / 0x84730
     `auipc a1,0xfff8c; ld a1,-1032(a1)`, 0x8473c `mulhu a0,a2,a1`) and holds ENC_MAGIC = 0xaaaaaaaaaaaaaaab
     (enc_magic_val; the pinned fs.asan-ubsan 5ac5ce09 bytes at file offset 0x320 are ab aa aa aa aa aa aa aa);
   - image B's loaded segments (elf-snapshot of the pinned fs.asan-ubsan: its four PT_LOADs page-rounded,
     0x10000 +0x20000 r--, 0x30000 +0x6f000 r-x, 0x9f000 +0x2000 rw-, 0xa1000 +0x55c000 rw-; p_vaddr 0x10000, 0x30d20,
     0x9f678, 0xa1920) are contiguous over [65536, 6279168) (enc_img_rng) and the first is read-only
     (enc_seg0_rom);
   - a live block is application memory outside the shadow band and outside the image (enc_blk_bounds,
     enc_blk_not_img); the kit steps the walk needs that FSW_K lacks (enc_drop_head, enc_seat_ro1, enc_she,
     enc_frame_X, enc_val_agree, enc_ra_agree, enc_reg_val, enc_reg_val0) and the engine's arithmetic shapes
     (enc_U_*: B's index shapes 0x847f0, 0x84828..0x84838, 0x84878..0x84880, 0x848c0 are A's shift / or / and
     shapes; enc_U_addG and enc_U_t0..t3 take the atoms as arguments, because B's round state is not A's).
   Left out of A's text (they encode A's loop-round register allocation, and B's loop uses other registers; a later
   lane states B's after the block map): enc_rin, enc_rout, enc_gf, enc_round_ss, enc_SH, enc_SH1..enc_SH4,
   enc_round_state, enc_sh_ok and enc_sh_seat (stated over A's atoms 12 / 17 / 11 and enc_SH).
   Kept with A's statement: enc_Bx = SOff 18 0, because B's shadow base is s2 = x18 as well (0x84738 `ld s2,0(a0)`,
   and every inline check adds s2), and enc_seat, which is parametric in its register and atom.
   No callee contract and no assumption beyond the Section's: the lane's three instances, the allocator symbols B
   and the two image hypotheses HSS / IMG, as A's Section W has them. Every lemma ends in Qed. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
FSupoison FSupoisonU FSH_YC20 FSH_Gen FSW_preset_base64_encode_blocks.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSH_Fn_writer FSH_Fn_alloc
FSW_K FSW_K3 FSW_rres FSW_ret FSW_writer_tbl.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* the .rodata word 0x10320 the size arithmetic multiplies by, as a region of the entry state (B listing 0x84728 /
   0x84730: auipc a1,0xfff8c; ld a1,-1032(a1) -> 0x10320; old-B donor ENC_KMAGIC) *)
Definition ENC_MAGIC_A : Z := 0x10320.
Definition enc_magic_region : YP09.region :=
  YP09.mkRegion None ENC_MAGIC_A (ENC_MAGIC_A + 8) 0 0 [YP09.mkChunk ENC_MAGIC_A (CVal 8 (SLit ENC_MAGIC))].
(* the 64 letters of g_b64, as lib/B/FSH_Rt.v's FS_RO_STRS lists them at G_B64 *)
Definition enc_b64_bytes : list Z := map WriterSpec.b64c (map Z.of_nat (seq 0 64)).

(* ---- pointer bounds of the walk's states. Pointer atoms are bounded by PTOP, which keeps every shadow byte the
   token run needs inside fs_Bspan (a heap block ends below 2^47 - 4096: enc_blk_bounds). ---- *)
Definition PTOP : Z := 2 ^ 47 - 4096.
(* a byte range outside the shadow band [SHADOW_OFF, SHADOW_OFF + 2^44): a heap block may sit below the band
   (kLowMemEnd) or above it (kHighMemBeg), never in it (enc_blk_bounds) *)
Definition enc_apart (lo hi : Z) : Prop :=
  forall x, lo <= x < hi -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416).
(* the token run's shadow-base register: s2 = x18, which image B's prologue loads with the shadow offset (0x84724 /
   0x8472c `auipc a0,0x1b; ld a0,1260(a0)` reads the .got word 0x9fc10 = FS_GOT_shadow, 0x84738 `ld s2,0(a0)`) and
   every inline shadow check adds (0x847a8, 0x847cc, ...), as in A; atom 18 of a state built on sr_atoms *)
Definition enc_Bx : sv := SOff 18 0.
(* a register re-seated on a fresh atom whose one-byte read-only region holds the byte it points at: the g_b64
   reads, whose address - the table base plus a six-bit index - the engine cannot name *)
Definition enc_seat (ss : sstate) (r : bv 5) (n : nat) (lo hi : Z) : sstate :=
  add_atom (add_atom
    (mkSS (ss_pc ss) (sr_set (ss_regs ss) r (SOff n 0))
       (YP09.mkRegion (Some n) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff (S n) 0))] :: ss_mem ss)
       (ss_resv ss) (ss_facts ss)) n (mkAF lo hi 0)) (S n) (mkAF 0 255 0).

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the shadow-cell pair (lib/B/FSH_Base.v FsShadowSyms: B's .got word 0x9fc10 and cell 0xa8438) *)
Hypothesis HSS : FsShadowSyms B.
(* the image facts (lib/B/FSH_Rt.v): rom_view, the canary cells, and cstr_ok / str_homeA for FS_RO_STRS,
   which holds g_b64 *)
Hypothesis IMG : fs_img_facts tfibsegs B.

(* ---------------------------------------------------------------------------------------------------------- *)
(* 1. the user-poisoned shadow bytes are the heads of live blocks, so they are nowhere near the bytes this walk
      reads: the input block's user bytes, the image, and the output block's user bytes.                       *)
(* ---------------------------------------------------------------------------------------------------------- *)

(* a user-poisoned shadow byte covers an address inside a live block's 16-byte head *)
Lemma enc_ush_cover : forall ly S U x s,
  upoison_ok B ly S U -> fs_heads B ly S U -> in_ush U s = true -> s = shadow_addr x -> 0 <= x ->
  exists h m, In (h, m) (ablocks B ly S) /\ 16 <= req_size m /\ h <= x < h + 16.
Proof.
intros ly S U x s HOK HHEADS Hs Hx Hx0.
apply (proj1 (in_ush_spec U s)) in Hs as (r & Hr & Hrange).
destruct (upoison_ok_In B ly S U r HOK Hr) as (Hal & _ & _ & _).
destruct (HHEADS r Hr) as (Hlen & m & Hin & Hreq).
exists (fst r), m. split; [exact Hin|]. split; [exact Hreq|].
rewrite Hlen in Hrange. unfold shadow_addr in Hrange, Hx.
rewrite Hx in Hrange.
assert (Hd : fst r / 8 <= x / 8 < fst r / 8 + 2) by lia.
pose proof (Z.div_mod (fst r) 8 ltac:(lia)) as D1. pose proof (Z.div_mod x 8 ltac:(lia)) as D2.
pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M2.
rewrite Hal in D1. lia.
Qed.

(* the client bytes of a live block, read on the machine's own memory (the heads of U are elsewhere) *)
Lemma enc_ra_block : forall ly S U (W : world tfibsegs) mem md p n a k,
  ARU tfibsegs B ly S U W mem md -> fs_heads B ly S U ->
  In (p - HEAD, n + HEAD) (ablocks B ly S) -> 0 < n ->
  p <= a -> 0 <= k -> a + k <= p + n ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF a k.
Proof.
intros ly S U W mem md p n a k HARU HHEADS Hin Hn Hpa Hk Hak.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
pose proof (ARU_ok tfibsegs B ly S U W mem md HARU) as HOK.
assert (Hrq : req_size (n + HEAD) = n + HEAD)
  by (unfold req_size; destruct (n + HEAD =? 0) eqn:E; [apply Z.eqb_eq in E; unfold HEAD in *; lia | reflexivity]).
assert (HRA0 : range_addressable (aview tfibsegs (w_H W) (unpoison U mem)) SHADOW_OFF a k).
{ apply (range_addressable_of_block tfibsegs B LAWS ly S W (unpoison U mem) md (p - HEAD) (n + HEAD) a k HAR Hin);
    [unfold HEAD in *; lia | rewrite Hrq; unfold HEAD in *; lia]. }
intros x Hx. destruct (HRA0 x Hx) as (s & Hs & Hsok). exists s. split; [|exact Hsok].
rewrite <- Hs.
assert (Hxlo : 0 <= x) by (destruct (al_blocks tfibsegs B LAWS ly S W (unpoison U mem) md _ _ HAR Hin)
  as (_ & H4096 & _); unfold HEAD in *; lia).
assert (Hsa : shadow_of_addr SHADOW_OFF x = shadow_addr x) by reflexivity.
assert (Hwz : bv_unsigned (Z_to_bv 64 (shadow_of_addr SHADOW_OFF x)) = shadow_of_addr SHADOW_OFF x).
{ apply unsigned_lit_small. unfold shadow_of_addr, SHADOW_OFF in *.
  destruct (al_blocks tfibsegs B LAWS ly S W (unpoison U mem) md _ _ HAR Hin) as (_ & _ & Hceil & _).
  pose proof alloc_ceiling_val as [CR _]. rewrite Hrq in Hceil.
  split; [|]; Z.div_mod_to_equations; lia. }
apply (ARU_view_out tfibsegs B ly S U W mem md _ HARU).
destruct (in_ush U (bv_unsigned (Z_to_bv 64 (shadow_of_addr SHADOW_OFF x)))) eqn:E; [exfalso|reflexivity].
rewrite Hwz, Hsa in E.
destruct (enc_ush_cover ly S U x _ HOK HHEADS E eq_refl Hxlo) as (h & m & Hinh & Hreqm & Hhx).
destruct (Z.eq_dec h (p - HEAD)) as [-> | Hne].
- unfold HEAD in *. lia.
- assert (Hpair : (h, m) <> (p - HEAD, n + HEAD)) by (intros EE; inversion EE; lia).
  pose proof (sep_blocks tfibsegs B LAWS ly S W (unpoison U mem) md h m (p - HEAD) (n + HEAD) HAR Hinh Hin Hpair)
    as Hdj.
  unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. rewrite Hrq in Hdj. unfold HEAD in *. lia.
Qed.

(* an image byte is below the shadow, so the machine's memory and the allocator's agree on it *)
Lemma enc_mem_img : forall ly S U (W : world tfibsegs) mem md x,
  ARU tfibsegs B ly S U W mem md -> 0 <= x < SHADOW_OFF ->
  mbyte tfibsegs (mrestrict (w_H W) mem) x = mbyte tfibsegs (mrestrict (w_H W) (unpoison U mem)) x.
Proof.
intros ly S U W mem md x HARU Hx. unfold mbyte, mrestrict.
rewrite (ARU_mem_low tfibsegs B ly S U W mem md (Z_to_bv 64 x) HARU
  ltac:(rewrite (wz x ltac:(unfold SHADOW_OFF in *; lia)); lia)).
reflexivity.
Qed.

(* the shadow byte of an image address is no user-poisoned byte: a poisoned byte covers a live block's head, and
   a live block's bytes are never in the image (AR_client_img_law) *)
Lemma enc_view_img_shadow : forall ly S U (W : world tfibsegs) mem md x,
  ARU tfibsegs B ly S U W mem md -> fs_heads B ly S U -> in_img tfibsegs x -> 0 <= x < SHADOW_OFF ->
  aview tfibsegs (w_H W) mem (shadow_of_addr SHADOW_OFF x)
  = aview tfibsegs (w_H W) (unpoison U mem) (shadow_of_addr SHADOW_OFF x).
Proof.
intros ly S U W mem md x HARU HHEADS Himg Hx.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
pose proof (ARU_ok tfibsegs B ly S U W mem md HARU) as HOK.
assert (Hwz : bv_unsigned (Z_to_bv 64 (shadow_of_addr SHADOW_OFF x)) = shadow_of_addr SHADOW_OFF x).
{ apply unsigned_lit_small. unfold shadow_of_addr, SHADOW_OFF in *. Z.div_mod_to_equations; lia. }
apply (ARU_view_out tfibsegs B ly S U W mem md _ HARU).
destruct (in_ush U (bv_unsigned (Z_to_bv 64 (shadow_of_addr SHADOW_OFF x)))) eqn:E; [exfalso|reflexivity].
rewrite Hwz in E.
destruct (enc_ush_cover ly S U x _ HOK HHEADS E eq_refl ltac:(lia)) as (h & m & Hinh & Hreqm & Hhx).
destruct (al_client_img tfibsegs B LAWS ly S W (unpoison U mem) md x HAR
  ltac:(left; exists h, m; split; [exact Hinh | lia])) as (_ & Hni).
exact (Hni Himg).
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* 2. g_b64: its 64 letters and their shadow, on the machine's own memory, at any state of the walk            *)
(* ---------------------------------------------------------------------------------------------------------- *)

Lemma enc_g_b64_in_img : forall v, 0 <= v < 65 -> in_img tfibsegs (G_B64 + v).
Proof.
intros v Hv. unfold in_img.
assert (Y : map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs
           = [(65536, 131072); (196608, 454656); (651264, 8192); (659456, 5619712)])
  by (vm_compute; reflexivity).
destruct tfibsegs as [|sg rest]; [cbn in Y; discriminate|].
pose proof (f_equal (hd (0, 0)) Y) as Yh. cbn [map hd] in Yh.
injection Yh as Yb Ysz.
exists sg. split; [left; reflexivity|]. rewrite Yb, Ysz. unfold G_B64. lia.
Qed.

Lemma enc_table : forall ly S U (W : world tfibsegs) mem md,
  ARU tfibsegs B ly S U W mem md -> fs_heads B ly S U ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) (unpoison U mem)) ->
  (forall v, 0 <= v < 64 ->
     val_mem tfibsegs (mrestrict (w_H W) mem) (G_B64 + v) 1 (WriterSpec.b64c v)) /\
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF G_B64 65.
Proof.
intros ly S U W mem md HARU HHEADS HRO.
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
destruct IMG as [_ IMG2].
destruct (IMG2 ly S W (unpoison U mem) md HAR HRO) as (_ & _ & HSTRS & _).
assert (HG : In (G_B64, enc_b64_bytes) FS_RO_STRS)
  by (unfold FS_RO_STRS, enc_b64_bytes; cbn [In]; tauto).
destruct (proj1 (Forall_forall _ _) HSTRS (G_B64, enc_b64_bytes) HG) as [HC _].
cbn [fst snd] in HC.
destruct HC as (HCSTR & H4096 & Hceil & Hlen32 & Hmem & HRA & Hhull & Hnul).
assert (Hlen : Z.of_nat (length enc_b64_bytes) = 64) by reflexivity.
rewrite Hlen in HRA.
split.
- intros v Hv.
  destruct HCSTR as [HARR _].
  destruct (HARR (Z.to_nat v)
    ltac:(assert (HL : length (enc_b64_bytes ++ [0]) = 65%nat) by reflexivity; rewrite HL; lia)) as [HV _].
  assert (Hnth : nth (Z.to_nat v) (enc_b64_bytes ++ [0]) 0 = WriterSpec.b64c v).
  { rewrite app_nth1 by (unfold enc_b64_bytes; rewrite length_map, length_map, length_seq; lia).
    exact (b64_list_nth v Hv). }
  rewrite Hnth in HV. replace (Z.of_nat (Z.to_nat v)) with v in HV by lia.
  intros k Hk.
  rewrite (enc_mem_img ly S U W mem md (G_B64 + v + Z.of_nat k) HARU
    ltac:(assert (Hk0 : k = 0%nat) by lia; subst k; unfold G_B64, SHADOW_OFF; cbn [Z.of_nat]; lia)).
  exact (HV k Hk).
- intros x Hx. destruct (HRA x ltac:(lia)) as (s & Hs & Hsok). exists s. split; [|exact Hsok].
  assert (Himgx : in_img tfibsegs x).
  { replace x with (G_B64 + (x - G_B64)) by lia. apply enc_g_b64_in_img. unfold G_B64 in *. lia. }
  rewrite (enc_view_img_shadow ly S U W mem md x HARU HHEADS Himgx
    ltac:(unfold G_B64, SHADOW_OFF in *; lia)).
  exact Hs.
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* 3. two state steps the kit does not have: dropping a region the walk is done with, and re-seating a         *)
(*    register on a fresh atom whose one-byte read-only region holds the byte it points at (the four g_b64     *)
(*    reads of a round, whose address - the table base plus a six-bit index - the engine cannot name).         *)
(* ---------------------------------------------------------------------------------------------------------- *)

Lemma enc_drop_head : forall E ss ms r rs,
  ss_mem ss = r :: rs -> st_ok tfibsegs E ss ms ->
  st_ok tfibsegs E (mkSS (ss_pc ss) (ss_regs ss) rs (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r rs Hm (A1 & A2 & A3 & A4 & A5 & A6 & A7 & (M1 & M2 & M3) & A9).
rewrite Hm in M1, M2, M3. cbn [regions_wf] in M1. apply andb_prop in M1 as [_ M1].
inversion M2 as [|? ? _ M2']; subst. destruct M3 as [_ M3].
cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
split; [exact A6|]. split; [exact A7|]. split; [|exact A9].
split; [exact M1 | split; [exact M2' | exact M3]].
Qed.

Lemma enc_seat_ro1 : forall E ss ms (r : bv 5) n (av b lo hi : Z),
  st_ok tfibsegs E ss ms -> ss_atoms_lt n ss = true -> r <> 0%bv ->
  YK11.getr (ms_regs ms) r = Z_to_bv 64 av ->
  0 <= lo -> lo <= av <= hi -> hi + 1 <= 2 ^ 64 -> 0 <= b < 256 ->
  val_mem tfibsegs (ms_mem ms) av 1 b ->
  all_disjoint (ewset (ewset E n (Z_to_bv 64 av)) (S n) (Z_to_bv 64 b))
    (YP09.mkRegion (Some n) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff (S n) 0))]) (ss_mem ss) ->
  st_ok tfibsegs (ewset (ewset E n (Z_to_bv 64 av)) (S n) (Z_to_bv 64 b)) (enc_seat ss r n lo hi) ms.
Proof.
intros E ss ms r n av b lo hi HS Hat Hr Hval Hlo0 Hav Hhi Hb Hmem Hdj.
set (E2 := ewset (ewset E n (Z_to_bv 64 av)) (S n) (Z_to_bv 64 b)) in *.
assert (HE2n : ew E2 n = Z_to_bv 64 av)
  by (subst E2; rewrite ew_ewset_other by lia; apply ew_ewset_same).
assert (HE2b : ew E2 (S n) = Z_to_bv 64 b) by (subst E2; apply ew_ewset_same).
assert (HU2n : bv_unsigned (ew E2 n) = av) by (rewrite HE2n; apply unsigned_lit_small; lia).
assert (HS1 : st_ok tfibsegs E2 ss ms).
{ apply (st_ok_agree tfibsegs n E E2 ss ms HS); [subst E2; apply env_agree_ewset2 | exact Hat]. }
assert (HS2 : st_ok tfibsegs E2
  (mkSS (ss_pc ss) (sr_set (ss_regs ss) r (SOff n 0)) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms).
{ apply (st_ok_set_reg tfibsegs E2 ss ms r (SOff n 0) HS1 Hr).
  rewrite fsw_SOff0, HE2n. exact Hval. }
assert (WF : YP09.region_wf (YP09.mkRegion (Some n) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff (S n) 0))]) = true)
  by (vm_compute; reflexivity).
assert (OK : region_ok tfibsegs E2 (ms_mem ms)
  (YP09.mkRegion (Some n) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff (S n) 0))])).
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite HU2n. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val tfibsegs E2 (ms_mem ms) av 0 1%N (SOff (S n) 0) b);
    [rewrite fsw_SOff0; exact HE2b | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
    | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_r; exact Hmem]. }
assert (HS3 : st_ok tfibsegs E2
  (mkSS (ss_pc ss) (sr_set (ss_regs ss) r (SOff n 0))
     (YP09.mkRegion (Some n) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff (S n) 0))] :: ss_mem ss)
     (ss_resv ss) (ss_facts ss)) ms).
{ exact (st_ok_add_region' tfibsegs E2
    (mkSS (ss_pc ss) (sr_set (ss_regs ss) r (SOff n 0)) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms
    (YP09.mkRegion (Some n) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff (S n) 0))]) HS2 WF OK Hdj). }
apply (st_ok_add_fact tfibsegs E2 _ ms (S n) (mkAF 0 255 0)).
- apply (st_ok_add_fact tfibsegs E2 _ ms n (mkAF lo hi 0) HS3).
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HU2n, Z.pow_0_r.
  split; [lia | split; [apply Z.mod_1_r | lia]].
- unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE2b, Z.pow_0_r.
  rewrite (unsigned_lit_small b ltac:(lia)).
  split; [lia | split; [apply Z.mod_1_r | lia]].
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* 4. the .rodata word 0x10320 the size arithmetic reads                                                        *)
(* ---------------------------------------------------------------------------------------------------------- *)

Lemma enc_seg0_rom : forall a, 0x10000 <= a < 0x30000 -> in_rom tfibsegs a.
Proof.
intros a Ha. unfold in_rom.
assert (Y : map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) tfibsegs
           = [(65536, 131072, false); (196608, 454656, false);
              (651264, 8192, true); (659456, 5619712, true)])
  by (vm_compute; reflexivity).
destruct tfibsegs as [|sg rest]; [cbn in Y; discriminate|].
pose proof (f_equal (hd (0, 0, true)) Y) as Yh. cbn [map hd] in Yh.
injection Yh as Yb Ysz Yw.
exists sg. split; [left; reflexivity|]. split; [exact Yw|]. rewrite Yb, Ysz. lia.
Qed.

Lemma enc_rom_mbyte : forall (W : world tfibsegs) m a (bb : byte),
  rom_view tfibsegs W m -> in_rom tfibsegs a -> seg_rom tfibsegs (Z_to_bv 64 a) = Some bb ->
  mbyte tfibsegs (mrestrict (w_H W) m) a = Some bb.
Proof.
intros W m a bb HR Hi He. pose proof (HR a Hi) as X. unfold aview in X. rewrite He in X. cbn [option_map] in X.
destruct (mbyte tfibsegs (mrestrict (w_H W) m) a) as [b'|] eqn:E; cbn [option_map] in X; [|discriminate].
injection X as X. f_equal. apply bv_eq. exact X.
Qed.

Lemma enc_magic_val : forall ly S U (W : world tfibsegs) mem md,
  ARU tfibsegs B ly S U W mem md -> rom_view tfibsegs W (unpoison U mem) ->
  val_mem tfibsegs (mrestrict (w_H W) mem) ENC_MAGIC_A 8 ENC_MAGIC.
Proof.
intros ly S U W mem md HARU HROM k Hk.
rewrite (enc_mem_img ly S U W mem md (ENC_MAGIC_A + Z.of_nat k) HARU
  ltac:(unfold ENC_MAGIC_A, SHADOW_OFF; lia)).
apply (enc_rom_mbyte W (unpoison U mem) (ENC_MAGIC_A + Z.of_nat k) _ HROM
  (enc_seg0_rom (ENC_MAGIC_A + Z.of_nat k) ltac:(unfold ENC_MAGIC_A; lia))).
destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; try (exfalso; lia); vm_compute; reflexivity.
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* 6. a shent of a window inside an addressable range is answered with 0, so the token run takes no            *)
(*    __asan_report_* branch at it; and what a run keeps: every byte outside its regions' write windows.        *)
(* ---------------------------------------------------------------------------------------------------------- *)


Lemma enc_she : forall (W : world tfibsegs) mem (E : env) (n : nat) (b lo hi a k : Z),
  U E enc_Bx = SHADOW_OFF -> U E (SOff n 0) = b ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF a k ->
  a <= b + lo -> b + hi <= a + k -> lo <= hi -> enc_apart (b + lo) (b + hi) ->
  shent_ok tfibsegs enc_Bx E (mrestrict (w_H W) mem) (mkSHE n lo hi).
Proof.
intros W mem E n b lo hi a k HB Hn HRA H1 H2 H3 H4.
apply (shent_ok_of_range tfibsegs (w_H W) mem E enc_Bx n a k b lo hi HRA HB Hn H1 H2).
rewrite (Z.min_l lo hi H3), (Z.max_r lo hi H3). exact H4.
Qed.

(* what a run keeps: every byte outside its regions' write windows (frame_of), read through any bound X of them *)
Lemma enc_frame_X : forall (E : env) rs (m m' : word -> option byte) (X : Z -> Prop),
  frame_of E rs m m' -> (forall a, in_wrange E rs a -> X a) ->
  forall x : word, ~ X (bv_unsigned x) -> m' x = m x.
Proof. intros E rs m m' X HF HX x Hx. apply HF. intros Hin. exact (Hx (HX _ Hin)). Qed.

(* a value and an addressable range read away from the bytes X a keep may change *)
Lemma enc_val_agree : forall (H : word -> bool) (m m' : word -> option byte) (X : Z -> Prop) a (n : nat) v,
  (forall x : word, ~ X (bv_unsigned x) -> m' x = m x) ->
  0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> (forall i, a <= i < a + Z.of_nat n -> ~ X i) ->
  val_mem tfibsegs (mrestrict H m) a n v -> val_mem tfibsegs (mrestrict H m') a n v.
Proof.
intros H m m' X a n v HK Ha Han HX HV k Hk.
rewrite <- (HV k Hk). unfold mbyte, mrestrict.
rewrite (HK (Z_to_bv 64 (a + Z.of_nat k))); [reflexivity|].
rewrite (wz (a + Z.of_nat k) ltac:(lia)). apply HX. lia.
Qed.

Lemma enc_ra_agree : forall (H : word -> bool) (m m' : word -> option byte) (X : Z -> Prop) a n,
  (forall x : word, ~ X (bv_unsigned x) -> m' x = m x) ->
  0 <= a -> a + n <= 2 ^ 47 -> (forall i, SHADOW_OFF <= i < SHADOW_OFF + 17592186044416 -> ~ X i) ->
  range_addressable (aview tfibsegs H m) SHADOW_OFF a n -> range_addressable (aview tfibsegs H m') SHADOW_OFF a n.
Proof.
intros H m m' X a n HK Ha Han HX HRA x Hx.
destruct (HRA x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
rewrite <- Hs. unfold aview, mbyte, mrestrict.
assert (Hsh : SHADOW_OFF <= shadow_of_addr SHADOW_OFF x < SHADOW_OFF + 17592186044416)
  by (unfold shadow_of_addr; Z.div_mod_to_equations; lia).
rewrite (HK (Z_to_bv 64 (shadow_of_addr SHADOW_OFF x))); [reflexivity|].
rewrite (wz (shadow_of_addr SHADOW_OFF x) ltac:(unfold SHADOW_OFF in *; lia)). apply HX. exact Hsh.
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* 7. a live block's bytes: application memory (so nowhere in the shadow band, which is NOT the same as          *)
(*    "below SHADOW_OFF": kHighMemBeg = SHADOW_OFF + 2 ^ 44 < 2 ^ 47, so a block may sit above the band), and    *)
(*    never an image byte.                                                                                      *)
(* ---------------------------------------------------------------------------------------------------------- *)

Lemma enc_blk_bounds : forall ly S (W : world tfibsegs) mem md pb nb a,
  AR tfibsegs B ly S W mem md -> In (pb, nb) (ablocks B ly S) -> pb <= a < pb + req_size nb ->
  4096 <= a /\ a < 2 ^ 47 - 4096 /\ ~ (SHADOW_OFF <= a < SHADOW_OFF + 17592186044416).
Proof.
intros ly S W mem md pb nb a HAR Hin Ha.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct (al_blocks tfibsegs B LAWS ly S W mem md pb nb HAR Hin) as (_ & H4096 & Hceil & Happ & _).
pose proof alloc_ceiling_val as (HC & _).
pose proof (in_app_addr pb (req_size nb) a Happ Ha) as (H0 & [HL | [HH1 HH2]]);
  unfold SHADOW_OFF, kLowShadowBeg, kLowMemEnd, kHighMemBeg in *; lia.
Qed.

Lemma enc_blk_not_img : forall ly S (W : world tfibsegs) mem md pb nb a,
  AR tfibsegs B ly S W mem md -> In (pb, nb) (ablocks B ly S) -> pb <= a < pb + req_size nb ->
  ~ in_img tfibsegs a.
Proof.
intros ly S W mem md pb nb a HAR Hin Ha.
destruct (al_client_img tfibsegs B (AR_laws_ok tfibsegs B) ly S W mem md a HAR
  ltac:(left; exists pb, nb; split; [exact Hin | lia])) as (_ & Hni). exact Hni.
Qed.

(* reading a register the run left as an atom plus a literal offset *)
Lemma enc_reg_val : forall (H : word -> bool) E ss ms (r : bv 5) n z v,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n z ->
  bv_unsigned (ew E n) = v -> 0 <= v + z < 2 ^ 64 -> getr (ms_regs ms) r = w64 (v + z).
Proof.
intros H E ss ms r n z v HS Hr Hv Hz. apply bv_eq.
rewrite (fsw_reg_off H E ss ms r n z v HS Hr Hv Hz). symmetry. apply unsigned_lit_small. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* 8. the engine's arithmetic shapes of image B's index computations: g_b64 plus one of b64_enc's four six-bit   *)
(*    indices (FSW_preset_base64_encode_blocks' enc_ix0 / enc_ix1 / enc_ix2 / enc_ix3 over the engine's own     *)
(*    shift / or / and shapes). B's instruction shapes are A's; the atoms that hold the input bytes and g_b64    *)
(*    are arguments, because B's round state is not A's (g_b64 is a4 = x14 in B, a5 = x15 in A).               *)
(* ---------------------------------------------------------------------------------------------------------- *)


Lemma enc_land63 : forall s, 0 <= s < 64 -> Z.land s 63 = s.
Proof.
intros s Hs. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
Qed.

Lemma enc_U_srl : forall E (x : sv) s v, 0 <= s < 64 -> U E x = v -> U E (SAlu ALU_SRL x (SLit s)) = Z.shiftr v s.
Proof.
intros E x s v Hs Hx. pose proof (U_range E x) as HR. rewrite Hx in HR. unfold M64 in HR.
rewrite U_SAlu. cbn [zalu_raw]. rewrite Hx, U_SLit, (zcanon_id s) by (unfold M64; lia).
rewrite (enc_land63 s Hs), Z.shiftr_div_pow2 by lia.
assert (Hp : 0 < 2 ^ s) by (apply Z.pow_pos_nonneg; lia).
assert (Hp1 : 1 <= 2 ^ s) by (replace 1 with (2 ^ 0) by reflexivity; apply Z.pow_le_mono_r; lia).
apply zcanon_id. unfold M64. split; [apply Z.div_pos; lia|].
assert (v / 2 ^ s <= v) by (apply Z.div_le_upper_bound; [lia | nia]). lia.
Qed.

Lemma enc_U_sll : forall E (x : sv) s v, 0 <= s < 64 -> U E x = v ->
  U E (SAlu ALU_SLL x (SLit s)) = Z.shiftl v s mod 2 ^ 64.
Proof.
intros E x s v Hs Hx. rewrite U_SAlu. cbn [zalu_raw]. rewrite Hx, U_SLit, (zcanon_id s) by (unfold M64; lia).
rewrite (enc_land63 s Hs). reflexivity.
Qed.

Lemma enc_U_or : forall E (x y : sv) a b, U E x = a -> U E y = b ->
  U E (SAlu ALU_OR x y) = Z.lor a b mod 2 ^ 64.
Proof. intros E x y a b Hx Hy. rewrite U_SAlu. cbn [zalu_raw]. rewrite Hx, Hy. reflexivity. Qed.

(* g_b64 + a six-bit index is small, so the add does not wrap (B 0x847fc / 0x8484c / 0x84894 / 0x848d4
   `add a2,a4,a2|a3`, 0x84a38 / 0x84a80 / 0x84abc in the tail: the table base is the first operand) *)
Lemma enc_U_addG : forall E (n : nat) (y : sv) v, ew E n = w64 G_B64 -> U E y = v -> 0 <= v < 64 ->
  U E (SAlu ALU_ADD (SOff n 0) y) = G_B64 + v.
Proof.
intros E n y v Hn Hy Hv. rewrite U_SAlu. cbn [zalu_raw].
rewrite Hy, (U_atom E n G_B64 Hn ltac:(unfold G_B64; lia)).
apply zcanon_id. unfold M64, G_B64. lia.
Qed.

Lemma enc_denot_of_U : forall E (x : sv) v, U E x = v -> sv_denot E x = w64 v.
Proof. intros E x v H. rewrite denot_lit_U, H. reflexivity. Qed.

(* B 0x847f0  srli a2,t5,0x2 *)
Lemma enc_U_t0 : forall E (n0 : nat) b0, ew E n0 = w64 b0 -> 0 <= b0 < 256 ->
  U E (SAlu ALU_SRL (SOff n0 0) (SLit 2)) = b0 / 4.
Proof.
intros E n0 b0 H0 Hb.
rewrite (enc_U_srl E (SOff n0 0) 2 b0 ltac:(lia) (U_atom E n0 b0 H0 ltac:(lia))).
exact (enc_ix0 b0 Hb).
Qed.

(* B 0x84828..0x84838  slli t6,t5,0x10; slli t5,a3,0x8; or a3,t5,t6; slli a3,a3,0x2e; srli a3,a3,0x3a *)
Lemma enc_U_t1 : forall E (n0 n1 : nat) b0 b1, ew E n0 = w64 b0 -> ew E n1 = w64 b1 ->
  0 <= b0 < 256 -> 0 <= b1 < 256 ->
  U E (SAlu ALU_SRL (SAlu ALU_SLL
         (SAlu ALU_OR (SAlu ALU_SLL (SOff n1 0) (SLit 8)) (SAlu ALU_SLL (SOff n0 0) (SLit 16))) (SLit 46))
       (SLit 58))
  = (b0 mod 4) * 16 + b1 / 16.
Proof.
intros E n0 n1 b0 b1 H0e H1e H0 H1.
assert (A1 : U E (SAlu ALU_SLL (SOff n1 0) (SLit 8)) = Z.shiftl b1 8 mod 2 ^ 64)
  by (apply (enc_U_sll E (SOff n1 0) 8 b1); [lia | apply (U_atom E n1 b1 H1e); lia]).
assert (A0 : U E (SAlu ALU_SLL (SOff n0 0) (SLit 16)) = Z.shiftl b0 16 mod 2 ^ 64)
  by (apply (enc_U_sll E (SOff n0 0) 16 b0); [lia | apply (U_atom E n0 b0 H0e); lia]).
assert (AO : U E (SAlu ALU_OR (SAlu ALU_SLL (SOff n1 0) (SLit 8)) (SAlu ALU_SLL (SOff n0 0) (SLit 16)))
             = b0 * 65536 + b1 * 256).
{ rewrite (enc_U_or E _ _ _ _ A1 A0), (enc_or1 b0 b1 H0 H1). apply Z.mod_small. lia. }
rewrite (enc_U_srl E _ 58 _ ltac:(lia) (enc_U_sll E _ 46 _ ltac:(lia) AO)).
exact (enc_ix1 b0 b1 H0 H1).
Qed.

(* B 0x84878..0x84880  or a3,t5,t4; slli a3,a3,0x34; srli a3,a3,0x3a (t5 = b1 << 8 from 0x8482c) *)
Lemma enc_U_t2 : forall E (n1 n2 : nat) b1 b2, ew E n1 = w64 b1 -> ew E n2 = w64 b2 ->
  0 <= b1 < 256 -> 0 <= b2 < 256 ->
  U E (SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_OR (SAlu ALU_SLL (SOff n1 0) (SLit 8)) (SOff n2 0)) (SLit 52))
       (SLit 58))
  = (b1 mod 16) * 4 + b2 / 64.
Proof.
intros E n1 n2 b1 b2 H1e H2e H1 H2.
assert (A1 : U E (SAlu ALU_SLL (SOff n1 0) (SLit 8)) = Z.shiftl b1 8 mod 2 ^ 64)
  by (apply (enc_U_sll E (SOff n1 0) 8 b1); [lia | apply (U_atom E n1 b1 H1e); lia]).
assert (AO : U E (SAlu ALU_OR (SAlu ALU_SLL (SOff n1 0) (SLit 8)) (SOff n2 0)) = b1 * 256 + b2).
{ rewrite (enc_U_or E _ _ _ _ A1 (U_atom E n2 b2 H2e ltac:(lia))), (enc_or2 b1 b2 H1 H2).
  apply Z.mod_small. lia. }
rewrite (enc_U_srl E _ 58 _ ltac:(lia) (enc_U_sll E _ 52 _ ltac:(lia) AO)).
exact (enc_ix2 b1 b2 H1 H2).
Qed.

(* B 0x848c0  andi a3,t4,63 *)
Lemma enc_U_t3 : forall E (n2 : nat) b2, ew E n2 = w64 b2 -> 0 <= b2 < 256 ->
  U E (SAlu ALU_AND (SOff n2 0) (SLit 63)) = b2 mod 64.
Proof.
intros E n2 b2 H2e H2.
rewrite (U_and_lit E (SOff n2 0) 63 ltac:(lia)), (U_atom E n2 b2 H2e ltac:(lia)).
exact (enc_ix3 b2 H2).
Qed.

(* `add rd, rm, rn` on two atoms, as the loop head recomputes the input pointer (B 0x84784 `add a2,s1,a5`) *)
Lemma enc_U_add2 : forall E (m n : nat) cm cn vm vn, ew E m = w64 vm -> ew E n = w64 vn ->
  0 <= vm < 2 ^ 64 -> 0 <= vm + cm < 2 ^ 64 -> 0 <= vn < 2 ^ 64 -> 0 <= vn + cn < 2 ^ 64 ->
  0 <= vm + cm + (vn + cn) < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SOff m cm) (SOff n cn)) = vm + cm + (vn + cn).
Proof.
intros E m n cm cn vm vn Hm Hn Hvm Hvm' Hvn Hvn' Hsum. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E m vm cm Hm Hvm Hvm'), (U_atom_off E n vn cn Hn Hvn Hvn').
apply zcanon_id. unfold M64. lia.
Qed.

(* the same at offset 0 *)
Lemma enc_reg_val0 : forall (H : word -> bool) E ss ms (rg : bv 5) n v,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) rg = SOff n 0 ->
  bv_unsigned (ew E n) = v -> 0 <= v < 2 ^ 64 -> getr (ms_regs ms) rg = w64 v.
Proof.
intros H E ss ms rg n v HS Hr Hv Hb.
pose proof (enc_reg_val H E ss ms rg n 0 v HS Hr Hv ltac:(lia)) as Hx.
rewrite Z.add_0_r in Hx. exact Hx.
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* 9. the bytes of a live block at ANY state of the walk: present, writable and addressable. The walk needs     *)
(*    them of the output block at every round, and ARU is all it has there.                                     *)
(* ---------------------------------------------------------------------------------------------------------- *)

(* a byte apart from the shadow band reads the same on the machine's memory and on the allocator's *)
Lemma enc_unp_apart : forall ly S U (W : world tfibsegs) mem md x,
  ARU tfibsegs B ly S U W mem md -> 0 <= x < 2 ^ 64 -> ~ (SHADOW_OFF <= x < kHighMemBeg) ->
  unpoison U mem (Z_to_bv 64 x) = mem (Z_to_bv 64 x).
Proof.
intros ly S U W mem md x HARU Hx Hap. unfold unpoison.
destruct (in_ush U (bv_unsigned (Z_to_bv 64 x))) eqn:E; [exfalso | reflexivity].
rewrite (wz x Hx) in E.
destruct (ush_facts tfibsegs B ly S U W mem md x HARU E) as (_ & L1 & L2). lia.
Qed.

Lemma enc_blk_present : forall ly S U (W : world tfibsegs) mem md pb nb a,
  ARU tfibsegs B ly S U W mem md -> In (pb, nb) (ablocks B ly S) -> pb <= a < pb + req_size nb ->
  apresent (w_H W) mem a /\ writable_at tfibsegs (mrestrict (w_H W) mem) a.
Proof.
intros ly S U W mem md pb nb a HARU Hin Ha.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
destruct (al_blocks tfibsegs B LAWS ly S W (unpoison U mem) md pb nb HAR Hin) as (_ & _ & _ & _ & Hpres & _).
destruct (enc_blk_bounds ly S W (unpoison U mem) md pb nb a HAR Hin Ha) as (A1 & A2 & A3).
destruct (Hpres a Ha) as ((Hh & b & Hb) & _).
assert (Hap : apresent (w_H W) mem a).
{ split; [exact Hh|]. exists b.
  rewrite <- (enc_unp_apart ly S U W mem md a HARU ltac:(lia) ltac:(unfold kHighMemBeg, SHADOW_OFF in *; lia)).
  exact Hb. }
split; [exact Hap | exact (apresent_writable tfibsegs (w_H W) mem a Hap)].
Qed.

(* every byte of fs.asan-ubsan's four loaded segments is an image byte (the segments are contiguous) *)
Lemma enc_img_rng : forall a, 65536 <= a < 6279168 -> in_img tfibsegs a.
Proof.
intros a Ha. unfold in_img.
assert (Y : map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) tfibsegs
           = [(65536, 131072); (196608, 454656); (651264, 8192); (659456, 5619712)])
  by (vm_compute; reflexivity).
assert (K : forall b n, In (b, n) [(65536, 131072); (196608, 454656); (651264, 8192); (659456, 5619712)] ->
              b <= a < b + n -> exists sg, In sg tfibsegs /\
                Z.of_N (seg_base sg) <= a < Z.of_N (seg_base sg) + Z.of_N (seg_size sg)).
{ intros b n Hp Hr. rewrite <- Y in Hp. apply in_map_iff in Hp as (sg & Hsg & Hin).
  exists sg. split; [exact Hin|]. injection Hsg as Eb En. rewrite Eb, En. exact Hr. }
destruct (Z_lt_le_dec a 196608) as [H1|H1]; [exact (K 65536 131072 ltac:(cbn; tauto) ltac:(lia))|].
destruct (Z_lt_le_dec a 651264) as [H2|H2]; [exact (K 196608 454656 ltac:(cbn; tauto) ltac:(lia))|].
destruct (Z_lt_le_dec a 659456) as [H3|H3]; [exact (K 651264 8192 ltac:(cbn; tauto) ltac:(lia))|].
exact (K 659456 5619712 ltac:(cbn; tauto) ltac:(lia)).
Qed.

End W.
