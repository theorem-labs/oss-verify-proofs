(* check_reject_clean_starved 0x82670 (fs.c:206-226), fs.asan-ubsan (image B), 548 bytes = 137 words (136 instructions
   and a trailing `unimp`): the walk of lib/B/FSH_Fn_checks.v check_reject_clean_starved_spec, closed by
   check_reject_clean_starved_proof (end of file) with every callee a named Section hypothesis (Section W). The B
   RE-WALK of lib/A/FSH_check_reject_clean_starved.v (a working branch 43764928304, CTX-drop form):
   same segments, invariants, state shapes and lemma names, over lib/B's image (YB1v tfibsegs = AsanUbsan) and lib/B's
   kit twins. The instruction table is lib/B/FSW_check_reject_clean_starved_tbl.v; the fake frame is FSW_frame.v's
   fsw_stack_malloc_atU / fsw_flag_storeU, the s8 re-seat FSW_K's fsw_reseat_atom, each program call FSW_K's
   fsw_after_callU_s0_own (crcs_call); the two `beqz` / `bnez` / `bne` data tests are branch conditions added to the
   after-call state (YP06.add_cond).
   Ported from: lib/A/FSH_check_reject_clean_starved.v (above; itself from a Theorem Labs lane's FMW_check_reject_clean.v and fs's
   released plain walk lib/Prog/check_reject_clean_starved.v:663); donor fake-frame steps cgif lib/A/ACez.v:33-40,
   134-222, lib/YCbq.v:1747, :2361.
   rule 24: proves function check_reject_clean_starved (image B entry 0x82670 = lib/B/FSH_Base.v
   A_check_reject_clean_starved; reuse search and CONFIRM: (internal path)).
   B's code (MEASURED 2026-10-29, capstone 5.0.7 RISCV64 + C on the pinned fs.asan-ubsan 5ac5ce0954f8..., the same 548
   bytes in the unstripped twin b1566a1ca816...): every B pc is the fs.asan pc + 0x168 and the encodings are equal
   except the 15 pc-relative call targets and GOT displacements; there is NO UBSan check in this body (no extra
   branch). Its calls (unstripped .symtab): 0x826e0 __asan_stack_malloc_0 0x3d4f4 (FSH_Base PC_stack_malloc_0);
   0x82774 / 0x827e0 fuzz_alloc_live 0x82eec; 0x8278c / 0x827a4 / 0x827c0 / 0x827d8 fuzz_alloc_fail 0x82f18;
   0x82798 preset_base64_decode 0x84c4c; 0x827b4 check_reject_clean 0x81b5c; 0x827cc preset_base64_encode 0x84700;
   0x82888 __asan_handle_no_return 0x5a1ec; 0x8288c abort 0x8cca8. Control flow:
   - 0x82670-0x826ac: frame 0x80, ra/s0..s10 saved, s0 := entry sp, sp re-aligned down to 32 (andi), s1 := sp;
   - 0x826bc-0x826d0: a2 := *(u32 * )*(0x9fc68) (__asan_option_detect_stack_use_after_return, 0xa8440), s8 :=
     *(u64 * )*(0x9fc10) (__asan_shadow_memory_dynamic_address, 0xa8438): under TL : TfibLib B and AR_const_law
     (YG0d.v:460-466) a2 = 1 and s8 = SHADOW_OFF, so `beqz a2` (0x826d8) is not taken;
   - 0x826e0 jal __asan_stack_malloc_0 (a0 = 64): granted (count_cid 0 (frames S) < fs_frames 0, crcs_grant below),
     so s2 = s9 = the fake frame and `bnez s2` (0x826f4) skips the real-stack fallback 0x826f8-0x82710;
   - 0x82714-0x82770: s9 kept at 0x18(s1); frame header (magic, descriptor, pc) at s9 + 0/8/16; s7 := s9 + 32 (n);
     shadow of the frame := f1 f1 f1 f1 f8 f3 f3 f3;
   - 0x82774 fuzz_alloc_live (s6 := live); n's shadow byte := 0; n := SIZE_MAX (uninstrumented `sd`);
   - 0x8278c fuzz_alloc_fail (0); 0x82798 preset_base64_decode (text, &n): refused (fail = cnt), s5 := 0;
   - 0x827a4 fuzz_alloc_fail (SIZE_MAX); 0x827b4 check_reject_clean (0, n = SIZE_MAX, live);
   - 0x827b8 `beqz s4` (body = bd): bd = 0 goes to the epilogue 0x827e8;
   - 0x827c0 fuzz_alloc_fail (0); 0x827cc preset_base64_encode (bd, l): refused, s3 := 0; 0x827d8 fuzz_alloc_fail
     (SIZE_MAX); 0x827dc `bnez s3` (dead); 0x827e0 fuzz_alloc_live; 0x827e4 `bne a0, s6` (dead);
   - 0x827e8-0x82828: frame shadow := f8 at n, magic := retired; s2 <> 0: shadow := f5 x 8, flag := 0 through the
     frame's last word (0x82820-0x82824: the frame is released, so frames S' = frames S); 0x8284c-0x82884 restore, ret.
   - 0x82888 / 0x8288c __asan_handle_no_return / abort: reached only from the two dead branches. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q YG05 YG0t.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YN3u.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSW_K FSW_K3
FSH_Fn_alloc FSH_Fn_writer FSH_Fn_checks FSW_check_reject_clean_starved_tbl FSW_ret FSW_frame FSW_frame3 FSW_strkit.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec check_reject_clean_starved.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* a register index is callee-saved (YG0d.v acallee_saved) *)
Ltac crcs_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?b] => let v := eval vm_compute in (bv_unsigned b) in change (bv_unsigned b) with v end;
  lia.
(* the register r of a machine state, as the symbolic state of HS says *)
Ltac crcs_reg HS r :=
  rewrite (st_ok_restrict_reg tfibsegs _ _ _ _ r HS);
  lazymatch type of HS with st_ok _ _ ?ss _ =>
    let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v end.

(* ---- the fake frame is granted: at most FRL_CHECK = 1 frame is live at the call (the arithmetic of FSH_Fn_entry.v
   fs_fake_granted, restated here: FSH_Fn_entry.v imports the raw cgif ACfn.v, which does not build over RELOC's core) *)
Lemma crcs_count_le : forall cid (l : list (Z * Z)), count_cid cid l <= Z.of_nat (length l).
Proof.
intros cid l. induction l as [|[c p] t IH]; cbn [count_cid length]; [lia|].
destruct (c =? cid); lia.
Qed.
Lemma crcs_grant : forall l : list (Z * Z), Z.of_nat (length l) <= FRL_CHECK -> count_cid 0 l < fs_frames 0.
Proof.
intros l Hl. pose proof (crcs_count_le 0 l) as Hle.
unfold fs_frames, kStackSizeLog. rewrite Z.shiftl_1_l. change (2 ^ (20 - 6 - 0)) with 16384.
unfold FRL_CHECK in Hl. lia.
Qed.
(* the callees (decode, encode) run with starved's frame on top: at most FRL_CRT_CALLEE = 2 frames *)
Lemma crcs_frames_callee : forall (f : Z * Z) (l : list (Z * Z)),
  Z.of_nat (length l) <= FRL_CHECK -> Z.of_nat (length (f :: l)) <= FRL_CRT_CALLEE.
Proof. intros f l Hl. cbn [length]. unfold FRL_CHECK, FRL_CRT_CALLEE in *. lia. Qed.

(* ---- fs_heads depends only on ablocks ---- *)
Lemma crcs_heads : forall B ly S ly' S' U,
  ablocks B ly' S' = ablocks B ly S -> fs_heads B ly S U -> fs_heads B ly' S' U.
Proof. intros B ly S ly' S' U E H r Hr. rewrite E. exact (H r Hr). Qed.

(* ---- fuzz/alloc.c's counters along the walk (fuzz_alloc_fail_spec's saturating store, quiet's bound) ---- *)
Lemma crcs_fail0 : forall c, 0 <= c < 2 ^ 63 -> (if c + 0 <? 2 ^ 64 then c + 0 else SIZE_MAXZ) = c.
Proof. intros c Hc. rewrite (proj2 (Z.ltb_lt _ _)) by lia. lia. Qed.
Lemma crcs_failmax : forall c, 0 <= c -> (if c + SIZE_MAXZ <? 2 ^ 64 then c + SIZE_MAXZ else SIZE_MAXZ) = SIZE_MAXZ.
Proof.
intros c Hc. unfold SIZE_MAXZ. destruct (Z.ltb_spec (c + (2 ^ 64 - 1)) (2 ^ 64)); [|reflexivity]. lia.
Qed.
Lemma crcs_tick : forall c, 0 <= c -> c + 1 < 2 ^ 64 -> (c + 1) mod 2 ^ 64 = c + 1.
Proof. intros c H0 H1. apply Z.mod_small. lia. Qed.

(* ---- the room the decode / encode specs ask (FSH_Fn_writer.v dec_size / enc_size against LIVE_* = 2 ^ 23) ---- *)
Lemma crcs_dec_size : forall tb : list Z, Z.of_nat (length tb) <= PRESET_FILE_MAX_BYTES ->
  FSH_Fn_writer.dec_size tb <= 2 ^ 23.
Proof.
intros tb H. unfold FSH_Fn_writer.dec_size, PRESET_FILE_MAX_BYTES in *.
pose proof (Zle_0_nat (length tb)). Z.div_mod_to_equations. lia.
Qed.
Lemma crcs_enc_size : forall n, 0 <= n <= PRESET_FILE_MAX_BYTES -> FSH_Fn_writer.enc_size n <= 2 ^ 23.
Proof. intros n H. unfold FSH_Fn_writer.enc_size, PRESET_FILE_MAX_BYTES in *. Z.div_mod_to_equations. lia. Qed.

(* ---- where the walk's own stores land, against what it keeps: the stack window (>= alloc_ceiling), the fake frame
   (in_app, not in the image: YCbq.frames_bounds, AR_client_img_law) and the frame's shadow granules ---- *)
(* a byte whose shadow byte is one of a 64-byte, 8-aligned frame's 8 shadow bytes is a byte of that frame *)
Lemma crcs_shadow_inv : forall F a, F mod 8 = 0 -> 0 <= F -> 0 <= a ->
  shadow_addr F <= shadow_addr a < shadow_addr F + 8 -> F <= a < F + 64.
Proof. intros F a HF H0 Ha. unfold shadow_addr. intros H. Z.div_mod_to_equations. lia. Qed.
(* a run's stores outside the image leave every image byte unchanged *)
Lemma crcs_img_keep : forall E rs (m m' : word -> option byte),
  frame_of E rs m m' -> (forall a, in_wrange E rs a -> ~ in_img tfibsegs a) ->
  forall a, in_img tfibsegs a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
intros E rs m m' HF Hw a Ha. apply HF. pose proof (fs_segs_img a Ha) as Hb.
rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold FS_IMG_END in Hb; change (bv_modulus 64) with (2 ^ 64); lia).
intros Hin. exact (Hw a Hin Ha).
Qed.
(* fuzz/alloc.c's statics are image bytes (the last RW segment [0xa1000, 0x5fd000) of tfibsegs holds .data and .bss) *)
Lemma crcs_glob_img : forall a, (G_FAIL <= a < G_FAIL + 8 \/ G_LIVE <= a < G_LIVE + 8 \/ G_PEAK <= a < G_PEAK + 8 \/
  G_COUNT <= a < G_COUNT + 8) -> in_img tfibsegs a.
Proof.
intros a Ha.
assert (Hx : existsb (fun s => (Z.of_N (seg_base s) <=? 0xa1000) && (0x5fd000 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))
  tfibsegs = true) by (vm_compute; reflexivity).
apply existsb_exists in Hx as (sg & Hin & Hc). apply andb_prop in Hc as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2.
exists sg. split; [exact Hin|]. unfold G_FAIL, G_LIVE, G_PEAK, G_COUNT in Ha. lia.
Qed.
(* every read-only byte arodata_okP speaks of is an image byte (the relro range [FS_RLO, FS_RHI) lies in tfibsegs'
   segment [0x9f000, 0xa1000)) *)
Lemma crcs_roP_img : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> in_img tfibsegs a.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr]|].
assert (Hx : existsb (fun s => (Z.of_N (seg_base s) <=? 0x9f000) && (0xa1000 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))
  tfibsegs = true) by (vm_compute; reflexivity).
apply existsb_exists in Hx as (sg & Hin & Hc). apply andb_prop in Hc as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2.
exists sg. split; [exact Hin|]. unfold FS_RLO, FS_RHI in Hr. lia.
Qed.
Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* shadow bytes of addresses below the high-memory end are no application bytes *)
Lemma crcs_shadow_not_app : forall x a, 0 <= x < kHighMemEnd -> in_app a 1 -> shadow_addr x <> a.
Proof.
intros x a Hx Ha E. pose proof (shadow_addr_bounds x Hx) as Hb. pose proof asan_consts as (_ & C2 & C3 & C4 & C5).
unfold in_app, kLowShadowBeg, ASAN_CEIL in *. lia.
Qed.
(* fs_glob survives any memory change that keeps the image bytes (crcs_img_keep, crcs_glob_img) *)
Lemma crcs_glob_keep : forall (W : world tfibsegs) (m m' : word -> option byte) live peak cnt fail,
  (forall a, in_img tfibsegs a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  fs_glob tfibsegs W m live peak cnt fail -> fs_glob tfibsegs W m' live peak cnt fail.
Proof.
intros W m m' live peak cnt fail Hk (G1 & G2 & G3 & G4 & R).
assert (VB : forall g v, (G_FAIL <= g /\ g + 8 <= G_FAIL + 8 \/ G_LIVE <= g /\ g + 8 <= G_LIVE + 8 \/
    G_PEAK <= g /\ g + 8 <= G_PEAK + 8 \/ G_COUNT <= g /\ g + 8 <= G_COUNT + 8) ->
  val_mem tfibsegs (mrestrict (w_H W) m) g 8 v -> val_mem tfibsegs (mrestrict (w_H W) m') g 8 v).
{ intros g v Hg Hv k Hkk. assert (Hi : in_img tfibsegs (g + Z.of_nat k)) by (apply crcs_glob_img; lia).
  unfold mbyte, mrestrict in *. rewrite (Hk _ Hi). exact (Hv k Hkk). }
unfold fs_glob, fs_glob_at in *.
split; [apply VB; [lia | exact G1]|]. split; [apply VB; [lia | exact G2]|].
split; [apply VB; [lia | exact G3]|]. split; [apply VB; [lia | exact G4]|]. exact R.
Qed.
(* arodata_okP survives any memory change that keeps the image bytes (crcs_roP_img) *)
Lemma crcs_arodata_keep : forall B (W : world tfibsegs) (m m' : word -> option byte),
  (forall a, in_img tfibsegs a -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) m) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) m').
Proof.
intros B W m m' Hk HR a Ha Ho He. rewrite <- (HR a Ha Ho He). apply (aview_at tfibsegs). exact (Hk a (crcs_roP_img a Ha)).
Qed.
(* ---- the body arm of caw_answerA: what encode_spec asks of (bd, l), and the live reader block holding the bytes ---- *)
Lemma crcs_body : forall B ly S U (W : world tfibsegs) mem tb bd l,
  caw_answerA tfibsegs B ly S U W mem tb bd l -> bd <> 0 -> Z.of_nat (length tb) <= PRESET_FILE_MAX_BYTES ->
  exists bs m, WriterSpec.bytes_ok bs /\ Z.of_nat (length bs) = l /\ 0 <= l <= PRESET_FILE_MAX_BYTES /\ l <= 2 ^ 27 /\
    zbytes_at tfibsegs W mem bd bs /\ 4096 <= bd /\ bd + l <= alloc_ceiling /\
    fs_rblock tfibsegs B ly S W mem bd m /\ l <= m.
Proof.
intros B ly S U W mem tb bd l [(_ & Hbd & _) | (bs & m & Hdec & _ & Hl & Hsrc & Hrb & Hlm & _)] Hne Htb;
  [exfalso; exact (Hne Hbd)|].
destruct Hsrc as (Hz & H4096 & Hceil & _).
pose proof (check_reject_clean_starved.crs_dec_len tb bs Hdec) as Hlen.
exists bs, m. split.
- apply Forall_forall. intros b Hb. apply In_nth with (d := 0) in Hb as (j & Hj & <-). exact (proj2 (Hz j Hj)).
- unfold PRESET_FILE_MAX_BYTES in *. split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact Hz|]. split; [lia|]. split; [lia|]. split; [exact Hrb | lia].
Qed.
(* ---- the frame-pointer chain at a callee's entry: starved keeps s0 = its entry sp (0x826a8) with ra / s0 saved at
   sp0 - 8 / sp0 - 16, so a callee entered with s0 = sp0 sees starved's record on top of starved's own chain; with
   sp0 below ly_top - 16 (the spec's `spZ regs + 32 <= ly_top ly`) the trace is the return address on top of starved's
   trace (YCbq.achain_push) ---- *)
Lemma crcs_chain : forall ly (rd rd' : reader) sp0 v ch ra spc,
  achain ly rd sp0 v ch -> sp0 < ly_top ly - 16 -> ly_top ly <= 2 ^ 64 ->
  (forall a, sp0 <= a < 2 ^ 64 -> rd' a = rd a) ->
  rdword rd' (sp0 - 8) = Some ra -> rdword rd' (sp0 - 16) = Some v -> 4096 <= ra ->
  alloc_ceiling <= sp0 -> sp0 mod 8 = 0 -> spc + 16 <= sp0 ->
  achain ly rd' spc sp0 ((sp0, ra, v) :: ch) /\ spine ((sp0, ra, v) :: ch) = ra :: spine ch.
Proof.
intros ly rd rd' sp0 v ch ra spc Hc Hlt Htop Hk H8 H16 Hra Hceil Hal Hsp.
split; [|reflexivity].
exact (achain_push ly rd rd' sp0 v ra ch spc Hc Htop Hk H8 H16 Hra Hceil Hal Hlt Hsp).
Qed.
End p.

(* ================= the walk ================= *)
(* the entry state: fss0T (the shadow-base cells) with the use-after-return cells (FSW_K fs_uar_regions) and the
   0x80-byte frame of the prologue *)
Definition crcs_ss0 : sstate := fss0T_args A_check_reject_clean_starved 128 fs_uar_regions [].
(* the state at the call of __asan_stack_malloc_0 (0x826e0 -> 0x3d4f4): MEASURED (vm_compute) sp and s1 hold the
   re-aligned SAlu AND (SOff 2 (-128)) (SLit (-32)), a0 = 64, a2 = 1 (the flag: `beqz a2` 0x826d8 not taken), s8 = the
   shadow base atom 32, ra = 0x826e4 *)
Definition crcs_ss1 : sstate :=
  Eval vm_compute in fst (sym_run_toN tfibsegs crcs_tbl FUEL PC_stack_malloc_0 crcs_ss0).
(* starved's instance at 0x826e4: env Ereg regs2 (crcs_extra regs flag), atom 32 the shadow base, atoms 33..44 the
   twelve values the prologue saved (ra, s0, s1, s2..s10 of the entry, at s0 - 8 .. s0 - 96), atom 45 the flag address;
   the slot 0x18(s1) at atom 9, the frame at atom 10 (a0) *)
Definition crcs_extra (regs : bvmap 5 word) (flag : Z) : list word :=
  [Z_to_bv 64 SHADOW_OFF; YK11.getr regs 1%bv; YK11.getr regs 8%bv; YK11.getr regs 9%bv; YK11.getr regs 18%bv;
   YK11.getr regs 19%bv; YK11.getr regs 20%bv; YK11.getr regs 21%bv; YK11.getr regs 22%bv; YK11.getr regs 23%bv;
   YK11.getr regs 24%bv; YK11.getr regs 25%bv; YK11.getr regs 26%bv; Z_to_bv 64 flag].
Definition crcs_sv_chunks : list YP09.chunk :=
  [YP09.mkChunk (-8) (CVal 8 (SOff 33 0)); YP09.mkChunk (-16) (CVal 8 (SOff 34 0));
   YP09.mkChunk (-24) (CVal 8 (SOff 35 0)); YP09.mkChunk (-32) (CVal 8 (SOff 36 0));
   YP09.mkChunk (-40) (CVal 8 (SOff 37 0)); YP09.mkChunk (-48) (CVal 8 (SOff 38 0));
   YP09.mkChunk (-56) (CVal 8 (SOff 39 0)); YP09.mkChunk (-64) (CVal 8 (SOff 40 0));
   YP09.mkChunk (-72) (CVal 8 (SOff 41 0)); YP09.mkChunk (-80) (CVal 8 (SOff 42 0));
   YP09.mkChunk (-88) (CVal 8 (SOff 43 0)); YP09.mkChunk (-96) (CVal 8 (SOff 44 0))].
(* the walk's state at the return address r of each program call: the fake frame at s9 (atom 25) with the frame
   words fcs it keeps, the frame's shadow at s8 (atom 24) with the shadow bytes scs it keeps, the saved words at s0
   (atom 8) *)
Definition crcs_fsS (r : Z) (fcs scs : list YP09.chunk) : sstate :=
  mkSS r sr_atoms
    [YP09.mkRegion (Some 25%nat) 0 64 0 64 fcs; YP09.mkRegion (Some 24%nat) 0 8 0 8 scs;
     fs_ret_s0_region (-96) 0 crcs_sv_chunks]
    None (mkFacts [(8%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] []).
Definition crcs_fs (r : Z) (fcs : list YP09.chunk) : sstate := crcs_fsS r fcs [].
(* n's shadow byte (s8 + 4, the granule of frame + 32): 00, addressable, from 0x82780 on *)
Definition crcs_nsh : YP09.chunk := YP09.mkChunk 4 (CVal 1 (SLit 0)).
Definition crcs_ss2 : sstate := fsw_resume_ss 0x826e4 (-96) 0 crcs_sv_chunks 9 0x18 0x20 10 (SOff 45 0) 0.


(* ================= walk helpers, generic in B ================= *)
Section H. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* fuzz/alloc.c's statics: a closed footprint of image bytes, none read-only *)
Lemma crcs_pstat_closed : ~ YI16.sink_open_fp FS_PSTAT_FP.
Proof.
intros (r & Hr & H). unfold FS_PSTAT_FP in Hr.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in H; lia.
Qed.
Lemma crcs_pstat_img : forall a, inFP FS_PSTAT_FP a -> in_img tfibsegs a.
Proof.
intros a (r & Hr & H1 & H2). apply crcs_glob_img. unfold FS_PSTAT_FP in Hr.
unfold G_FAIL, G_LIVE, G_PEAK, G_COUNT.
destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in H1, H2; lia.
Qed.
Lemma crcs_roP_notFP : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> ~ inFP FS_PSTAT_FP a.
Proof.
intros a Ha (r & Hr & H1 & H2).
assert (Hx : forallb (fun s => seg_writable s || forallb (fun r => (snd r <=? Z.of_N (seg_base s)) ||
  (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? fst r)) FS_PSTAT_FP) tfibsegs = true) by (vm_compute; reflexivity).
destruct Ha as [(sg & Hin & Hw & Hs) | Hr2].
- pose proof (proj1 (forallb_forall _ _) Hx sg Hin) as Hs'. cbv beta in Hs'. rewrite Hw in Hs'. cbn [orb] in Hs'.
  pose proof (proj1 (forallb_forall _ _) Hs' r Hr) as Hr'.
  apply Bool.orb_true_iff in Hr' as [Hr'|Hr']; apply Z.leb_le in Hr'; lia.
- unfold FS_PSTAT_FP in Hr. unfold FS_RLO, FS_RHI in Hr2.
  destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in H1, H2; lia.
Qed.
(* arodata_okP across a journal at FS_PSTAT_FP (its image clause, YCbq.v:362) *)
Lemma crcs_arodata_j : forall STK sp0 ly S W mem md own ly' S' W' mem' md' k,
  @ajournal rc SK tfibsegs B STK sp0 FS_PSTAT_FP ly S W mem md own ly' S' W' mem' md' k ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) mem) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W') mem').
Proof.
intros STK sp0 ly S W mem md own ly' S' W' mem' md' k HJ HR a Ha Ho He.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a (crcs_roP_img a Ha) Ho He (crcs_roP_notFP a Ha) (fp_spares_closed _ a crcs_pstat_closed)).
exact (HR a Ha Ho He).
Qed.

(* the callee's fpreU at a program call: FSW_ret.v fsw_fpreU_at with the caller's FP and own generic *)
Lemma crcs_fpreU : forall STK sp0 FP ly S U W0 mem md own lyc Sc W memc mdc k regsc STK1 (o : Z) ch1,
  @ajournal rc SK tfibsegs B STK sp0 FP ly S W0 (unpoison U mem) md own lyc Sc W (unpoison U memc) mdc k ->
  ARU tfibsegs B lyc Sc U W memc mdc ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) memc) ->
  spZ regsc = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 0 <= STK1 -> STK1 - o <= STK ->
  YK0s.ret_ok (getr regsc 1) -> 4096 <= raZ regsc ->
  getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
  achain lyc (aview tfibsegs (w_H W) (unpoison U memc)) (spZ regsc) (s0Z regsc) ch1 ->
  fpreU tfibsegs B STK1 lyc Sc U W regsc memc mdc ch1.
Proof.
intros STK sp0 FP ly S U W0 mem md own lyc Sc W memc mdc k regsc STK1 o ch1 HJ HARU Hro Hsp Hal Hneg Hstk1 Hbud Hra
  Hra4 Hgp Htp Hch.
destruct HARU as (_ & OK & PO).
split; [|exact Hro]. split; [|split; [exact OK | exact PO]].
exact (afn_pre_at tfibsegs B STK sp0 FP ly S W0 (unpoison U mem) md own lyc Sc W (unpoison U memc) mdc k regsc STK1 o ch1
  HJ Hsp Hal Hneg Hstk1 Hbud Hra Hra4 Hgp Htp Hch).
Qed.

(* bytes of a live frame of the caller, outside the callee's footprint, keep their value across the callee *)
Lemma crcs_val_keep_call : forall STKc sp1 FPc lyc Sc Uc (W : world tfibsegs) memC mdC ly' S' U' W' mem' md' kc cid pos
    a n v,
  @ajournal rc SK tfibsegs B STKc sp1 FPc lyc Sc W (unpoison Uc memC) mdC [] ly' S' W' (unpoison U' mem') md' kc ->
  ARU tfibsegs B lyc Sc Uc W memC mdC -> upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  In (cid, pos) (frames Sc) -> 0 <= cid ->
  frame_addr lyc cid pos <= a -> a + Z.of_nat n <= frame_addr lyc cid pos + fs_frame_bytes cid ->
  (forall x, a <= x < a + Z.of_nat n -> ~ inFP FPc x) ->
  val_mem tfibsegs (mrestrict (w_H W) memC) a n v -> val_mem tfibsegs (mrestrict (w_H W') mem') a n v.
Proof.
intros STKc sp1 FPc lyc Sc Uc W memC mdC ly' S' U' W' mem' md' kc cid pos a n v HJc HARUc OK' PO' Hin Hc0 Hlo Hhi
  HnFP HV k Hk.
pose proof HJc as (HAR' & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & F4 & _).
assert (HARU' : ARU tfibsegs B ly' S' U' W' mem' md') by (split; [exact HAR' | split; [exact OK' | exact PO']]).
pose proof (ARU_AR tfibsegs B lyc Sc Uc W memC mdC HARUc) as HARc.
assert (Hin' : In (cid, pos) (frames S')) by (rewrite Hfrs; exact Hin).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _).
assert (EA : frame_addr ly' cid pos = frame_addr lyc cid pos) by (unfold frame_addr; rewrite EF; reflexivity).
destruct (al_frames _ _ LAWS lyc Sc W (unpoison Uc memC) mdC cid pos HARc Hin) as (_ & _ & Hfc & _).
destruct (al_frames _ _ LAWS ly' S' W' (unpoison U' mem') md' cid pos HAR' Hin') as (_ & _ & Hf' & _).
destruct (frames_bounds tfibsegs B LAWS lyc Sc W (unpoison Uc memC) mdC cid pos HARc Hin) as (H4096 & Hceil & _).
pose proof asan_consts as (C1 & _).
set (x := a + Z.of_nat k).
assert (Hx : frame_addr lyc cid pos <= x < frame_addr lyc cid pos + fs_frame_bytes cid) by (subst x; lia).
rewrite <- (HV k Hk). apply (mbyte_of_aview tfibsegs). fold x.
rewrite <- (aview_at tfibsegs (w_H W') (unpoison U' mem') mem' x).
2:{ apply (fsw_unpoison_notowned B ly' S' U' W' mem' md' x HARU'); [lia|].
    rewrite EA in Hf'. exact (proj2 (Hf' x Hx)). }
rewrite (F4 cid pos x Hin (or_introl Hx) (HnFP x ltac:(subst x; lia))).
apply (aview_at tfibsegs).
apply (fsw_unpoison_notowned B lyc Sc Uc W memC mdC x HARUc); [lia|]. exact (proj2 (Hfc x Hx)).
Qed.
(* the same for a shadow byte of a live frame of the caller (ajournal's frame clause covers the frame's shadow) *)
Lemma crcs_sh_keep_call : forall STKc sp1 FPc lyc Sc Uc (W : world tfibsegs) memC mdC ly' S' U' W' mem' md' kc cid pos
    o v,
  @ajournal rc SK tfibsegs B STKc sp1 FPc lyc Sc W (unpoison Uc memC) mdC [] ly' S' W' (unpoison U' mem') md' kc ->
  ARU tfibsegs B lyc Sc Uc W memC mdC -> upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  In (cid, pos) (frames Sc) -> 0 <= cid -> 0 <= o < fs_frame_bytes cid / 8 ->
  ~ inFP FPc (shadow_addr (frame_addr lyc cid pos) + o) ->
  val_mem tfibsegs (mrestrict (w_H W) memC) (shadow_addr (frame_addr lyc cid pos) + o) 1 v ->
  val_mem tfibsegs (mrestrict (w_H W') mem') (shadow_addr (frame_addr lyc cid pos) + o) 1 v.
Proof.
intros STKc sp1 FPc lyc Sc Uc W memC mdC ly' S' U' W' mem' md' kc cid pos o v HJc HARUc OK' PO' Hin Hc0 Ho HnFP HV k Hk.
pose proof HJc as (HAR' & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & F4 & _).
assert (HARU' : ARU tfibsegs B ly' S' U' W' mem' md') by (split; [exact HAR' | split; [exact OK' | exact PO']]).
pose proof (ARU_AR tfibsegs B lyc Sc Uc W memC mdC HARUc) as HARc.
assert (Hin' : In (cid, pos) (frames S')) by (rewrite Hfrs; exact Hin).
pose proof Hly as (_ & _ & _ & _ & _ & EF & _).
assert (EA : frame_addr ly' cid pos = frame_addr lyc cid pos) by (unfold frame_addr; rewrite EF; reflexivity).
destruct (al_frames _ _ LAWS lyc Sc W (unpoison Uc memC) mdC cid pos HARc Hin) as (_ & _ & _ & Hsc).
destruct (al_frames _ _ LAWS ly' S' W' (unpoison U' mem') md' cid pos HAR' Hin') as (_ & _ & _ & Hs').
destruct (frames_bounds tfibsegs B LAWS lyc Sc W (unpoison Uc memC) mdC cid pos HARc Hin) as (H4096 & Hceil & _).
pose proof asan_consts as (C1 & _).
rewrite EA in Hs'.
set (F := frame_addr lyc cid pos) in *.
assert (Hk0 : Z.of_nat k = 0) by lia.
set (x := shadow_addr F + o + Z.of_nat k).
assert (Hxo : x = shadow_addr F + o) by (subst x; lia).
assert (Hxr : 0 <= x < 2 ^ 64) by (rewrite Hxo; unfold shadow_addr, SHADOW_OFF; Z.div_mod_to_equations; lia).
rewrite <- (HV k Hk). apply (mbyte_of_aview tfibsegs). fold x.
rewrite <- (aview_at tfibsegs (w_H W') (unpoison U' mem') mem' x).
2:{ apply (fsw_unpoison_notowned B ly' S' U' W' mem' md' x HARU' Hxr). rewrite Hxo. exact (proj2 (Hs' o Ho)). }
assert (Hzr : in_zr x (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)).
{ unfold in_zr. cbn [fst snd]. fold F. rewrite Hxo. lia. }
assert (HnFPx : ~ inFP FPc x) by (rewrite Hxo; exact HnFP).
rewrite (F4 cid pos x Hin (or_intror Hzr) HnFPx).
apply (aview_at tfibsegs).
apply (fsw_unpoison_notowned B lyc Sc Uc W memC mdC x HARUc Hxr). rewrite Hxo. exact (proj2 (Hsc o Ho)).
Qed.
(* a frame variable at frame + 32 (F 32-aligned) is addressable when its granule's shadow byte (shadow + 4) is 00 *)
Lemma crcs_shadow_addressable : forall (W : world tfibsegs) mem F,
  F mod 32 = 0 -> 0 <= F ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (shadow_addr F + 4) 1 0 ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF (F + 32) 8.
Proof.
intros W mem F HF H0 HV x Hx. exists 0. split; [|left; reflexivity].
assert (Hs : shadow_of_addr SHADOW_OFF x = shadow_addr F + 4).
{ unfold shadow_of_addr, shadow_addr. Z.div_mod_to_equations. lia. }
rewrite Hs. unfold aview. pose proof (HV 0%nat ltac:(lia)) as H1. change (Z.of_nat 0) with 0 in H1.
rewrite Z.add_0_r in H1. rewrite H1.
vm_compute. reflexivity.
Qed.

(* chunk values through an environment change that keeps the atoms they mention *)
Lemma crcs_chunk_eq : forall E1 E2 m b c,
  (forall i, YP09.cbyte tfibsegs E1 (b + YP09.c_off c) (YP09.c_val c) i = YP09.cbyte tfibsegs E2 (b + YP09.c_off c) (YP09.c_val c) i) ->
  YP09.chunk_ok tfibsegs E1 m b c -> YP09.chunk_ok tfibsegs E2 m b c.
Proof. intros E1 E2 m b c Hc H i Hi. destruct (H i Hi) as (bt & H1 & H2). exists bt. rewrite <- Hc. auto. Qed.
Lemma crcs_sv_conv : forall E1 E2 m b, (forall n, (33 <= n < 45)%nat -> ew E1 n = ew E2 n) ->
  Forall (YP09.chunk_ok tfibsegs E1 m b) crcs_sv_chunks -> Forall (YP09.chunk_ok tfibsegs E2 m b) crcs_sv_chunks.
Proof.
intros E1 E2 m b Hj HF. apply Forall_forall. intros c Hc.
pose proof (proj1 (Forall_forall _ _) HF c Hc) as H1. revert H1. apply crcs_chunk_eq. intros i.
unfold crcs_sv_chunks in Hc.
repeat (destruct Hc as [<-|Hc];
  [cbn [YP09.c_val YP09.c_off YP09.cbyte]; rewrite !fsw_SOff0;
   match goal with |- context [ew E1 ?n] => rewrite (Hj n ltac:(lia)) end; reflexivity|]).
destruct Hc.
Qed.
Lemma crcs_ew_extra : forall regs extra n, (32 <= n)%nat -> ew (Ereg regs extra) n = nth (n - 32) extra (Z_to_bv 64 0).
Proof. intros regs extra n Hn. replace n with (32 + (n - 32))%nat at 1 by lia. apply ew_Ereg_extra. Qed.
(* a chunk read under one environment, restated with another expression of the same value *)
Lemma crcs_chunk_conv : forall E1 E2 m b o w v1 v2,
  YP09.chunk_ok tfibsegs E1 m b (YP09.mkChunk o (CVal w v1)) -> sv_denot E1 v1 = sv_denot E2 v2 ->
  YP09.chunk_ok tfibsegs E2 m b (YP09.mkChunk o (CVal w v2)).
Proof.
intros E1 E2 m b o w v1 v2 H Hv i Hi. destruct (H i Hi) as (bt & H1 & H2). exists bt.
cbn [YP09.c_val YP09.c_off YP09.cbyte] in *. rewrite <- Hv. auto.
Qed.

(* a register set to an expression of its own value *)
Lemma crcs_set_reg : forall (H : word -> bool) E ss ms (r : bv 5) e,
  st_ok tfibsegs E ss (restrict H ms) -> r <> 0%bv -> getr (ms_regs ms) r = sv_denot E e ->
  st_ok tfibsegs E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e) (ss_mem ss) (ss_resv ss) (ss_facts ss)) (restrict H ms).
Proof. intros H E ss ms r e HS Hr He. exact (st_ok_set_reg tfibsegs E ss (restrict H ms) r e HS Hr He). Qed.
End H.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* ---- the Section hypotheses (owners in brackets): every callee is its own spec, and the image / runtime facts are
   named exactly as the kit takes them (lib/B/FSW_frame.v:49-50, FSW_K fsw_uar_regions_ok, lib/B/FSH_Base.v
   FsShadowSyms); RELOC-B's TfibLib (lib/B/YCeg.v:27-38) is the owner that discharges errno_low (tl_env), ML
   (tl_universe) and the two cell pairs (tl_got_shadow / tl_shadow_cell, tl_got_uar / tl_uar_cell). No CTX. Every
   sink-dependent name in a statement of this file (the six specs, fpostU, ajournal; MEASURED by `About` over every
   identifier of the file's statements: no other takes a sink_head) is applied to the Section's fx / rc / SK
   EXPLICITLY (`@`), so no instance search picks the sink argument of a hypothesis, a lemma or the theorem ---- *)
Hypothesis IMG : @fs_img_facts rc tfibsegs B.                 (* [S0] lib/B/FSH_Rt.v, the statement's own *)
Hypothesis HSS : FsShadowSyms B.                              (* [S0 / RELOC-B] lib/B/FSH_Base.v: GOT 0x9fc10, cell 0xa8438 *)
Hypothesis HGUAR : as_got_uar B = fs_D_GOT_uar.               (* [RELOC-B] TfibLib tl_got_uar (GOT 0x9fc68) *)
Hypothesis HUCELL : as_uar_cell B = fs_D_uar_cell.            (* [RELOC-B] TfibLib tl_uar_cell (0xa8440) *)
Hypothesis errno_low : api_env tfibsegs B.                    (* [RELOC-B] TfibLib tl_env; lib/B/FSW_frame.v:49 *)
Hypothesis ML : model_laws (as_universe B).                   (* [RELOC-B] TfibLib tl_universe; lib/B/FSW_frame.v:50 *)
(* [RUNTIME / S0] lib/B/FSH_Rt.v: FsRt's fr_stack_malloc_0 by its field type, the only FsRt field the walk uses *)
Hypothesis RTsm0 :
  pc_stack_malloc (as_code B) 0 = PC_stack_malloc_0 /\ @FSupoisonU.astack_malloc_realizesU fx rc tfibsegs B 0.
Hypothesis LIVE : @fuzz_alloc_live_spec fx rc SK tfibsegs B.  (* [ALLOC] lib/B/FSH_Fn_alloc.v *)
Hypothesis FAIL : @fuzz_alloc_fail_spec fx rc SK tfibsegs B.  (* [ALLOC] lib/B/FSH_Fn_alloc.v *)
Hypothesis CRC : @check_reject_clean_spec fx rc SK tfibsegs B.  (* [CHECKS] lib/B/FSH_Fn_checks.v *)
Hypothesis DEC : @decode_spec_ff fx rc SK B tfibsegs.         (* [WRITER] lib/B/FSH_Fn_writer.v *)
Hypothesis ENC : @encode_spec fx rc SK B tfibsegs.            (* [WRITER] lib/B/FSH_Fn_writer.v *)
(* fuzz/alloc.c's statics are not errno (IMG's footprint conjunct, lib/B/FSH_Rt.v fs_img_facts) *)
Lemma HPST_ERRNO : forall a, inFP FS_PSTAT_FP a -> ~ (as_errno B <= a < as_errno B + 4).
Proof. intros a Ha. exact (proj2 (proj1 IMG a Ha)). Qed.
(* the engine's laws, proved for fs (not assumed) *)
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
Let crcs_ML : model_laws (as_universe B) := ML.
Lemma crcs_SMP : stack_malloc_progressP B.
Proof. intros s cid Hw Hc Hn. exact (stack_malloc_progress (as_universe B) s cid Hw Hc Hn). Qed.
Lemma crcs_ASF : astack_free_law tfibsegs B.
Proof. exact (astack_free_law_ok tfibsegs B). Qed.
(* the donor's link_FFL (cgif lib/A/ACfi.v:76-87) over S0's image cover (YF0x.img_cover_of_ledger, as FSW_rd.v:99) *)
Lemma crcs_FFL : frame_flag_lawP tfibsegs B.
Proof.
intros ly S W mem md cid pos HAR Hin.
destruct (al_flag _ _ LAWS ly S W mem md cid pos HAR Hin) as (Hp & Ho & Happ & Hceil).
destruct (al_client_img _ _ LAWS ly S W mem md (flag_addr ly cid pos) HAR) as [Hhull Himg].
{ right. right. exists cid, pos. split; [exact Hin | reflexivity]. }
pose proof HAR as (M & L & _). pose proof (YF0x.img_cover_of_ledger ly S md L) as [C1 C2].
unfold YF0x.TFIB_IMG_LO, YF0x.TFIB_IMG_END in C1, C2.
destruct Happ as [H4096 Hz]. unfold in_zr in Hhull.
split; [exact Hp|]. split; [exact Ho|]. split.
- split; [|exact Himg]. unfold app_addr, in_app, ASAN_CEIL in *. lia.
- split; [exact H4096|]. split; [|exact Hceil]. unfold zone2, off_img, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
(* the shadow cells at the names FSW_K's entry takes *)
Lemma HGOT : as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address.
Proof. exact (proj1 HSS). Qed.
Lemma HCELL : as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address.
Proof. exact (proj2 HSS). Qed.
Lemma HPC0 : pc_stack_malloc (as_code B) 0 = PC_stack_malloc_0.
Proof. exact (proj1 RTsm0). Qed.

Lemma crcs_stk : STK_check_reject_clean_starved = 16767.
Proof. reflexivity. Qed.

Lemma crcs_entry : forall ly S U (W : world tfibsegs) regs mem md ch,
  afn_preU tfibsegs B STK_check_reject_clean_starved ly S U W regs mem md ch ->
  st_ok tfibsegs (Ereg regs fs_extraT) crcs_ss0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 A_check_reject_clean_starved) mem (seg_rom tfibsegs))).
Proof.
intros ly S U W regs mem md ch HPRE.
pose proof (fsw_sp B _ ly S U W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _). pose proof crcs_stk as FS.
assert (E2 : bv_unsigned (ew (Ereg regs fs_extraT) 2) = spZ regs)
  by (rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl); reflexivity).
apply (fsw_entryT_args B _ 128 ly S U W regs mem md ch _ fs_uar_regions [] HGOT HCELL HPRE).
- lia.
- vm_compute. reflexivity.
- exact (fsw_uar_regions_ok B _ ly S U W regs mem md ch _ HGUAR HUCELL HPRE).
- apply pairwise_disjoint_of_extents.
  unfold fsT_regions_args, fsT_regions, fs_uar_regions, fs_got_uar_region, fs_uar_cell_region, fs_got_region,
    fs_bcell_region, fstk, extent_of_region.
  cbn [app map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, fs_D_GOT_uar,
    fs_D_uar_cell.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia].
- exact I.
Qed.

(* segment 0: the prologue, the re-align and the flag test, up to the call of __asan_stack_malloc_0 *)
Lemma crcs_seg0 : forall ly S U (W : world tfibsegs) regs mem md ch FP (Q : world tfibsegs -> config -> Prop),
  afn_preU tfibsegs B STK_check_reject_clean_starved ly S U W regs mem md ch ->
  (forall ms mat,
     st_ok tfibsegs (Ereg regs fs_extraT) crcs_ss1 (restrict (w_H W) ms) ->
     @ajournal rc SK tfibsegs B STK_check_reject_clean_starved (spZ regs) FP ly S W (unpoison U mem) md [] ly S W
       (unpoison U (ms_mem ms)) (with_vm_backing (m_vm_lazy md) mat md) 0 ->
     ARU tfibsegs B ly S U W (ms_mem ms) (with_vm_backing (m_vm_lazy md) mat md) ->
     frame_of (Ereg regs fs_extraT) (ss_mem crcs_ss0) mem (ms_mem ms) ->
     frame_of (Ereg regs fs_extraT) (ss_mem crcs_ss0) (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms)) ->
     SRr tfibsegs W (mkCfg ms (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
  SRr tfibsegs W (cfg_at tfibsegs A_check_reject_clean_starved regs mem md) Q.
Proof.
intros ly S U W regs mem md ch FP Q HPRE K.
pose proof (fsw_sp B _ ly S U W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _). pose proof crcs_stk as FS.
pose proof (crcs_entry ly S U W regs mem md ch HPRE) as HS.
pose proof (fsw_ARU B _ ly S U W regs mem md ch HPRE) as HARU.
pose proof (ajournal_init tfibsegs B STK_check_reject_clean_starved FP ly S W regs (unpoison U mem) md ch (proj1 HPRE))
  as HJ.
assert (Usp : bv_unsigned (ew (Ereg regs fs_extraT) 2) = spZ regs)
  by (rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl); reflexivity).
unfold cfg_at. change (w64 A_check_reject_clean_starved) with (Z_to_bv 64 A_check_reject_clean_starved).
fsw_aj_run_toU crcs_tbl_ok HS HJ HARU PC_stack_malloc_0.
{ awr_ok_tac. exact Usp. }
exact (K _ _ HS HJ HARU HF HFr).
Qed.

(* the registers at the call of __asan_stack_malloc_0 (read off crcs_ss1): sp = s1 = the re-aligned sp1 (the frame
   drop 0x80, then down to 32), a0 = 64 (class 0), ra = 0x826e4, gp / tp kept, s0 = the entry sp, s3 / s4 / s5 = the
   entry a2 / a1 / a0 (l, bd, t), s8 = the shadow base *)
Lemma crcs_sm_site : forall ly S U (W : world tfibsegs) regs mem md ch ms,
  afn_preU tfibsegs B STK_check_reject_clean_starved ly S U W regs mem md ch ->
  st_ok tfibsegs (Ereg regs fs_extraT) crcs_ss1 (restrict (w_H W) ms) ->
  YK11.getr (ms_regs ms) 2%bv = Z_to_bv 64 (32 * ((spZ regs - 128) / 32)) /\
  YK11.getr (ms_regs ms) 9%bv = Z_to_bv 64 (32 * ((spZ regs - 128) / 32)) /\
  spZ regs - 144 <= 32 * ((spZ regs - 128) / 32) <= spZ regs - 128 /\ (32 * ((spZ regs - 128) / 32)) mod 32 = 0 /\
  YK11.getr (ms_regs ms) 1%bv = Z_to_bv 64 0x826e4 /\ YK11.getr (ms_regs ms) 10%bv = Z_to_bv 64 64 /\
  YK11.getr (ms_regs ms) 3%bv = YK11.getr regs 3%bv /\ YK11.getr (ms_regs ms) 4%bv = YK11.getr regs 4%bv /\
  YK11.getr (ms_regs ms) 8%bv = YK11.getr regs 2%bv /\ YK11.getr (ms_regs ms) 24%bv = Z_to_bv 64 SHADOW_OFF /\
  YK11.getr (ms_regs ms) 19%bv = YK11.getr regs 12%bv /\ YK11.getr (ms_regs ms) 20%bv = YK11.getr regs 11%bv /\
  YK11.getr (ms_regs ms) 21%bv = YK11.getr regs 10%bv.
Proof.
intros ly S U W regs mem md ch ms HPRE HS.
pose proof (fsw_sp B _ ly S U W regs mem md ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _). pose proof crcs_stk as FS.
set (E := Ereg regs fs_extraT) in *.
assert (E2 : ew E 2 = Z_to_bv 64 (spZ regs)) by (subst E; rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl);
  unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
pose proof (fsw_realign_facts (spZ regs - 128) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity)) as (F1 & F2 & F3).
set (sp1 := 32 * ((spZ regs - 128) / 32)) in *.
assert (R2 : YK11.getr (ms_regs ms) 2%bv = Z_to_bv 64 sp1).
{ exact (fsw_realign_val E crcs_ss1 (restrict (w_H W) ms) 2%bv 2 (-128) (spZ regs) HS
    ltac:(vm_compute; reflexivity) E2 ltac:(unfold spZ; apply u64_range) ltac:(lia)). }
assert (R9 : YK11.getr (ms_regs ms) 9%bv = Z_to_bv 64 sp1).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E crcs_ss1 ms 9%bv HS).
  lazymatch goal with |- _ = Z_to_bv 64 ?v => change (sr_get (ss_regs crcs_ss1) 9%bv) with
    (SAlu ALU_ADD (SAlu ALU_AND (SOff 2 (-128)) (SLit (-32))) (SLit 0)) end.
  rewrite denot_lit_U, U_SAlu. f_equal. cbn [zalu_raw]. rewrite U_SLit.
  assert (UA : YP0e.U E (SAlu ALU_AND (SOff 2 (-128)) (SLit (-32))) = sp1).
  { unfold YP0e.U. rewrite (denot_and_m32 E 2 (spZ regs) (-128) E2 ltac:(lia) ltac:(lia) ltac:(unfold spZ; apply u64_range)).
    apply wz. lia. }
  rewrite UA. change (zcanon 0) with 0. rewrite Z.add_0_r. apply zcanon_id. unfold M64. lia. }
split; [exact R2|]. split; [exact R9|]. split; [lia|]. split; [exact F2|].
split; [exact (fsw_reg_lit _ E _ ms 1%bv 0x826e4 HS ltac:(vm_compute; reflexivity) ltac:(lia))|].
split; [exact (fsw_reg_lit _ E _ ms 10%bv 64 HS ltac:(vm_compute; reflexivity) ltac:(lia))|].
split; [exact (fsw_reg_atom _ regs fs_extraT _ ms 3%bv 3%bv 3 HS ltac:(vm_compute; reflexivity) eq_refl)|].
split; [exact (fsw_reg_atom _ regs fs_extraT _ ms 4%bv 4%bv 4 HS ltac:(vm_compute; reflexivity) eq_refl)|].
split; [exact (fsw_reg_atom _ regs fs_extraT _ ms 8%bv 2%bv 2 HS ltac:(vm_compute; reflexivity) eq_refl)|].
split.
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) E crcs_ss1 ms 24%bv HS).
  change (sr_get (ss_regs crcs_ss1) 24%bv) with (SOff 32 0). rewrite fsw_SOff0.
  subst E. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity. }
split; [exact (fsw_reg_atom _ regs fs_extraT _ ms 19%bv 12%bv 12 HS ltac:(vm_compute; reflexivity) eq_refl)|].
split; [exact (fsw_reg_atom _ regs fs_extraT _ ms 20%bv 11%bv 11 HS ltac:(vm_compute; reflexivity) eq_refl)|].
exact (fsw_reg_atom _ regs fs_extraT _ ms 21%bv 10%bv 10 HS ltac:(vm_compute; reflexivity) eq_refl).
Qed.

(* the twelve saved words of the prologue, read off crcs_ss1's frame region (atom 2 = the entry sp) and restated over
   any environment whose atoms 33..44 are the entry's ra, s0, s1, s2..s10 (crcs_extra) *)
Lemma crcs_sv_init : forall (W : world tfibsegs) regs ms E2,
  st_ok tfibsegs (Ereg regs fs_extraT) crcs_ss1 (restrict (w_H W) ms) ->
  (forall n, (33 <= n < 45)%nat -> ew E2 n = nth (n - 32) (crcs_extra regs 0) (Z_to_bv 64 0)) ->
  Forall (YP09.chunk_ok tfibsegs E2 (mrestrict (w_H W) (ms_mem ms)) (spZ regs)) crcs_sv_chunks.
Proof.
intros W regs ms E2 HS HE.
set (E := Ereg regs fs_extraT) in *.
pose proof (fsw_region_nth E crcs_ss1 (restrict (w_H W) ms) 0 (nth 0 (ss_mem crcs_ss1) (fs_ret_s0_region 0 0 [])) HS eq_refl)
  as (_ & _ & _ & Hcs).
cbn [ss_mem crcs_ss1 nth YP09.r_chunks YP09.r_base base_val ms_mem restrict] in Hcs.
assert (E2b : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl); reflexivity).
rewrite E2b in Hcs.
repeat match type of Hcs with Forall _ (_ :: _) => let h := fresh "Hc" in apply Forall_cons_iff in Hcs as [h Hcs] end.
unfold crcs_sv_chunks.
repeat (apply Forall_cons;
  [ match goal with
    | h : YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o (CVal _ _)) |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o _) =>
        apply (crcs_chunk_conv _ _ _ _ _ _ _ _ h); rewrite !fsw_SOff0;
        match goal with |- _ = ew E2 ?n => rewrite (HE n ltac:(lia)) end;
        subst E; match goal with |- ew _ ?m = _ => rewrite (ew_Ereg_nat regs fs_extraT m (Z_to_bv 5 (Z.of_nat m)) ltac:(reflexivity)) end;
        reflexivity
    end |]).
apply Forall_nil.
Qed.

(* ---- one program call of a fake-frame caller: the callee's fpostU, composed by fsw_after_callU_s0_own into the
   caller's journal, and the after-call state at the return address r (the saved words at s0 - 96 .. s0 - 8) ---- *)
Lemma crcs_call : forall STK sp0 FP ly S U W0 mem0 md0 own lyc Sc (W : world tfibsegs) ms mdC k E ss STKc FPc kc
    (Qc : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
    (Q : world tfibsegs -> config -> Prop) extra r,
  st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  @ajournal rc SK tfibsegs B STK sp0 FP ly S W0 (unpoison U mem0) md0 own lyc Sc W (unpoison U (ms_mem ms)) mdC k ->
  ARU tfibsegs B lyc Sc U W (ms_mem ms) mdC ->
  SRr tfibsegs W (cfg_at tfibsegs (ss_pc ss) (ms_regs ms) (ms_mem ms) mdC)
    (@fpostU fx rc SK tfibsegs B STKc (spZ (ms_regs ms)) FPc (ms_regs ms) lyc Sc U W (ms_mem ms) mdC kc U Qc) ->
  (forall a, inFP FPc a ->
     (inFP FP a /\ exists b n, In (b, n) (ablocks B lyc Sc) /\ b <= a < b + req_size n)
     \/ in_tmp_block (ablocks B ly S) (ablocks B lyc Sc) a
     \/ (inFP FP a /\ in_img tfibsegs a)
     \/ in_frames lyc own a) ->
  getr (ms_regs ms) 1 = Z_to_bv 64 r -> getr (ms_regs ms) 8 = Z_to_bv 64 sp0 ->
  sp0 - STK <= spZ (ms_regs ms) - STKc -> spZ (ms_regs ms) <= sp0 - 96 -> sp0 - STK <= sp0 - 96 ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms)) sp0) crcs_sv_chunks ->
  (forall n, (33 <= n < 45)%nat -> ew E n = nth (n - 32) extra (Z_to_bv 64 0)) ->
  (forall ly' S' W' regs' mem' md',
     Qc ly' S' W' regs' mem' md' -> aregs_preserved (ms_regs ms) regs' ->
     @ajournal rc SK tfibsegs B STKc (spZ (ms_regs ms)) FPc lyc Sc W (unpoison U (ms_mem ms)) mdC [] ly' S' W'
       (unpoison U mem') md' kc ->
     @ajournal rc SK tfibsegs B STK sp0 FP ly S W0 (unpoison U mem0) md0 own ly' S' W' (unpoison U mem') md' (k + kc) ->
     ARU tfibsegs B ly' S' U W' mem' md' ->
     st_ok tfibsegs (Ereg regs' extra) (fss_ret_s0 r (-96) 0 crcs_sv_chunks)
       (restrict (w_H W') (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))) ->
     SRr tfibsegs W' (mkCfg (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs)) md') Q) ->
  SRr tfibsegs W (mkCfg ms mdC) Q.
Proof.
intros STK sp0 FP ly S U W0 mem0 md0 own lyc Sc W ms mdC k E ss STKc FPc kc Qc Q extra r HS Hrv HJ HARU HSPEC HFP Hra
  Hs0 Hw1 Hw2 Hw3 Hcs Hext K.
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E ss ms HS Hrv).
eapply SRr_bind; [exact HSPEC|].
intros W' c' _ (ly' & S' & regs' & mem' & md' & -> & HJc & OK' & PO' & HP & HQc).
rewrite Hra.
assert (Hs0' : YK11.getr regs' 8%bv = Z_to_bv 64 sp0).
{ rewrite (fsw_pres (ms_regs ms) regs' 8%bv HP ltac:(crcs_cs)). exact Hs0. }
assert (Hcs' : Forall (YP09.chunk_ok tfibsegs (Ereg regs' extra) (mrestrict (w_H W) (ms_mem ms)) sp0) crcs_sv_chunks).
{ apply (crcs_sv_conv E (Ereg regs' extra) _ _); [|exact Hcs].
  intros n Hn. rewrite (Hext n Hn), crcs_ew_extra by lia. reflexivity. }
assert (Hin : Forall (fun c => -96 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= 0) crcs_sv_chunks).
{ unfold crcs_sv_chunks. repeat constructor; cbn; lia. }
destruct (fsw_after_callU_s0_own B STK sp0 FP ly S U W0 mem0 md0 own lyc Sc U W (ms_mem ms) mdC k STKc FPc
  (spZ (ms_regs ms)) (ms_regs ms) ly' S' U W' regs' mem' md' kc extra crcs_sv_chunks r (-96) 0 HJ HARU HJc OK' PO' HFP
  HP eq_refl Hs0' ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity) Hin Hcs')
  as [HJ2 HS2].
apply (K ly' S' W' regs' mem' md' HQc HP HJc HJ2); [|exact HS2].
split; [exact (proj1 HJ2) | split; [exact OK' | exact PO']].
Qed.

(* the call chain at a callee's entry: starved's record (its entry sp, the saved ra and s0) on top of its entry chain *)
Lemma crcs_chain_at : forall ly S U W0 mem0 md0 regs ch lyc Sc (W : world tfibsegs) memc mdc k own spc,
  achain ly (aview tfibsegs (w_H W0) (unpoison U mem0)) (spZ regs) (s0Z regs) ch -> spZ regs + 32 <= ly_top ly ->
  ARU tfibsegs B lyc Sc U W memc mdc ->
  @ajournal rc SK tfibsegs B STK_check_reject_clean_starved (spZ regs) FS_PSTAT_FP ly S W0 (unpoison U mem0) md0 own lyc Sc W
    (unpoison U memc) mdc k ->
  val_mem tfibsegs (mrestrict (w_H W) memc) (spZ regs - 8) 8 (raZ regs) ->
  val_mem tfibsegs (mrestrict (w_H W) memc) (spZ regs - 16) 8 (s0Z regs) ->
  4096 <= raZ regs -> spc + 16 <= spZ regs ->
  achain lyc (aview tfibsegs (w_H W) (unpoison U memc)) spc (spZ regs) ((spZ regs, raZ regs, s0Z regs) :: ch).
Proof.
intros ly S U W0 mem0 md0 regs ch lyc Sc W memc mdc k own spc Hch HTOP HARU HJ V8 V16 Hra Hspc.
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as (C1 & _ & C3 & _). pose proof crcs_stk as FS.
assert (Hc : achain lyc (aview tfibsegs (w_H W0) (unpoison U mem0)) (spZ regs) (s0Z regs) ch)
  by (unfold achain in *; rewrite Etop; exact Hch).
assert (Hal8 : spZ regs mod 8 = 0).
{ apply (Z.mod_divide _ 16 ltac:(lia)) in Hal16 as [q Hq]. rewrite Hq. replace (q * 16) with ((2 * q) * 8) by lia.
  apply Z.mod_mul. lia. }
refine (proj1 (crcs_chain lyc _ _ (spZ regs) (s0Z regs) ch (raZ regs) spc Hc _ _ _ _ _ Hra _ Hal8 Hspc)).
- rewrite Etop. lia.
- rewrite Etop. lia.
- intros a Ha. apply F1; lia.
- rewrite (rdword_ext (aview tfibsegs (w_H W) memc)).
  + apply YF0x.val_mem_rdword; [unfold raZ; apply u64_range | exact V8].
  + intros i Hi. apply (fsw_aview_unpoison_high B lyc Sc U W memc mdc _ HARU). lia.
- rewrite (rdword_ext (aview tfibsegs (w_H W) memc)).
  + apply YF0x.val_mem_rdword; [unfold s0Z; apply u64_range | exact V16].
  + intros i Hi. apply (fsw_aview_unpoison_high B lyc Sc U W memc mdc _ HARU). lia.
- lia.
Qed.

(* ---- glue of the walk ---- *)
(* image bytes are no user-poisoned shadow bytes (the twin of FSW_K's fsw_unpoison_high) *)
Lemma crcs_aview_low : forall ly S U (W : world tfibsegs) mem md a,
  ARU tfibsegs B ly S U W mem md -> 0 <= a < SHADOW_OFF ->
  aview tfibsegs (w_H W) (unpoison U mem) a = aview tfibsegs (w_H W) mem a.
Proof.
intros ly S U W mem md a H Ha. apply (aview_at tfibsegs). apply unpoison_out. rewrite (wz a ltac:(unfold SHADOW_OFF in Ha; lia)).
destruct (in_ush U a) eqn:E; [|reflexivity]. exfalso.
assert (UF : aowned B ly S a /\ SHADOW_OFF <= a < kHighMemBeg) by (eapply ush_facts; eassumption). lia.
Qed.
Lemma crcs_aro_unp : forall ly S U (W : world tfibsegs) mem md, ARU tfibsegs B ly S U W mem md ->
  (arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) mem) <->
   arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) (unpoison U mem))).
Proof.
intros ly S U W mem md H. pose proof asan_consts as (C1 & _).
split; intros HR a Ha Ho He; pose proof (fs_segs_img a (crcs_roP_img a Ha)) as Hb; unfold FS_IMG_END in Hb;
  [rewrite (crcs_aview_low ly S U W mem md a H ltac:(unfold SHADOW_OFF; lia)) | rewrite <- (crcs_aview_low ly S U W mem md a H ltac:(unfold SHADOW_OFF; lia))];
  exact (HR a Ha Ho He).
Qed.
(* fs_glob through any change that keeps the four cells' bytes *)
Lemma crcs_glob_aview : forall (W W' : world tfibsegs) m m' live peak cnt fail,
  (forall a, inFP FS_PSTAT_FP a -> aview tfibsegs (w_H W') m' a = aview tfibsegs (w_H W) m a) ->
  fs_glob tfibsegs W m live peak cnt fail -> fs_glob tfibsegs W' m' live peak cnt fail.
Proof.
intros W W' m m' live peak cnt fail Hk (G1 & G2 & G3 & G4 & R).
assert (VB : forall g v, In (g, g + 8) FS_PSTAT_FP ->
  val_mem tfibsegs (mrestrict (w_H W) m) g 8 v -> val_mem tfibsegs (mrestrict (w_H W') m') g 8 v).
{ intros g v Hg Hv k Hkk.
  rewrite (mbyte_of_aview tfibsegs (w_H W) (w_H W') m m' (g + Z.of_nat k)
    (Hk _ (inFP_FS_PSTAT_FP g Hg (g + Z.of_nat k) ltac:(lia)))).
  exact (Hv k Hkk). }
unfold fs_glob, fs_glob_at in *.
split; [apply VB; [right; left; reflexivity | exact G1]|]. split; [apply VB; [right; right; left; reflexivity | exact G2]|].
split; [apply VB; [right; right; right; left; reflexivity | exact G3]|]. split; [apply VB; [left; reflexivity | exact G4]|].
exact R.
Qed.
(* the cells after a RUNTIME call (acall_kept's image clause; IMG: not runtime-owned; HPST_ERRNO: not errno) *)
Lemma crcs_glob_acall : forall lyc Sc ly2 S2 U (W W' : world tfibsegs) m m' md md' slo shi live peak cnt fail,
  ARU tfibsegs B lyc Sc U W m md -> ARU tfibsegs B ly2 S2 U W' m' md' ->
  acall_kept tfibsegs B lyc Sc W (unpoison U m) W' (unpoison U m') slo shi (fun _ => False) ->
  fs_glob tfibsegs W m live peak cnt fail -> fs_glob tfibsegs W' m' live peak cnt fail.
Proof.
intros lyc Sc ly2 S2 U W W' m m' md md' slo shi live peak cnt fail H1 H2 (_ & _ & K3 & _) HG.
apply (crcs_glob_aview W W' m m'); [|exact HG].
intros a Ha. pose proof (crcs_pstat_img a Ha) as Hi. pose proof (fs_segs_img a Hi) as Hb. unfold FS_IMG_END in Hb.
rewrite <- (crcs_aview_low ly2 S2 U W' m' md' a H2 ltac:(unfold SHADOW_OFF; lia)),
  <- (crcs_aview_low lyc Sc U W m md a H1 ltac:(unfold SHADOW_OFF; lia)).
exact (K3 a Hi (fs_pstat_not_owned tfibsegs B _ _ _ _ _ _ _ IMG a Ha) (HPST_ERRNO a Ha)).
Qed.
(* the bytes of starved's fake frame and its shadow are bytes of its own frame list *)
Lemma crcs_in_fr : forall ly pos a, frame_addr ly 0 pos <= a < frame_addr ly 0 pos + 64 -> in_frames ly [(0, pos)] a.
Proof. intros ly pos a Ha. exists 0, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. exact Ha. Qed.
Lemma crcs_in_sh : forall ly pos a, shadow_addr (frame_addr ly 0 pos) <= a < shadow_addr (frame_addr ly 0 pos) + 8 ->
  in_frames ly [(0, pos)] a.
Proof. intros ly pos a Ha. exists 0, pos. split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd]. exact Ha. Qed.

(* the state after a program call with the fake frame and its shadow put back (FSW_frame.v fsw_readd_frame_regions) *)
Lemma crcs_readd : forall ly S U (W : world tfibsegs) md regs' mem' extra r fcs pos sp0,
  ARU tfibsegs B ly S U W mem' md -> In (0, pos) (frames S) ->
  st_ok tfibsegs (Ereg regs' extra) (fss_ret_s0 r (-96) 0 crcs_sv_chunks)
    (restrict (w_H W) (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))) ->
  getr regs' 25 = Z_to_bv 64 (frame_addr ly 0 pos) ->
  getr regs' 24 = Z_to_bv 64 (shadow_addr (frame_addr ly 0 pos)) ->
  getr regs' 8 = Z_to_bv 64 sp0 -> alloc_ceiling <= sp0 - 96 -> sp0 <= 2 ^ 47 ->
  YP09.region_wf (YP09.mkRegion (Some 25%nat) 0 64 0 64 fcs) = true ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs' extra) (mrestrict (w_H W) mem') (frame_addr ly 0 pos)) fcs ->
  st_ok tfibsegs (Ereg regs' extra) (crcs_fs r fcs)
    (restrict (w_H W) (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))).
Proof.
intros ly S U W md regs' mem' extra r fcs pos sp0 HARU Hin HS R25 R24 R8 Hsp Hsp47 Hwf Hfcs.
pose proof (ARU_AR tfibsegs B ly S U W mem' md HARU) as HAR.
destruct (frames_bounds tfibsegs B LAWS ly S W (unpoison U mem') md 0 pos HAR Hin) as (H4096 & Hceil & Happ).
change (fs_frame_bytes 0) with 64 in *.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (F := frame_addr ly 0 pos) in *.
pose proof (Z.mul_div_le F 8 ltac:(lia)) as Hd8. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)) as Hd0.
assert (E25 : bv_unsigned (ew (Ereg regs' extra) 25) = F)
  by (rewrite (ew_Ereg_nat regs' extra 25 25%bv eq_refl), R25; apply unsigned_lit_small; lia).
assert (E24 : bv_unsigned (ew (Ereg regs' extra) 24) = shadow_addr F)
  by (rewrite (ew_Ereg_nat regs' extra 24 24%bv eq_refl), R24; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia).
assert (E8 : bv_unsigned (ew (Ereg regs' extra) 8) = sp0)
  by (rewrite (ew_Ereg_nat regs' extra 8 8%bv eq_refl), R8; apply unsigned_lit_small; lia).
unfold in_app, kLowShadowBeg, ASAN_CEIL in Happ.
apply (fsw_readd_frame_regions B ly S U W md (Ereg regs' extra) (fss_ret_s0 r (-96) 0 crcs_sv_chunks)
  (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs)) 0 pos 25 24 fcs HARU Hin ltac:(lia) HS E25 E24 Hwf
  ltac:(vm_compute; reflexivity) Hfcs).
- apply all_disjoint_of_extents. unfold fss_ret_s0, fs_ret_s0_region, extent_of_region.
  cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E8, E24.
  change (fs_frame_bytes 0 / 8) with 8. cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold shadow_addr, SHADOW_OFF. repeat split; try exact I; lia.
- apply all_disjoint_of_extents. unfold fss_ret_s0, fs_ret_s0_region, extent_of_region.
  cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E8, E24, E25.
  change (fs_frame_bytes 0 / 8) with 8. change (fs_frame_bytes 0) with 64. cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
  unfold shadow_addr, SHADOW_OFF. repeat split; try exact I; lia.
Qed.
(* the saved words read off a state's s0 region *)
Lemma crcs_sv_at : forall E ss (H : word -> bool) ms i sp0,
  st_ok tfibsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some (fs_ret_s0_region (-96) 0 crcs_sv_chunks) ->
  bv_unsigned (ew E 8) = sp0 -> Forall (YP09.chunk_ok tfibsegs E (mrestrict H (ms_mem ms)) sp0) crcs_sv_chunks.
Proof.
intros E ss H ms i sp0 HS Hi E8. pose proof (fsw_region_nth E ss (restrict H ms) i _ HS Hi) as (_ & _ & _ & Hcs).
cbn [fs_ret_s0_region YP09.r_base YP09.r_chunks base_val ms_mem restrict] in Hcs. rewrite E8 in Hcs. exact Hcs.
Qed.
(* the saved ra and s0 among them *)
Lemma crcs_sv_ra : forall E m sp0 v1 v2, Forall (YP09.chunk_ok tfibsegs E m sp0) crcs_sv_chunks ->
  sv_denot E (SOff 33 0) = Z_to_bv 64 v1 -> 0 <= v1 < 2 ^ 64 ->
  sv_denot E (SOff 34 0) = Z_to_bv 64 v2 -> 0 <= v2 < 2 ^ 64 ->
  val_mem tfibsegs m (sp0 - 8) 8 v1 /\ val_mem tfibsegs m (sp0 - 16) 8 v2.
Proof.
intros E m sp0 v1 v2 HF H1 R1 H2 R2. unfold crcs_sv_chunks in HF.
apply Forall_cons_iff in HF as [C1 HF]. apply Forall_cons_iff in HF as [C2 _].
split.
- replace (sp0 - 8) with (sp0 + -8) by lia.
  exact (val_of_chunk_ok tfibsegs E m sp0 (-8) 8 _ v1 C1 H1 ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)).
- replace (sp0 - 16) with (sp0 + -16) by lia.
  exact (val_of_chunk_ok tfibsegs E m sp0 (-16) 8 _ v2 C2 H2 ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(cbn; lia)).
Qed.

(* ---- one engine run from an after-call state (crcs_fsS r fcs scs, possibly with a branch condition added: same
   memory) to the next stop: the run writes only the fake frame, its shadow (bytes of starved's own frame) and the
   saved words' window (its stack), so the image is unchanged ---- *)
Lemma crcs_seg : forall ly S U W0 mem0 md0 pos lyc Sc (Wc : world tfibsegs) regsP memP mdP k ext sp0 r fcs scs ss stop ssC
    stC (Q : world tfibsegs -> config -> Prop),
  st_ok tfibsegs (Ereg regsP ext) ss (restrict (w_H Wc) (mkst regsP (Z_to_bv 64 r) memP (seg_rom tfibsegs))) ->
  ss_mem ss = ss_mem (crcs_fsS r fcs scs) ->
  @ajournal rc SK tfibsegs B STK_check_reject_clean_starved sp0 FS_PSTAT_FP ly S W0 (unpoison U mem0) md0 [(0, pos)] lyc Sc Wc
    (unpoison U memP) mdP k ->
  ARU tfibsegs B lyc Sc U Wc memP mdP ->
  getr regsP 8 = Z_to_bv 64 sp0 -> getr regsP 25 = Z_to_bv 64 (frame_addr lyc 0 pos) ->
  getr regsP 24 = Z_to_bv 64 (shadow_addr (frame_addr lyc 0 pos)) ->
  sym_run_toN tfibsegs crcs_tbl FUEL stop ss = (ssC, stC) ->
  match stC with RS_ecall => False | _ => True end ->
  (forall msC matC,
     st_ok tfibsegs (Ereg regsP ext) ssC (restrict (w_H Wc) msC) ->
     @ajournal rc SK tfibsegs B STK_check_reject_clean_starved sp0 FS_PSTAT_FP ly S W0 (unpoison U mem0) md0 [(0, pos)] lyc Sc Wc
       (unpoison U (ms_mem msC)) (with_vm_backing (m_vm_lazy mdP) matC mdP) k ->
     ARU tfibsegs B lyc Sc U Wc (ms_mem msC) (with_vm_backing (m_vm_lazy mdP) matC mdP) ->
     (forall a, in_img tfibsegs a -> ms_mem msC (Z_to_bv 64 a) = memP (Z_to_bv 64 a)) ->
     SRr tfibsegs Wc (mkCfg msC (with_vm_backing (m_vm_lazy mdP) matC mdP)) Q) ->
  SRr tfibsegs Wc (mkCfg (mkst regsP (Z_to_bv 64 r) memP (seg_rom tfibsegs)) mdP) Q.
Proof.
intros ly S U W0 mem0 md0 pos lyc Sc Wc regsP memP mdP k ext sp0 r fcs scs ss stop ssC stC Q HS Hmem HJ HARU R8 R25 R24
  Hrun Hst K.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof crcs_stk as FS.
assert (Hin : In (0, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds tfibsegs B LAWS lyc Sc Wc (unpoison U memP) mdP 0 pos HAR Hin) as (H4096 & HFc & HFapp).
change (fs_frame_bytes 0) with 64 in *.
set (F := frame_addr lyc 0 pos) in *.
pose proof (Z.mul_div_le F 8 ltac:(lia)) as Hd8. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)) as Hd0.
assert (E25 : bv_unsigned (ew (Ereg regsP ext) 25) = F)
  by (rewrite (ew_Ereg_nat regsP ext 25 25%bv eq_refl), R25; apply unsigned_lit_small; lia).
assert (E24 : bv_unsigned (ew (Ereg regsP ext) 24) = shadow_addr F)
  by (rewrite (ew_Ereg_nat regsP ext 24 24%bv eq_refl), R24; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia).
assert (E8 : bv_unsigned (ew (Ereg regsP ext) 8) = sp0)
  by (rewrite (ew_Ereg_nat regsP ext 8 8%bv eq_refl), R8; apply unsigned_lit_small; lia).
assert (NIF : forall a, F <= a < F + 64 -> ~ in_img tfibsegs a).
{ intros a Ha. exact (proj2 (al_client_img _ _ LAWS lyc Sc Wc (unpoison U memP) mdP a HAR
    (or_intror (or_introl (ex_intro _ 0 (ex_intro _ pos (conj Hin Ha))))))). }
assert (NIH : forall a, FS_IMG_END <= a -> ~ in_img tfibsegs a) by (intros a Ha Hi; pose proof (fs_segs_img a Hi); lia).
eapply (fsw_run_to_AJU B crcs_tbl crcs_tbl_ok Wc FUEL stop _ _ ssC stC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS Hrun Hst HARU HJ).
- rewrite Hmem. unfold crcs_fsS. cbn [ss_mem].
  eapply awr_ok_cons_gen; [reflexivity | exact E25 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. left; right; right; right. apply crcs_in_fr. lia. }
  eapply awr_ok_cons_gen; [reflexivity | exact E24 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. left; right; right; right. apply crcs_in_sh. fold F. lia. }
  eapply awr_ok_cons_stack; [reflexivity | exact E8 | cbn [fs_ret_s0_region YP09.r_wlo]; lia | cbn [fs_ret_s0_region YP09.r_whi]; lia |].
  apply awr_ok_nil.
- intros msC matC HSC HJC HARUC HFC _ _. apply (K msC matC HSC HJC HARUC).
  cbn [ms_mem mkst] in HFC. apply (crcs_img_keep _ _ _ _ HFC).
  intros a (rg & Hr & Ha). rewrite Hmem in Hr. unfold crcs_fsS in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<-|[<-|[<-|[]]]]; cbn [fs_ret_s0_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  + apply NIF. rewrite E25 in Ha. lia.
  + apply NIH. rewrite E24 in Ha. unfold FS_IMG_END. unfold shadow_addr, SHADOW_OFF in Ha. lia.
  + apply NIH. rewrite E8 in Ha. unfold FS_IMG_END. lia.
Qed.

(* ---- the facts at a program call reached from an after-call state: the callee's fpreU and crcs_call's register,
   window and saved-word premises ---- *)
Lemma crcs_site : forall ly S U W0 mem0 md0 regs0 ch pos FL lyc Sc (Wc : world tfibsegs) regsP msC mdC k ssC ra sp1 STKc,
  afn_preU tfibsegs B STK_check_reject_clean_starved ly S U W0 regs0 mem0 md0 ch -> spZ regs0 + 32 <= ly_top ly ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W0) mem0) ->
  st_ok tfibsegs (Ereg regsP (crcs_extra regs0 FL)) ssC (restrict (w_H Wc) msC) ->
  sr_get (ss_regs ssC) 1%bv = SLit ra -> sr_get (ss_regs ssC) 2%bv = SOff 2 0 -> sr_get (ss_regs ssC) 3%bv = SOff 3 0 ->
  sr_get (ss_regs ssC) 4%bv = SOff 4 0 -> sr_get (ss_regs ssC) 8%bv = SOff 8 0 ->
  nth_error (ss_mem ssC) 2 = Some (fs_ret_s0_region (-96) 0 crcs_sv_chunks) ->
  getr regsP 2%bv = Z_to_bv 64 sp1 -> getr regsP 3%bv = getr regs0 3%bv -> getr regsP 4%bv = getr regs0 4%bv ->
  getr regsP 8%bv = Z_to_bv 64 (spZ regs0) ->
  spZ regs0 - 144 <= sp1 <= spZ regs0 - 128 -> (sp1 - spZ regs0) mod 16 = 0 ->
  4096 <= ra < 2 ^ 64 -> YK0s.ret_ok (Z_to_bv 64 ra) -> 0 <= STKc -> STKc + 144 <= STK_check_reject_clean_starved ->
  @ajournal rc SK tfibsegs B STK_check_reject_clean_starved (spZ regs0) FS_PSTAT_FP ly S W0 (unpoison U mem0) md0 [(0, pos)] lyc Sc
    Wc (unpoison U (ms_mem msC)) mdC k ->
  ARU tfibsegs B lyc Sc U Wc (ms_mem msC) mdC ->
  fpreU tfibsegs B STKc lyc Sc U Wc (ms_regs msC) (ms_mem msC) mdC ((spZ regs0, raZ regs0, s0Z regs0) :: ch) /\
  getr (ms_regs msC) 1 = Z_to_bv 64 ra /\ getr (ms_regs msC) 8 = Z_to_bv 64 (spZ regs0) /\ spZ (ms_regs msC) = sp1 /\
  Forall (YP09.chunk_ok tfibsegs (Ereg regsP (crcs_extra regs0 FL)) (mrestrict (w_H Wc) (ms_mem msC)) (spZ regs0))
    crcs_sv_chunks /\
  (forall n, (33 <= n < 45)%nat -> ew (Ereg regsP (crcs_extra regs0 FL)) n = nth (n - 32) (crcs_extra regs0 FL) (Z_to_bv 64 0)).
Proof.
intros ly S U W0 mem0 md0 regs0 ch pos FL lyc Sc Wc regsP msC mdC k ssC ra sp1 STKc HPRE HTOP HRO0 HS S1 S2 S3 S4 S8 Hs0
  P2 P3 P4 P8 Hsp1 Hm16 Hra Hret HSTK0 HSTK HJ HARU.
pose proof (fsw_sp B _ ly S U W0 regs0 mem0 md0 ch HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof (fsw_ARU B _ ly S U W0 regs0 mem0 md0 ch HPRE) as HARU0.
pose proof HPRE as ((HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0) & OK0 & PO0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof crcs_stk as FS.
set (E := Ereg regsP (crcs_extra regs0 FL)) in *.
assert (R2 : getr (ms_regs msC) 2%bv = Z_to_bv 64 sp1).
{ rewrite (st_ok_restrict_reg tfibsegs _ _ _ _ 2%bv HS), S2, fsw_SOff0. subst E. rewrite (ew_Ereg_nat regsP _ 2 2%bv eq_refl). exact P2. }
assert (R8 : getr (ms_regs msC) 8%bv = Z_to_bv 64 (spZ regs0)).
{ rewrite (st_ok_restrict_reg tfibsegs _ _ _ _ 8%bv HS), S8, fsw_SOff0. subst E. rewrite (ew_Ereg_nat regsP _ 8 8%bv eq_refl). exact P8. }
assert (R3 : getr (ms_regs msC) 3%bv = getr regs0 3%bv).
{ rewrite (st_ok_restrict_reg tfibsegs _ _ _ _ 3%bv HS), S3, fsw_SOff0. subst E. rewrite (ew_Ereg_nat regsP _ 3 3%bv eq_refl). exact P3. }
assert (R4 : getr (ms_regs msC) 4%bv = getr regs0 4%bv).
{ rewrite (st_ok_restrict_reg tfibsegs _ _ _ _ 4%bv HS), S4, fsw_SOff0. subst E. rewrite (ew_Ereg_nat regsP _ 4 4%bv eq_refl). exact P4. }
assert (R1 : getr (ms_regs msC) 1%bv = Z_to_bv 64 ra) by exact (fsw_reg_lit (w_H Wc) E ssC msC 1%bv ra HS S1 ltac:(lia)).
assert (Hsp : spZ (ms_regs msC) = sp1) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
assert (E8 : bv_unsigned (ew E 8) = spZ regs0) by (subst E; rewrite (ew_Ereg_nat regsP _ 8 8%bv eq_refl), P8; apply unsigned_lit_small; lia).
assert (Cs : Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H Wc) (ms_mem msC)) (spZ regs0)) crcs_sv_chunks)
  by exact (crcs_sv_at E ssC (w_H Wc) msC 2 (spZ regs0) HS Hs0 E8).
assert (Ex : forall n, (33 <= n < 45)%nat -> ew E n = nth (n - 32) (crcs_extra regs0 FL) (Z_to_bv 64 0))
  by (intros n Hn; subst E; exact (crcs_ew_extra regsP _ n ltac:(lia))).
destruct (crcs_sv_ra E _ (spZ regs0) (raZ regs0) (s0Z regs0) Cs) as [V8 V16].
{ rewrite fsw_SOff0, (Ex 33%nat ltac:(lia)). unfold crcs_extra. cbn [nth Nat.sub]. unfold raZ. symmetry. apply Z_to_bv_bv_unsigned. }
{ apply u64_range. }
{ rewrite fsw_SOff0, (Ex 34%nat ltac:(lia)). unfold crcs_extra. cbn [nth Nat.sub]. unfold s0Z. symmetry. apply Z_to_bv_bv_unsigned. }
{ apply u64_range. }
split; [|split; [exact R1 | split; [exact R8 | split; [exact Hsp | split; [exact Cs | exact Ex]]]]].
apply (crcs_fpreU B _ (spZ regs0) FS_PSTAT_FP ly S U W0 mem0 md0 [(0, pos)] lyc Sc Wc (ms_mem msC) mdC k (ms_regs msC)
  STKc (sp1 - spZ regs0) _ HJ HARU).
- apply (proj2 (crcs_aro_unp lyc Sc U Wc (ms_mem msC) mdC HARU)).
  eapply crcs_arodata_j; [exact HJ|]. apply (proj1 (crcs_aro_unp ly S U W0 mem0 md0 HARU0)). exact HRO0.
- rewrite Hsp. lia.
- exact Hm16.
- lia.
- exact HSTK0.
- lia.
- rewrite R1. exact Hret.
- unfold raZ. rewrite R1, unsigned_lit_small by lia. lia.
- rewrite R3. exact Hgp0.
- rewrite R4. exact Htp0.
- replace (s0Z (ms_regs msC)) with (spZ regs0) by (unfold s0Z; rewrite R8; symmetry; apply unsigned_lit_small; lia).
  apply (crcs_chain_at ly S U W0 mem0 md0 regs0 ch lyc Sc Wc (ms_mem msC) mdC k [(0, pos)] (spZ (ms_regs msC)) Hch0 HTOP
    HARU HJ V8 V16 Hra40). rewrite Hsp. lia.
Qed.

(* a value the symbolic state holds in a region's chunk, on the machine's memory *)
Lemma crcs_val_at : forall E ss (H : word -> bool) ms i n lo hi wlo whi cs od w e v b,
  st_ok tfibsegs E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  In (YP09.mkChunk od (CVal w e)) cs -> bv_unsigned (ew E n) = b -> sv_denot E e = Z_to_bv 64 v ->
  0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 -> val_mem tfibsegs (mrestrict H (ms_mem ms)) (b + od) (N.to_nat w) v.
Proof.
intros E ss H ms i n lo hi wlo whi cs od w e v b HS Hi Hin Hb He Hv Hw.
exact (fsw_field E _ n b cs lo hi wlo whi od w e v (fsw_region_nth E ss (restrict H ms) i _ HS Hi) Hb Hin He Hv Hw).
Qed.

(* the callee-saved registers starved holds fixed from 0x82750 to its epilogue: sp = s1-realigned sp1, gp / tp, s0 = the
   entry sp, s2 = s9 = the frame, s4 = body, s7 = the frame + 32 (&n), s8 = the frame's shadow, s10 = -8, s11 *)
Definition crcs_csr (regs0 regsX : bvmap 5 word) (sp0 sp1 F : Z) : Prop :=
  getr regsX 2%bv = Z_to_bv 64 sp1 /\ getr regsX 3%bv = getr regs0 3%bv /\ getr regsX 4%bv = getr regs0 4%bv /\
  getr regsX 8%bv = Z_to_bv 64 sp0 /\ getr regsX 18%bv = Z_to_bv 64 F /\ getr regsX 20%bv = getr regs0 11%bv /\
  getr regsX 23%bv = Z_to_bv 64 (F + 32) /\ getr regsX 24%bv = Z_to_bv 64 (shadow_addr F) /\
  getr regsX 25%bv = Z_to_bv 64 F /\ getr regsX 26%bv = Z_to_bv 64 (2 ^ 64 - 8) /\ getr regsX 27%bv = getr regs0 27%bv.
Lemma crcs_csr_call : forall regs0 regsC regs' sp0 sp1 F,
  aregs_preserved regsC regs' -> crcs_csr regs0 regsC sp0 sp1 F -> crcs_csr regs0 regs' sp0 sp1 F.
Proof.
intros regs0 regsC regs' sp0 sp1 F HP (C2 & C3 & C4 & C8 & C18 & C20 & C23 & C24 & C25 & C26 & C27).
repeat split;
  match goal with |- getr regs' ?r = _ => rewrite (fsw_pres regsC regs' r HP ltac:(crcs_cs)); assumption end.
Qed.
Definition CRCS_CSR : list (bv 5) := [2%bv; 3%bv; 4%bv; 8%bv; 18%bv; 20%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv].
Lemma crcs_csr_run : forall (H : word -> bool) regs0 regsP extra ss ms sp0 sp1 F,
  st_ok tfibsegs (Ereg regsP extra) ss (restrict H ms) -> crcs_csr regs0 regsP sp0 sp1 F ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CRCS_CSR = true ->
  crcs_csr regs0 (ms_regs ms) sp0 sp1 F.
Proof.
intros H regs0 regsP extra ss ms sp0 sp1 F HS (C2 & C3 & C4 & C8 & C18 & C20 & C23 & C24 & C25 & C26 & C27) Hb.
assert (K : forall r : bv 5, In r CRCS_CSR -> getr (ms_regs ms) r = getr regsP r).
{ intros r Hr. pose proof (proj1 (forallb_forall _ _) Hb r Hr) as Hq. cbv beta in Hq. apply sv_eqb_eq in Hq.
  apply (fsw_reg_atom H regsP extra ss ms r r _ HS Hq). rewrite Z2Nat.id; [reflexivity | apply bv_unsigned_in_range]. }
unfold CRCS_CSR in K.
repeat split;
  match goal with |- getr (ms_regs ms) ?r = _ => rewrite (K r ltac:(cbn; tauto)); assumption end.
Qed.

(* the after-call state with the two frame words starved keeps from 0x82784 on: n at frame + 32 and the flag word *)
Definition crcs_fcs2 (v32 : Z) : list YP09.chunk :=
  [YP09.mkChunk 32 (CVal 8 (SLit v32)); YP09.mkChunk 56 (CVal 8 (SOff 45 0))].
Lemma crcs_readd2 : forall ly S U (W : world tfibsegs) md regs0 regs' mem' FL r pos sp0 v32,
  ARU tfibsegs B ly S U W mem' md -> In (0, pos) (frames S) ->
  st_ok tfibsegs (Ereg regs' (crcs_extra regs0 FL)) (fss_ret_s0 r (-96) 0 crcs_sv_chunks)
    (restrict (w_H W) (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))) ->
  getr regs' 25 = Z_to_bv 64 (frame_addr ly 0 pos) ->
  getr regs' 24 = Z_to_bv 64 (shadow_addr (frame_addr ly 0 pos)) ->
  getr regs' 8 = Z_to_bv 64 sp0 -> alloc_ceiling <= sp0 - 96 -> sp0 <= 2 ^ 47 -> 0 <= v32 < 2 ^ 64 -> 0 <= FL < 2 ^ 64 ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (frame_addr ly 0 pos + 32) 8 v32 ->
  val_mem tfibsegs (mrestrict (w_H W) mem') (frame_addr ly 0 pos + 56) 8 FL ->
  st_ok tfibsegs (Ereg regs' (crcs_extra regs0 FL)) (crcs_fs r (crcs_fcs2 v32))
    (restrict (w_H W) (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))).
Proof.
intros ly S U W md regs0 regs' mem' FL r pos sp0 v32 HARU Hin HS R25 R24 R8 Hsp Hsp47 Hv HFL V32 V56.
apply (crcs_readd ly S U W md regs' mem' _ r _ pos sp0 HARU Hin HS R25 R24 R8 Hsp Hsp47); [vm_compute; reflexivity|].
constructor; [|constructor; [|constructor]].
- apply (chunk_ok_val tfibsegs _ _ _ 32 8 (SLit v32) v32); [| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact V32].
  apply bv_eq. rewrite unsigned_lit_small by lia. change (bv_unsigned (sv_denot (Ereg regs' (crcs_extra regs0 FL)) (SLit v32)))
    with (YP0e.U (Ereg regs' (crcs_extra regs0 FL)) (SLit v32)). rewrite U_lit by lia. reflexivity.
- apply (chunk_ok_val tfibsegs _ _ _ 56 8 (SOff 45 0) FL); [| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact V56].
  change 45%nat with (32 + 13)%nat. rewrite fsw_SOff0, ew_Ereg_extra. reflexivity.
Qed.

(* a kept text (a live block, or a read-only table string / format) is no byte of a live fake frame *)
Lemma crcs_text_nf : forall lyc Sc U (W : world tfibsegs) mem md t tb cid pos,
  AR tfibsegs B lyc Sc W mem md -> arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) mem) ->
  cstr_kept B lyc Sc U t tb -> In (cid, pos) (frames Sc) ->
  forall x, t <= x < t + Z.of_nat (length tb) + 1 ->
  ~ (frame_addr lyc cid pos <= x < frame_addr lyc cid pos + fs_frame_bytes cid).
Proof.
intros lyc Sc U W mem md t tb cid pos HAR HRO Hk Hfr x Hx Hxf.
assert (NI : ~ in_img tfibsegs x).
{ exact (proj2 (al_client_img _ _ LAWS lyc Sc W mem md x HAR (or_intror (or_introl (ex_intro _ cid (ex_intro _ pos (conj Hfr Hxf))))))). }
assert (BLK : forall b m, In (b, m) (ablocks B lyc Sc) -> b <= x < b + m -> False).
{ intros b m Hb Hbx. pose proof (sep_block_frame tfibsegs B LAWS lyc Sc W mem md b m cid pos HAR Hb Hfr) as Hd.
  unfold zdisjoint, req_size in Hd. cbn [fst snd] in Hd. destruct (Z.eqb_spec m 0); lia. }
destruct (proj2 IMG lyc Sc W mem md HAR HRO) as (_ & _ & Hstrs & Hfmts).
destruct Hk as [(b & m & Hin & H1 & H2 & _) | [Hro | (ps & Hf & ->)]].
- exact (BLK b m Hin ltac:(lia)).
- destruct (proj2 (proj1 (Forall_forall _ _) Hstrs (t, tb) Hro)) as [(b & m & Hin & H1 & H2 & _) | HR];
    cbn [fst snd] in *.
  + exact (BLK b m Hin ltac:(lia)).
  + destruct (HR x ltac:(lia)) as (Hr & _). exact (NI (crcs_roP_img x Hr)).
- destruct (proj2 (Hfmts t ps Hf)) as [(b & m & Hin & H1 & H2 & _) | HR].
  + exact (BLK b m Hin ltac:(lia)).
  + destruct (HR x ltac:(lia)) as (Hr & _). exact (NI (crcs_roP_img x Hr)).
Qed.

(* bytes of a block live at both ends of a journal, outside its footprint, keep their machine value *)
Lemma crcs_block_keep : forall STK sp0 FP ly S U (W : world tfibsegs) mem md own ly' S' W' mem' md' k p n a w v,
  @ajournal rc SK tfibsegs B STK sp0 FP ly S W (unpoison U mem) md own ly' S' W' (unpoison U mem') md' k ->
  ARU tfibsegs B ly S U W mem md -> ARU tfibsegs B ly' S' U W' mem' md' ->
  In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') ->
  p <= a -> a + Z.of_nat w <= p + req_size n ->
  (forall x, a <= x < a + Z.of_nat w -> ~ inFP FP x) ->
  val_mem tfibsegs (mrestrict (w_H W) mem) a w v -> val_mem tfibsegs (mrestrict (w_H W') mem') a w v.
Proof.
intros STK sp0 FP ly S U W mem md own ly' S' W' mem' md' k p n a w v HJ HARU HARU' Hin Hin' Hlo Hhi HnFP HV j Hj.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FB & _).
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
pose proof (ARU_AR tfibsegs B ly' S' U W' mem' md' HARU') as HAR'.
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md p n HAR Hin) as (_ & H4096 & Hceil & _ & Hb & _).
destruct (al_blocks _ _ LAWS ly' S' W' (unpoison U mem') md' p n HAR' Hin') as (_ & _ & _ & _ & Hb' & _).
pose proof asan_consts as (C1 & _).
set (x := a + Z.of_nat j).
assert (Hx : p <= x < p + req_size n) by (subst x; lia).
assert (Hxr : 0 <= x < 2 ^ 64) by lia.
rewrite <- (HV j Hj). apply (mbyte_of_aview tfibsegs). fold x.
rewrite <- (aview_at tfibsegs (w_H W') (unpoison U mem') mem' x).
2:{ apply (fsw_unpoison_notowned B ly' S' U W' mem' md' x HARU' Hxr). exact (proj2 (Hb' x Hx)). }
replace x with (p + (x - p)) by lia.
rewrite (FB p n (x - p) Hin Hin' ltac:(lia) ltac:(apply HnFP; subst x; lia)).
replace (p + (x - p)) with x by lia.
apply (aview_at tfibsegs).
apply (fsw_unpoison_notowned B ly S U W mem md x HARU Hxr). exact (proj2 (Hb x Hx)).
Qed.
(* decode's text premise across starved's journal (footprint image statics only, blocks unchanged) *)
Lemma crcs_wsrc_keep : forall STK sp0 FP ly S U (W : world tfibsegs) mem md own ly' S' W' mem' md' k buf s bs,
  @ajournal rc SK tfibsegs B STK sp0 FP ly S W (unpoison U mem) md own ly' S' W' (unpoison U mem') md' k ->
  ARU tfibsegs B ly S U W mem md -> ARU tfibsegs B ly' S' U W' mem' md' ->
  ablocks B ly' S' = ablocks B ly S -> (forall a, inFP FP a -> in_img tfibsegs a) ->
  FSH_Fn_writer.wsrc_kept B tfibsegs ly S U W mem buf s bs -> FSH_Fn_writer.wsrc_kept B tfibsegs ly' S' U W' mem' buf s bs.
Proof.
intros STK sp0 FP ly S U W mem md own ly' S' W' mem' md' k buf s bs HJ HARU HARU' Eab HFPi
  [H0 | [(p & kk & Hp & (Hin & Hm & Hk & Hv) & H1 & H2) | [(p & kk & Hp & Hin & H1 & H2 & HU) | Hro]]].
- left. exact H0.
- right; left. exists p, kk. split; [exact Hp|]. split; [|split; assumption].
  split; [rewrite Eab; exact Hin|]. split; [exact Hm|]. split; [exact Hk|].
  pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
  assert (Hreq : req_size (kk + HEAD) = kk + HEAD).
  { unfold req_size. rewrite (proj2 (Z.eqb_neq (kk + HEAD) 0)) by (unfold HEAD; lia). reflexivity. }
  apply (crcs_block_keep STK sp0 FP ly S U W mem md own ly' S' W' mem' md' k (p - HEAD) (kk + HEAD) (p - HEAD) 8 kk
    HJ HARU HARU' Hin ltac:(rewrite Eab; exact Hin)); [lia | rewrite Hreq; unfold HEAD; lia | |exact Hv].
  intros x Hx Hf.
  assert (Hxb : p - HEAD <= x < p - HEAD + req_size (kk + HEAD)) by (rewrite Hreq; unfold HEAD in *; lia).
  apply (proj2 (al_client_img _ _ LAWS ly S W (unpoison U mem) md x HAR
    (or_introl (ex_intro _ (p - HEAD) (ex_intro _ (kk + HEAD) (conj Hin Hxb)))))).
  exact (HFPi x Hf).
- right; right; left. exists p, kk. split; [exact Hp|]. split; [rewrite Eab; exact Hin|]. repeat split; assumption.
- right; right; right. exact Hro.
Qed.
(* the decoded body: a live reader block's header and the bytes it holds, across starved's journal (blocks unchanged,
   footprint fuzz/alloc.c's image statics, which no block byte is) *)
Lemma crcs_rblock_keep : forall STK sp0 ly S U (W : world tfibsegs) mem md own ly' S' W' mem' md' k p n bs,
  @ajournal rc SK tfibsegs B STK sp0 FS_PSTAT_FP ly S W (unpoison U mem) md own ly' S' W' (unpoison U mem') md' k ->
  ARU tfibsegs B ly S U W mem md -> ARU tfibsegs B ly' S' U W' mem' md' -> ablocks B ly' S' = ablocks B ly S ->
  fs_rblock tfibsegs B ly S W mem p n -> Z.of_nat (length bs) <= n -> zbytes_at tfibsegs W mem p bs ->
  fs_rblock tfibsegs B ly' S' W' mem' p n /\ zbytes_at tfibsegs W' mem' p bs.
Proof.
intros STK sp0 ly S U W mem md own ly' S' W' mem' md' k p n bs HJ HARU HARU' Eab (Hin & Hm & Hn & Hv) Hlen Hz.
pose proof (ARU_AR tfibsegs B ly S U W mem md HARU) as HAR.
assert (Hin' : In (p - HEAD, n + HEAD) (ablocks B ly' S')) by (rewrite Eab; exact Hin).
assert (Hreq : req_size (n + HEAD) = n + HEAD).
{ unfold req_size. rewrite (proj2 (Z.eqb_neq (n + HEAD) 0)) by (unfold HEAD; lia). reflexivity. }
assert (NFP : forall x, p - HEAD <= x < p - HEAD + req_size (n + HEAD) -> ~ inFP FS_PSTAT_FP x).
{ intros x Hx Hf. apply (proj2 (al_client_img _ _ LAWS ly S W (unpoison U mem) md x HAR
    (or_introl (ex_intro _ (p - HEAD) (ex_intro _ (n + HEAD) (conj Hin Hx)))))).
  exact (crcs_pstat_img x Hf). }
split.
- split; [exact Hin'|]. split; [exact Hm|]. split; [exact Hn|].
  apply (crcs_block_keep STK sp0 FS_PSTAT_FP ly S U W mem md own ly' S' W' mem' md' k (p - HEAD) (n + HEAD) (p - HEAD) 8 n
    HJ HARU HARU' Hin Hin'); [lia | rewrite Hreq; unfold HEAD; lia | | exact Hv].
  intros x Hx. apply NFP. rewrite Hreq. unfold HEAD in *. lia.
- intros j Hj. destruct (Hz j Hj) as [Hvj Hr]. split; [|exact Hr].
  apply (crcs_block_keep STK sp0 FS_PSTAT_FP ly S U W mem md own ly' S' W' mem' md' k (p - HEAD) (n + HEAD)
    (p + Z.of_nat j) 1 (nth j bs 0) HJ HARU HARU' Hin Hin'); [unfold HEAD; lia | rewrite Hreq; unfold HEAD; lia | | exact Hvj].
  intros x Hx. apply NFP. rewrite Hreq. unfold HEAD in *. lia.
Qed.
Lemma crcs_ev_nonneg : forall tb, 0 <= FSH_Fn_writer.dec_ev tb.
Proof.
intros tb. unfold FSH_Fn_writer.dec_ev. destruct (WriterSpec.b64_dec tb); vm_compute; discriminate.
Qed.

(* ---- the epilogue 0x827e8 .. 0x82884: n's shadow byte := f8, the frame's magic := retired, s2 <> 0 so the frame's
   shadow := f5 x 8 and the flag byte := 0 through the frame's last word (FSW_frame.v fsw_flag_storeU releases the frame),
   then the restores and `ret` (FSW_ret.v fsw_retU). The engine's state at 0x827e8 gets the flag byte as a region at the
   flag atom 45, s2 re-stated as the frame atom 25 (both hold the frame) and atom 25's fact, so `beqz s2` and
   `ld a0, 0x38(s2)` are decided ---- *)
Definition crcs_epi_ss (ss : sstate) : sstate :=
  add_atom (mkSS (ss_pc ss) (sr_set (ss_regs ss) 18%bv (SOff 25 0)) (YP09.mkRegion (Some 45%nat) 0 1 0 1 [] :: ss_mem ss)
    (ss_resv ss) (ss_facts ss)) 25 (mkAF 4096 (2 ^ 47) 5).
(* the callee-saved registers at the final `ret`: sp = s0's entry value, the restored s-registers, gp / tp / s11 kept *)
Definition crcs_expect (r : bv 5) : sv :=
  match Z.to_nat (bv_unsigned r) with
  | 2%nat => SOff 8 0 | 3%nat => SOff 3 0 | 4%nat => SOff 4 0 | 8%nat => SOff 34 0 | 9%nat => SOff 35 0
  | 18%nat => SOff 36 0 | 19%nat => SOff 37 0 | 20%nat => SOff 38 0 | 21%nat => SOff 39 0 | 22%nat => SOff 40 0
  | 23%nat => SOff 41 0 | 24%nat => SOff 42 0 | 25%nat => SOff 43 0 | 26%nat => SOff 44 0 | _ => SOff 27 0
  end.
Lemma crcs_apresent_app : forall ly S U (W : world tfibsegs) mem md a,
  ARU tfibsegs B ly S U W mem md -> app_addr a -> apresent (w_H W) (unpoison U mem) a -> apresent (w_H W) mem a.
Proof.
intros ly S U W mem md a H Ha (Hh & b & Hb). split; [exact Hh|]. exists b. rewrite <- Hb. symmetry.
pose proof asan_consts as (C1 & _ & C3 & _). unfold app_addr, kLowShadowBeg, ASAN_CEIL in Ha.
apply unpoison_out. rewrite (wz a ltac:(lia)).
destruct (in_ush U a) eqn:E; [|reflexivity]. exfalso.
assert (UF : aowned B ly S a /\ SHADOW_OFF <= a < kHighMemBeg) by (eapply ush_facts; eassumption).
unfold SHADOW_OFF in UF. lia.
Qed.
Lemma crcs_epi : forall ly S U W0 mem0 md0 regs0 pos FL lyc Sc (Wc : world tfibsegs) regsP msP mdP k ss80 ssR stR
    live peak cntF,
  afn_preU tfibsegs B STK_check_reject_clean_starved ly S U W0 regs0 mem0 md0 [] \/ True ->
  YK0s.ret_ok (getr regs0 1) ->
  st_ok tfibsegs (Ereg regsP (crcs_extra regs0 FL)) ss80 (restrict (w_H Wc) msP) ->
  ss_mem ss80 = ss_mem (crcs_fs 0 (crcs_fcs2 (2 ^ 64 - 1))) ->
  sr_get (ss_regs ss80) 18%bv = SOff 18 0 ->
  sym_runN tfibsegs crcs_tbl FUEL (crcs_epi_ss ss80) = (ssR, stR) ->
  match stR with RS_ecall => False | _ => True end ->
  ss_resv ssR = None -> clookup crcs_tbl (ss_pc ssR) = Some RET_WORD_r -> sr_get (ss_regs ssR) 1%bv = SOff 33 0 ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ssR) r) (crcs_expect r)) CALLEE_SAVED = true ->
  nth_error (ss_mem ssR) 0 = Some (YP09.mkRegion (Some 45%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 0))]) ->
  crcs_csr regs0 regsP (spZ regs0) (spZ regs0 - 128 - (spZ regs0 - 128) mod 32) (frame_addr lyc 0 pos) ->
  FL = flag_addr lyc 0 pos ->
  @ajournal rc SK tfibsegs B STK_check_reject_clean_starved (spZ regs0) FS_PSTAT_FP ly S W0 (unpoison U mem0) md0 [(0, pos)]
    lyc Sc Wc (unpoison U (ms_mem msP)) mdP k ->
  ARU tfibsegs B lyc Sc U Wc (ms_mem msP) mdP ->
  ablocks B lyc Sc = ablocks B ly S ->
  fs_glob tfibsegs Wc (ms_mem msP) live peak cntF SIZE_MAXZ ->
  SRr tfibsegs Wc (mkCfg msP mdP)
    (@fpostU fx rc SK tfibsegs B STK_check_reject_clean_starved (spZ regs0) FS_PSTAT_FP regs0 ly S U W0 mem0 md0 k U
       (fun ly' S' W' regs' mem' md' =>
          ablocks B ly' S' = ablocks B ly S /\ fs_glob tfibsegs W' mem' live peak cntF SIZE_MAXZ)).
Proof.
intros ly S U W0 mem0 md0 regs0 pos FL lyc Sc Wc regsP msP mdP k ss80 ssR stR live peak cntF _ Hret HS Hmem S18 Hrun Hst
  Hrv Hpc S1 Hcs Hfl CS HFL HJ HARU Eab HG.
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof crcs_stk as FS.
assert (Hin : In (0, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds tfibsegs B LAWS lyc Sc Wc (unpoison U (ms_mem msP)) mdP 0 pos HAR Hin) as (H4096 & HFc & HFapp).
destruct (al_frames _ _ LAWS lyc Sc Wc (unpoison U (ms_mem msP)) mdP 0 pos HAR Hin) as (HFal & _ & HFp & HFs).
destruct (crcs_FFL lyc Sc Wc (unpoison U (ms_mem msP)) mdP 0 pos HAR Hin) as (HLp & HLo & (HLapp & HLimg) & HL4096 & HLz & HLc).
change (fs_frame_bytes 0) with 64 in *. change (fs_frame_bytes 0 / 8) with 8 in *.
set (F := frame_addr lyc 0 pos) in *. rewrite <- HFL in *.
pose proof CS as (C2r & C3r & C4r & C8r & C18r & C20r & C23r & C24r & C25r & C26r & C27r).
set (E := Ereg regsP (crcs_extra regs0 FL)) in *.
pose proof (Z.mul_div_le F 8 ltac:(lia)) as Hd8. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)) as Hd0.
unfold in_app, kLowShadowBeg, ASAN_CEIL in HFapp. unfold app_addr, kLowShadowBeg, ASAN_CEIL in HLapp.
assert (E25 : bv_unsigned (ew E 25) = F) by (subst E; rewrite (ew_Ereg_nat regsP _ 25 25%bv eq_refl), C25r; apply unsigned_lit_small; lia).
assert (E24 : bv_unsigned (ew E 24) = shadow_addr F)
  by (subst E; rewrite (ew_Ereg_nat regsP _ 24 24%bv eq_refl), C24r; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia).
assert (E8 : bv_unsigned (ew E 8) = spZ regs0) by (subst E; rewrite (ew_Ereg_nat regsP _ 8 8%bv eq_refl), C8r; apply unsigned_lit_small; lia).
assert (E45 : bv_unsigned (ew E 45) = FL)
  by (subst E; change 45%nat with (32 + 13)%nat; rewrite ew_Ereg_extra; cbn [nth crcs_extra]; apply unsigned_lit_small; lia).
(* the flag byte is owned, the frame and its shadow are not: the regions are disjoint *)
assert (HFLnf : forall o, 0 <= o < 64 -> F + o <> FL) by (intros o Ho Heq; destruct (HFp (F + o) ltac:(lia)) as (_ & Hn); rewrite Heq in Hn; exact (Hn HLo)).
assert (HFLns : forall o, 0 <= o < 8 -> shadow_addr F + o <> FL) by (intros o Ho Heq; destruct (HFs o Ho) as (_ & Hn); rewrite Heq in Hn; exact (Hn HLo)).
(* the state at 0x827e8 with the flag region, s2 := the frame atom and the frame atom's fact *)
assert (HSE : st_ok tfibsegs E (crcs_epi_ss ss80) (restrict (w_H Wc) msP)).
{ unfold crcs_epi_ss. apply (st_ok_add_fact tfibsegs).
  - apply (crcs_set_reg (w_H Wc) E (mkSS (ss_pc ss80) (ss_regs ss80) (YP09.mkRegion (Some 45%nat) 0 1 0 1 [] :: ss_mem ss80)
      (ss_resv ss80) (ss_facts ss80)) msP 18%bv (SOff 25 0)).
    + apply (st_ok_add_region' tfibsegs E ss80 (restrict (w_H Wc) msP)); [exact HS | vm_compute; reflexivity | |].
      * unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict].
        rewrite E45. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable tfibsegs). replace (FL + o) with FL by lia.
        exact (crcs_apresent_app lyc Sc U Wc (ms_mem msP) mdP FL HARU ltac:(unfold app_addr, kLowShadowBeg, ASAN_CEIL; lia) HLp).
      * rewrite Hmem. apply all_disjoint_of_extents. unfold crcs_fs, crcs_fsS, fs_ret_s0_region, extent_of_region.
        cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E45, E25, E24, E8.
        cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
        split; [destruct (Z_lt_le_dec FL F) as [Hl|Hl]; [left; lia|]; destruct (Z_le_gt_dec (F + 64) FL) as [Hg|Hg]; [right; lia|];
          exfalso; exact (HFLnf (FL - F) ltac:(lia) ltac:(lia))|].
        split; [destruct (Z_lt_le_dec FL (shadow_addr F)) as [Hl|Hl]; [left; lia|];
          destruct (Z_le_gt_dec (shadow_addr F + 8) FL) as [Hg|Hg]; [right; lia|];
          exfalso; exact (HFLns (FL - shadow_addr F) ltac:(lia) ltac:(lia))|].
        split; [left; lia | exact I].
    + intros Hc. apply (f_equal (@bv_unsigned 5)) in Hc. vm_compute in Hc. discriminate Hc.
    + cbn [ss_regs]. rewrite (st_ok_restrict_reg tfibsegs _ _ _ _ 18%bv HS), S18, !fsw_SOff0.
      subst E. rewrite (ew_Ereg_nat regsP _ 18 18%bv eq_refl), (ew_Ereg_nat regsP _ 25 25%bv eq_refl), C18r, C25r. reflexivity.
  - unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E25. change (2 ^ 5) with 32. lia. }
assert (NIF : forall a, F <= a < F + 64 -> ~ in_img tfibsegs a).
{ intros a Ha. exact (proj2 (al_client_img _ _ LAWS lyc Sc Wc (unpoison U (ms_mem msP)) mdP a HAR
    (or_intror (or_introl (ex_intro _ 0 (ex_intro _ pos (conj Hin Ha))))))). }
assert (NIH : forall a, FS_IMG_END <= a -> ~ in_img tfibsegs a) by (intros a Ha Hi; pose proof (fs_segs_img a Hi); lia).
assert (HWR : forall a, in_wrange E (ss_mem (crcs_epi_ss ss80)) a ->
  (a = FL) \/ (F <= a < F + 64) \/ (shadow_addr F <= a < shadow_addr F + 8) \/ (spZ regs0 - 96 <= a < spZ regs0)).
{ intros a (rg & Hr & Ha). unfold crcs_epi_ss in Hr. cbn [ss_mem add_atom] in Hr. rewrite Hmem in Hr.
  unfold crcs_fs, crcs_fsS in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fs_ret_s0_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  - left. rewrite E45 in Ha. lia.
  - right; left. rewrite E25 in Ha. lia.
  - right; right; left. rewrite E24 in Ha. lia.
  - right; right; right. rewrite E8 in Ha. lia. }
eapply (fsw_flag_storeU B crcs_ML crcs_ASF crcs_FFL crcs_tbl crcs_tbl_ok Wc FUEL E (crcs_epi_ss ss80) ssR stR msP
  STK_check_reject_clean_starved (spZ regs0) FS_PSTAT_FP ly S W0 (unpoison U mem0) md0 [] lyc Sc U mdP k 0 pos _
  HSE Hrun Hst HJ HARU ltac:(lia)).
- intros a Ha. destruct (HWR a Ha) as [->|[Hf|[Hs|Hk]]].
  + right. exact HFL.
  + left. left; right; right; right. apply crcs_in_fr. exact Hf.
  + left. left; right; right; right. apply crcs_in_sh. exact Hs.
  + left. left; left. lia.
- intros msr HSr. rewrite <- HFL.
  pose proof (fsw_field E (ms_mem msr) 45 FL [YP09.mkChunk 0 (CVal 1 (SLit 0))] 0 1 0 1 0 1%N (SLit 0) 0
    (fsw_region_nth E ssR msr 0 _ HSr Hfl) E45 ltac:(left; reflexivity) ltac:(reflexivity) ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  specialize (V 0%nat ltac:(lia)). rewrite !Z.add_0_r in V. rewrite V. reflexivity.
- intros ms' mat' HS' HJ' HARU' HF HFr HG'.
  apply (fsw_retU B crcs_tbl crcs_tbl_ok Wc E ssR ms' _ STK_check_reject_clean_starved (spZ regs0) FS_PSTAT_FP regs0 ly S
    U W0 mem0 md0 lyc (stack_free_state 0 pos Sc) U k _ HS' Hrv Hpc).
  + rewrite (st_ok_restrict_reg tfibsegs _ _ _ _ 1%bv HS'), S1, fsw_SOff0. subst E.
    change 33%nat with (32 + 1)%nat. rewrite ew_Ereg_extra. cbn [nth crcs_extra]. exact Hret.
  + exact HJ'.
  + exact HARU'.
  + apply (fsw_preserved (w_H Wc) E ssR ms' regs0 crcs_expect HS' Hcs).
    intros r Hr. cbv [CALLEE_SAVED In] in Hr. subst E.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]].
    * change (crcs_expect 2%bv) with (SOff 8 0). rewrite fsw_SOff0, (ew_Ereg_nat regsP _ 8 8%bv eq_refl), C8r.
      unfold spZ. apply Z_to_bv_bv_unsigned.
    * change (crcs_expect 3%bv) with (SOff 3 0). rewrite fsw_SOff0, (ew_Ereg_nat regsP _ 3 3%bv eq_refl). exact C3r.
    * change (crcs_expect 4%bv) with (SOff 4 0). rewrite fsw_SOff0, (ew_Ereg_nat regsP _ 4 4%bv eq_refl). exact C4r.
    * change (crcs_expect 8%bv) with (SOff (32 + 2) 0). rewrite fsw_SOff0, ew_Ereg_extra. reflexivity.
    * change (crcs_expect 9%bv) with (SOff (32 + 3) 0). rewrite fsw_SOff0, ew_Ereg_extra. reflexivity.
    * change (crcs_expect 18%bv) with (SOff (32 + 4) 0). rewrite fsw_SOff0, ew_Ereg_extra. reflexivity.
    * change (crcs_expect 19%bv) with (SOff (32 + 5) 0). rewrite fsw_SOff0, ew_Ereg_extra. reflexivity.
    * change (crcs_expect 20%bv) with (SOff (32 + 6) 0). rewrite fsw_SOff0, ew_Ereg_extra. reflexivity.
    * change (crcs_expect 21%bv) with (SOff (32 + 7) 0). rewrite fsw_SOff0, ew_Ereg_extra. reflexivity.
    * change (crcs_expect 22%bv) with (SOff (32 + 8) 0). rewrite fsw_SOff0, ew_Ereg_extra. reflexivity.
    * change (crcs_expect 23%bv) with (SOff (32 + 9) 0). rewrite fsw_SOff0, ew_Ereg_extra. reflexivity.
    * change (crcs_expect 24%bv) with (SOff (32 + 10) 0). rewrite fsw_SOff0, ew_Ereg_extra. reflexivity.
    * change (crcs_expect 25%bv) with (SOff (32 + 11) 0). rewrite fsw_SOff0, ew_Ereg_extra. reflexivity.
    * change (crcs_expect 26%bv) with (SOff (32 + 12) 0). rewrite fsw_SOff0, ew_Ereg_extra. reflexivity.
    * change (crcs_expect 27%bv) with (SOff 27 0). rewrite fsw_SOff0, (ew_Ereg_nat regsP _ 27 27%bv eq_refl). exact C27r.
  + intros mat. split.
    * rewrite <- Eab. reflexivity.
    * apply (crcs_glob_keep Wc (ms_mem msP) (ms_mem ms')); [|exact HG].
      apply (crcs_img_keep _ _ _ _ HF). intros a Ha. destruct (HWR a Ha) as [->|[Hf|[Hs|Hk]]].
      -- exact HLimg.
      -- exact (NIF a Hf).
      -- apply NIH. unfold FS_IMG_END. unfold shadow_addr, SHADOW_OFF in Hs. lia.
      -- apply NIH. unfold FS_IMG_END. lia.
Qed.

(* ================= the walk ================= *)
Theorem check_reject_clean_starved_proof : @check_reject_clean_starved_spec fx rc SK tfibsegs B.
Proof.
intros ly S U W regs mem md ch t bd l tb live peak cnt HPRE HHEADS HTOP HFRL Ht Hbd Hl Hcstr Hkept Hbytes HWS Htb
  Hcaw Hglob Hquiet Hev Hbb Hlive Henc.
destruct HPRE as [HPREU HRO0].
pose proof (fsw_sp B _ ly S U W regs mem md ch HPREU) as (Hal16 & Hceil & H47 & HS0).
pose proof (fsw_ARU B _ ly S U W regs mem md ch HPREU) as HARU0.
pose proof HPREU as ((HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0) & OK0 & PO0).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof crcs_stk as FS.
destruct Hquiet as (_ & Hcnt0 & Hcnt2).
set (sp0 := spZ regs) in *.
(* ---- segment 0: the prologue to __asan_stack_malloc_0 ---- *)
apply (crcs_seg0 ly S U W regs mem md ch FS_PSTAT_FP _ HPREU).
intros ms1 mat1 HS1 HJ1 HARU1 HF1 HFr1.
destruct (crcs_sm_site ly S U W regs mem md ch ms1 HPREU HS1)
  as (R2 & R9 & Hsp1 & Hal1 & R1 & R10 & R3 & R4 & R8 & R24 & R19 & R20 & R21).
set (sp1 := 32 * ((spZ regs - 128) / 32)) in *.
set (md1 := with_vm_backing (m_vm_lazy md) mat1 md) in *.
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ crcs_ss1 ms1 HS1 eq_refl).
replace (Z_to_bv 64 (ss_pc crcs_ss1)) with (Z_to_bv 64 (pc_stack_malloc (as_code B) 0)) by (rewrite HPC0; reflexivity).
assert (Esp1 : spZ (ms_regs ms1) = sp1) by (unfold spZ; rewrite R2; apply unsigned_lit_small; lia).
assert (Hm16 : (sp1 - sp0) mod 16 = 0).
{ assert (Hm : sp1 mod 16 = 0).
  { apply (Z.mod_divide _ 16 ltac:(lia)). exists (2 * ((spZ regs - 128) / 32)). unfold sp1. lia. }
  rewrite Zminus_mod, Hm, Hal16. reflexivity. }
(* ---- the fake frame: granted (count_cid 0 (frames S) < fs_frames 0), so the real-stack fallback is dead ---- *)
eapply SRr_bind.
{ apply (fsw_stack_malloc_atU B errno_low crcs_ML crcs_SMP 0 (proj2 RTsm0) ltac:(lia)
    W (ms_regs ms1) (ms_mem ms1) STK_check_reject_clean_starved sp0 FS_PSTAT_FP ly S W (unpoison U mem) md [] ly S U
    md1 0 (sp1 - sp0) (getr (ms_regs ms1) 1) HJ1 HARU1).
  - rewrite Esp1. lia.
  - assert (Hm : sp1 mod 16 = 0).
    { apply (Z.mod_divide _ 16 ltac:(lia)). exists (2 * ((spZ regs - 128) / 32)). unfold sp1. lia. }
    rewrite Zminus_mod, Hm, Hal16. reflexivity.
  - lia.
  - unfold ESTACK. lia.
  - rewrite R3. exact Hgp0.
  - rewrite R4. exact Htp0.
  - reflexivity.
  - rewrite R1. reflexivity.
  - exact (crcs_grant (frames S) HFRL). }
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HARU2 & HP2 & R10b & Eab2 & Hfrs2 & Hfresh & Hnev2 &
  Hbb2 & Hz2 & Hflag2 & Hkept2).
rewrite R1.
set (F := frame_addr ly 0 pos) in *. set (FL := flag_addr ly 0 pos) in *.
set (ext := crcs_extra regs FL).
assert (Hin2 : In (0, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
pose proof (ARU_AR tfibsegs B ly S2 U W mem2 md2 HARU2) as HAR2.
destruct (frames_bounds tfibsegs B LAWS ly S2 W (unpoison U mem2) md2 0 pos HAR2 Hin2) as (HF4096 & HFceil & HFapp).
destruct (al_frames _ _ LAWS ly S2 W (unpoison U mem2) md2 0 pos HAR2 Hin2) as (HFal & _ & HFp & HFs).
change (fs_frame_bytes 0) with 64 in *.
destruct (crcs_FFL ly S2 W (unpoison U mem2) md2 0 pos HAR2 Hin2) as (HFLp & HFLo & (HFLapp & HFLimg) & HFL4096 & HFLz & HFLc).
fold F FL in HFLp, HFLo, HFLapp, HFLimg, HFL4096, HFLz, HFLc.
(* ---- the resume at 0x826e4 ---- *)
assert (HS2 : st_ok tfibsegs (Ereg regs2 ext) crcs_ss2
  (restrict (w_H W) (mkst regs2 (Z_to_bv 64 0x826e4) mem2 (seg_rom tfibsegs)))).
{ apply (fsw_resume_after_stack_mallocU B STK_check_reject_clean_starved sp0 FS_PSTAT_FP ly S W (unpoison U mem) md [] ly S S2 U W
    (ms_mem ms1) md1 mem2 md2 0 0 pos sp1 regs2 ext 0x826e4 (-96) 0 crcs_sv_chunks 9 0x18 0x20 10 (SOff 45 0)
    HJ2 HARU2 HARU1).
  - replace (sp1 - ESTACK) with (sp0 + (sp1 - sp0) - ESTACK) by lia. replace sp1 with (sp0 + (sp1 - sp0)) at 2 by lia.
    exact Hkept2.
  - exact Hin2.
  - lia.
  - rewrite (ew_Ereg_nat regs2 ext 8 8%bv eq_refl), (fsw_pres (ms_regs ms1) regs2 8%bv HP2 ltac:(crcs_cs)), R8.
    reflexivity.
  - rewrite (ew_Ereg_nat regs2 ext 9 9%bv eq_refl), (fsw_pres (ms_regs ms1) regs2 9%bv HP2 ltac:(crcs_cs)), R9.
    apply unsigned_lit_small. lia.
  - rewrite (ew_Ereg_nat regs2 ext 10 10%bv eq_refl), R10b. apply unsigned_lit_small. lia.
  - change 45%nat with (32 + 13)%nat. rewrite fsw_extra_atom. reflexivity.
  - change (fs_frame_bytes 0) with 64. exact Hflag2.
  - lia.
  - lia.
  - lia.
  - lia.
  - unfold sp0. lia.
  - vm_compute. reflexivity.
  - unfold crcs_sv_chunks. repeat constructor; cbn; lia.
  - apply (crcs_sv_init W regs ms1 (Ereg regs2 ext) HS1).
    intros n Hn. rewrite crcs_ew_extra by lia. unfold ext, crcs_extra.
    destruct n as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
      try lia; reflexivity. }
(* atom values of the resume environment *)
set (E2 := Ereg regs2 ext) in *.
assert (E2r : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = getr regs2 r)
  by (intros n r Hn; exact (ew_Ereg_nat regs2 ext n r Hn)).
assert (R2_8 : getr regs2 8%bv = Z_to_bv 64 sp0).
{ rewrite (fsw_pres (ms_regs ms1) regs2 8%bv HP2 ltac:(crcs_cs)), R8.
  unfold sp0, spZ. symmetry. apply Z_to_bv_bv_unsigned. }
assert (R2_2 : getr regs2 2%bv = Z_to_bv 64 sp1)
  by (rewrite (fsw_pres (ms_regs ms1) regs2 2%bv HP2 ltac:(crcs_cs)), R2; reflexivity).
assert (R2_9 : getr regs2 9%bv = Z_to_bv 64 sp1)
  by (rewrite (fsw_pres (ms_regs ms1) regs2 9%bv HP2 ltac:(crcs_cs)), R9; reflexivity).
assert (R2_24 : getr regs2 24%bv = Z_to_bv 64 SHADOW_OFF)
  by (rewrite (fsw_pres (ms_regs ms1) regs2 24%bv HP2 ltac:(crcs_cs)), R24; reflexivity).
assert (R2_3 : getr regs2 3%bv = getr regs 3%bv)
  by (rewrite (fsw_pres (ms_regs ms1) regs2 3%bv HP2 ltac:(crcs_cs)), R3; reflexivity).
assert (R2_4 : getr regs2 4%bv = getr regs 4%bv)
  by (rewrite (fsw_pres (ms_regs ms1) regs2 4%bv HP2 ltac:(crcs_cs)), R4; reflexivity).
assert (R2_19 : getr regs2 19%bv = getr regs 12%bv)
  by (rewrite (fsw_pres (ms_regs ms1) regs2 19%bv HP2 ltac:(crcs_cs)), R19; reflexivity).
assert (R2_20 : getr regs2 20%bv = getr regs 11%bv)
  by (rewrite (fsw_pres (ms_regs ms1) regs2 20%bv HP2 ltac:(crcs_cs)), R20; reflexivity).
assert (R2_21 : getr regs2 21%bv = getr regs 10%bv)
  by (rewrite (fsw_pres (ms_regs ms1) regs2 21%bv HP2 ltac:(crcs_cs)), R21; reflexivity).
assert (R2_27 : getr regs2 27%bv = getr regs 27%bv).
{ rewrite (fsw_pres (ms_regs ms1) regs2 27%bv HP2 ltac:(crcs_cs)).
  exact (fsw_reg_atom (w_H W) regs fs_extraT crcs_ss1 ms1 27%bv 27%bv 27 HS1 ltac:(vm_compute; reflexivity) eq_refl). }
assert (E2_8 : bv_unsigned (ew E2 8) = sp0)
  by (subst E2; rewrite (ew_Ereg_nat regs2 ext 8 8%bv eq_refl), R2_8; apply unsigned_lit_small; lia).
assert (E2_9 : bv_unsigned (ew E2 9) = sp1)
  by (subst E2; rewrite (ew_Ereg_nat regs2 ext 9 9%bv eq_refl), R2_9; apply unsigned_lit_small; lia).
assert (E2_10 : bv_unsigned (ew E2 10) = F)
  by (subst E2; rewrite (ew_Ereg_nat regs2 ext 10 10%bv eq_refl), R10b; apply unsigned_lit_small; lia).
assert (E2_24 : bv_unsigned (ew E2 24) = SHADOW_OFF)
  by (subst E2; rewrite (ew_Ereg_nat regs2 ext 24 24%bv eq_refl), R2_24; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
pose proof (Z.mul_div_le F 8 ltac:(lia)) as Hd8. pose proof (Z.div_pos F 8 ltac:(lia) ltac:(lia)) as Hd0.
unfold in_app, kLowShadowBeg, ASAN_CEIL in HFapp.
(* image bytes the walk's runs never write *)
assert (NIF : forall a, F <= a < F + 64 -> ~ in_img tfibsegs a).
{ intros a Ha. exact (proj2 (al_client_img _ _ LAWS ly S2 W (unpoison U mem2) md2 a HAR2
    (or_intror (or_introl (ex_intro _ 0 (ex_intro _ pos (conj Hin2 Ha))))))). }
assert (NIH : forall a, FS_IMG_END <= a -> ~ in_img tfibsegs a) by (intros a Ha Hi; pose proof (fs_segs_img a Hi); lia).
(* fuzz/alloc.c's statics from the entry to the resume: segment 0's run writes only its frame; the runtime call keeps
   them (crcs_glob_acall) *)
assert (G1 : fs_glob tfibsegs W (ms_mem ms1) live peak cnt SIZE_MAXZ).
{ apply (crcs_glob_keep W mem (ms_mem ms1)); [|exact Hglob].
  apply (crcs_img_keep _ _ _ _ HF1).
  intros a (rg & Hr & Ha). unfold crcs_ss0, fss0T_args, fsT_regions_args, fsT_regions, fs_uar_regions in Hr.
  cbn [ss_mem app In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]];
    cbn [fstk fs_got_region fs_bcell_region fs_got_uar_region fs_uar_cell_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    try lia.
  apply NIH. rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl) in Ha. unfold FS_IMG_END. fold (spZ regs) sp0 in Ha. lia. }
assert (G2 : fs_glob tfibsegs W mem2 live peak cnt SIZE_MAXZ)
  by exact (crcs_glob_acall ly S ly S2 U W W (ms_mem ms1) mem2 md1 md2 _ _ live peak cnt SIZE_MAXZ HARU1 HARU2 Hkept2 G1).
(* ---- 0x826e4 .. 0x82750: s9 at 0x18(s1), s7 := s9 + 32, the frame header, s8 := (s9 >> 3) + s8 ---- *)
fsw_aj_run_toU crcs_tbl_ok HS2 HJ2 HARU2 0x82750.
{ unfold crcs_ss2, fsw_resume_ss, fsw_resume_regions. cbn [ss_mem]. change (fs_frame_bytes 0) with 64.
  eapply awr_ok_cons_stack; [reflexivity | exact E2_8 | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ _ _ _ 9%nat (sp1 - sp0));
    [reflexivity | rewrite E2_9; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  eapply awr_ok_cons_gen; [reflexivity | exact E2_10 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. left; right; right; right. apply crcs_in_fr. lia. }
  apply awr_ok_nil. }
rename ms into msA. rename mat into matA. rename HF into HFA. rename HFr into HFrA. rename HG into HGA.
assert (G3 : fs_glob tfibsegs W (ms_mem msA) live peak cnt SIZE_MAXZ).
{ apply (crcs_glob_keep W mem2 (ms_mem msA)); [|exact G2].
  apply (crcs_img_keep _ _ _ _ HFA).
  intros a (rg & Hr & Ha). unfold crcs_ss2, fsw_resume_ss, fsw_resume_regions in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<-|[<-|[<-|[]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  - apply NIH. rewrite E2_8 in Ha. unfold FS_IMG_END. lia.
  - apply NIH. rewrite E2_9 in Ha. unfold FS_IMG_END. lia.
  - apply NIF. rewrite E2_10 in Ha. change (fs_frame_bytes 0) with 64 in Ha. lia. }
set (md3 := with_vm_backing (m_vm_lazy md2) matA md2) in *.
(* s8 holds the frame's shadow address *)
assert (Hs8 : getr (ms_regs msA) 24%bv = Z_to_bv 64 (shadow_addr F)).
{ crcs_reg HS2 (24%bv : bv 5). rewrite (denot_lit_U E2). f_equal.
  rewrite !U_SAlu, !U_SOff, U_SLit. cbn [zalu_raw]. rewrite E2_10, E2_24, !Z.add_0_r.
  unfold zcanon, M64. rewrite (Z.mod_small F) by lia. change (3 mod 2 ^ 64) with 3. change (Z.land 3 63) with 3.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  rewrite (Z.mod_small (F / 8)) by lia. unfold shadow_addr, SHADOW_OFF. rewrite Z.mod_small by lia. lia. }
pose proof (ARU_AR tfibsegs B ly S2 U W (ms_mem msA) md3 HARU2) as HARA.
destruct (al_frames _ _ LAWS ly S2 W (unpoison U (ms_mem msA)) md3 0 pos HARA Hin2) as (_ & _ & _ & HFsA).
change (fs_frame_bytes 0 / 8) with 8 in HFsA. fold F in HFsA.
(* ---- 0x82750: s8 re-seated on the fresh atom 46 (FSW_K fsw_reseat_atom), with the frame's shadow as a region ---- *)
pose proof (fsw_reseat_atom E2 _ (restrict (w_H W) msA) 24%bv 46 0 8 (mkAF 0 (2 ^ 64 - 1) 0) HS2) as HS3.
change (ms_regs (restrict (w_H W) msA)) with (ms_regs msA) in HS3. rewrite Hs8 in HS3.
change (ms_mem (restrict (w_H W) msA)) with (mrestrict (w_H W) (ms_mem msA)) in HS3.
set (E3 := ewset E2 46 (Z_to_bv 64 (shadow_addr F))) in HS3.
assert (E3_46 : bv_unsigned (ew E3 46) = shadow_addr F)
  by (subst E3; rewrite ew_ewset_same; apply unsigned_lit_small; unfold shadow_addr, SHADOW_OFF; lia).
assert (E3o : forall n, n <> 46%nat -> ew E3 n = ew E2 n) by (intros n Hn; subst E3; apply ew_ewset_other; exact Hn).
clearbody E3.
specialize (HS3 ltac:(vm_compute; reflexivity)
  ltac:(intros Hc; apply (f_equal (@bv_unsigned 5)) in Hc; vm_compute in Hc; discriminate Hc)
  ltac:(vm_compute; reflexivity)).
specialize (HS3 ltac:(
  unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
  rewrite E3_46; split; [unfold shadow_addr, SHADOW_OFF; lia|]; split; [unfold shadow_addr, SHADOW_OFF; lia|];
  split; [|constructor];
  intros o Ho; apply (apresent_writable tfibsegs);
  destruct (HFsA o Ho) as (Hp & Hno);
  exact (fsw_apresent_notowned B ly S2 U W (ms_mem msA) md3 (shadow_addr F + o) HARU2
    ltac:(unfold shadow_addr, SHADOW_OFF; lia) Hno Hp))).
specialize (HS3 ltac:(
  apply all_disjoint_of_extents; unfold extent_of_region; cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi base_val];
  rewrite E3_46, (E3o 8%nat ltac:(lia)), (E3o 9%nat ltac:(lia)), (E3o 10%nat ltac:(lia)), E2_8, E2_9, E2_10;
  cbn [zall_disjoint]; unfold zdisj; cbn [fst snd]; unfold shadow_addr, SHADOW_OFF;
  repeat split; try exact I; lia)).
specialize (HS3 ltac:(
  unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E3_46; unfold shadow_addr, SHADOW_OFF;
  split; [lia|]; split; [apply Z.mod_1_r | lia])).
(* ---- 0x82750 .. 0x82774: the frame's shadow f1 f1 f1 f1 f8 f3 f3 f3, then jal fuzz_alloc_live ---- *)
fsw_aj_run_toU crcs_tbl_ok HS3 HJ2 HARU2 A_fuzz_alloc_live.
{ cbn [ss_mem add_atom].
  eapply awr_ok_cons_gen; [reflexivity | exact E3_46 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. left; right; right; right. apply crcs_in_sh. fold F. lia. }
  eapply awr_ok_cons_stack; [reflexivity | rewrite (E3o 8%nat ltac:(lia)); exact E2_8 | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ _ _ _ 9%nat (sp1 - sp0));
    [reflexivity | rewrite (E3o 9%nat ltac:(lia)), E2_9; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |].
  eapply awr_ok_cons_gen; [reflexivity | rewrite (E3o 10%nat ltac:(lia)); exact E2_10 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. left; right; right; right. apply crcs_in_fr. lia. }
  apply awr_ok_nil. }
rename ms into msB. rename mat into matB. rename HF into HFB. rename HFr into HFrB. rename HG into HGB.
assert (G4 : fs_glob tfibsegs W (ms_mem msB) live peak cnt SIZE_MAXZ).
{ apply (crcs_glob_keep W (ms_mem msA) (ms_mem msB)); [|exact G3].
  apply (crcs_img_keep _ _ _ _ HFB).
  intros a (rg & Hr & Ha). cbn [ss_mem add_atom In] in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  - apply NIH. rewrite E3_46 in Ha. unfold FS_IMG_END. unfold shadow_addr, SHADOW_OFF in Ha. lia.
  - apply NIH. rewrite (E3o 8%nat ltac:(lia)), E2_8 in Ha. unfold FS_IMG_END. lia.
  - apply NIH. rewrite (E3o 9%nat ltac:(lia)), E2_9 in Ha. unfold FS_IMG_END. lia.
  - apply NIF. rewrite (E3o 10%nat ltac:(lia)), E2_10 in Ha. lia. }
(* ---- fuzz_alloc_live () (fs.c:211, jal 0x82774) ---- *)
set (md4 := with_vm_backing (m_vm_lazy md3) matB md3) in *.
set (ch1 := (sp0, raZ regs, s0Z regs) :: ch).
assert (RB2 : getr (ms_regs msB) 2%bv = Z_to_bv 64 sp1).
{ crcs_reg HS3 (2%bv : bv 5). rewrite fsw_SOff0, (E3o 2%nat ltac:(lia)), (E2r 2%nat 2%bv eq_refl). exact R2_2. }
assert (RB8 : getr (ms_regs msB) 8%bv = Z_to_bv 64 sp0).
{ crcs_reg HS3 (8%bv : bv 5). rewrite fsw_SOff0, (E3o 8%nat ltac:(lia)), (E2r 8%nat 8%bv eq_refl). exact R2_8. }
assert (RB3 : getr (ms_regs msB) 3%bv = getr regs 3%bv).
{ crcs_reg HS3 (3%bv : bv 5). rewrite fsw_SOff0, (E3o 3%nat ltac:(lia)), (E2r 3%nat 3%bv eq_refl). exact R2_3. }
assert (RB4 : getr (ms_regs msB) 4%bv = getr regs 4%bv).
{ crcs_reg HS3 (4%bv : bv 5). rewrite fsw_SOff0, (E3o 4%nat ltac:(lia)), (E2r 4%nat 4%bv eq_refl). exact R2_4. }
assert (RB1 : getr (ms_regs msB) 1%bv = Z_to_bv 64 0x82778)
  by exact (fsw_reg_lit (w_H W) E3 _ msB 1%bv 0x82778 HS3 ltac:(vm_compute; reflexivity) ltac:(lia)).
assert (HspB : spZ (ms_regs msB) = sp1) by (unfold spZ; rewrite RB2; apply unsigned_lit_small; lia).
assert (CsB : Forall (YP09.chunk_ok tfibsegs E3 (mrestrict (w_H W) (ms_mem msB)) sp0) crcs_sv_chunks).
{ apply (crcs_sv_at E3 _ (w_H W) msB 1 sp0 HS3 ltac:(vm_compute; reflexivity)). rewrite (E3o 8%nat ltac:(lia)). exact E2_8. }
assert (ExB : forall n, (33 <= n < 45)%nat -> ew E3 n = nth (n - 32) ext (Z_to_bv 64 0)).
{ intros n Hn. rewrite (E3o n ltac:(lia)). exact (crcs_ew_extra regs2 ext n ltac:(lia)). }
destruct (crcs_sv_ra E3 _ sp0 (raZ regs) (s0Z regs) CsB) as [V8 V16].
{ rewrite fsw_SOff0, (ExB 33%nat ltac:(lia)). unfold ext, crcs_extra. cbn [nth Nat.sub]. unfold raZ. symmetry. apply Z_to_bv_bv_unsigned. }
{ apply u64_range. }
{ rewrite fsw_SOff0, (ExB 34%nat ltac:(lia)). unfold ext, crcs_extra. cbn [nth Nat.sub]. unfold s0Z. symmetry. apply Z_to_bv_bv_unsigned. }
{ apply u64_range. }
assert (AROB : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) (ms_mem msB))).
{ apply (proj2 (crcs_aro_unp ly S2 U W (ms_mem msB) md4 HARU2)).
  eapply crcs_arodata_j; [exact HJ2|]. apply (proj1 (crcs_aro_unp ly S U W mem md HARU0)). exact HRO0. }
assert (ChB : achain ly (aview tfibsegs (w_H W) (unpoison U (ms_mem msB))) (spZ (ms_regs msB)) (s0Z (ms_regs msB)) ch1).
{ replace (s0Z (ms_regs msB)) with sp0 by (unfold s0Z; rewrite RB8; symmetry; apply unsigned_lit_small; lia).
  apply (crcs_chain_at ly S U W mem md regs ch ly S2 W (ms_mem msB) md4 0 [(0, pos)] (spZ (ms_regs msB)) Hch0 HTOP
    HARU2 HJ2 V8 V16 Hra40). rewrite HspB. lia. }
assert (HPREB : fpreU tfibsegs B STK_fuzz_alloc ly S2 U W (ms_regs msB) (ms_mem msB) md4 ch1).
{ apply (crcs_fpreU B _ sp0 FS_PSTAT_FP ly S U W mem md [(0, pos)] ly S2 W (ms_mem msB) md4 0 (ms_regs msB)
    STK_fuzz_alloc (sp1 - sp0) ch1 HJ2 HARU2 AROB).
  - rewrite HspB. lia.
  - exact Hm16.
  - lia.
  - change STK_fuzz_alloc with 0. lia.
  - change STK_fuzz_alloc with 0. lia.
  - rewrite RB1. vm_compute. reflexivity.
  - unfold raZ. rewrite RB1, unsigned_lit_small by lia. lia.
  - rewrite RB3. exact Hgp0.
  - rewrite RB4. exact Htp0.
  - exact ChB. }
assert (CSB : crcs_csr regs (ms_regs msB) sp0 sp1 F).
{ unfold crcs_csr. split; [exact RB2|]. split; [exact RB3|]. split; [exact RB4|]. split; [exact RB8|].
  split; [crcs_reg HS3 (18%bv : bv 5); rewrite fsw_SOff0, (E3o 10%nat ltac:(lia)), (E2r 10%nat 10%bv eq_refl); exact R10b|].
  split; [crcs_reg HS3 (20%bv : bv 5); rewrite fsw_SOff0, (E3o 20%nat ltac:(lia)), (E2r 20%nat 20%bv eq_refl); exact R2_20|].
  split; [crcs_reg HS3 (23%bv : bv 5); apply bv_eq; rewrite denot_SOff, (E3o 10%nat ltac:(lia)), E2_10, unsigned_lit_small by lia;
    apply zcanon_id; unfold M64; lia|].
  split; [crcs_reg HS3 (24%bv : bv 5); rewrite fsw_SOff0; apply bv_eq; rewrite E3_46, unsigned_lit_small;
    [reflexivity | unfold shadow_addr, SHADOW_OFF; lia]|].
  split; [crcs_reg HS3 (25%bv : bv 5); rewrite fsw_SOff0, (E3o 10%nat ltac:(lia)), (E2r 10%nat 10%bv eq_refl); exact R10b|].
  split; [exact (fsw_reg_lit (w_H W) E3 _ msB 26%bv (2 ^ 64 - 8) HS3 ltac:(vm_compute; reflexivity) ltac:(lia))|].
  crcs_reg HS3 (27%bv : bv 5). rewrite fsw_SOff0, (E3o 27%nat ltac:(lia)), (E2r 27%nat 27%bv eq_refl). exact R2_27. }
assert (RB21 : getr (ms_regs msB) 21%bv = getr regs 10%bv).
{ crcs_reg HS3 (21%bv : bv 5). rewrite fsw_SOff0, (E3o 21%nat ltac:(lia)), (E2r 21%nat 21%bv eq_refl). exact R2_21. }
assert (RB19 : getr (ms_regs msB) 19%bv = getr regs 12%bv).
{ crcs_reg HS3 (19%bv : bv 5). rewrite fsw_SOff0, (E3o 19%nat ltac:(lia)), (E2r 19%nat 19%bv eq_refl). exact R2_19. }
(* the flag word in the frame at the call *)
assert (VFL : val_mem tfibsegs (mrestrict (w_H W) (ms_mem msB)) (F + 56) 8 FL).
{ eapply (crcs_val_at E3 _ (w_H W) msB 3 _ _ _ _ _ _ 56 8%N (SOff 45 0) FL F);
    [exact HS3 | reflexivity | cbn; repeat (first [left; reflexivity | right]) | | | |].
  - rewrite (E3o 10%nat ltac:(lia)). exact E2_10.
  - change 45%nat with (32 + 13)%nat. rewrite fsw_SOff0, (E3o (32 + 13)%nat ltac:(lia)). subst E2.
    rewrite ew_Ereg_extra. reflexivity.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - cbn. lia. }
refine (crcs_call STK_check_reject_clean_starved sp0 FS_PSTAT_FP ly S U W mem md [(0, pos)] ly S2 W msB md4 0 E3 _
  STK_fuzz_alloc [] 0 _ _ ext 0x82778 HS3 eq_refl HJ2 HARU2
  (LIVE ly S2 U W (ms_regs msB) (ms_mem msB) md4 ch1 live peak cnt SIZE_MAXZ HPREB (crcs_heads B ly S ly S2 U Eab2 HHEADS) G4)
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) RB1 RB8 ltac:(rewrite HspB; change STK_fuzz_alloc with 0; lia)
  ltac:(rewrite HspB; lia) ltac:(lia) CsB ExB _).
intros ly3 S3 W3 regs3 mem3 md5 (Q10 & Qab & Qglob & Qheads) HP3 HJc3 HJ3 HARU3 HSr3.
(* ---- after fuzz_alloc_live: 0x82778 (s6 := live), then s7's shadow byte := 0, n := SIZE_MAX, jal fuzz_alloc_fail ---- *)
pose proof HJ3 as (HAR3 & Hly3 & _ & _ & _ & Hfrs3 & Hnev3 & _).
pose proof Hly3 as (_ & _ & _ & _ & _ & EF3 & _).
assert (EA3 : frame_addr ly3 0 pos = F) by (unfold F, frame_addr; rewrite EF3; reflexivity).
assert (Hin3 : In (0, pos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
pose proof (crcs_csr_call regs (ms_regs msB) regs3 sp0 sp1 F HP3 CSB) as CS3.
pose proof CS3 as (C3_2 & C3_3 & C3_4 & C3_8 & C3_18 & C3_20 & C3_23 & C3_24 & C3_25 & C3_26 & C3_27).
assert (R3_21 : getr regs3 21%bv = getr regs 10%bv) by (rewrite (fsw_pres _ _ 21%bv HP3 ltac:(crcs_cs)); exact RB21).
assert (R3_19 : getr regs3 19%bv = getr regs 12%bv) by (rewrite (fsw_pres _ _ 19%bv HP3 ltac:(crcs_cs)); exact RB19).
pose proof HARU3 as (HAR3' & OK3 & PO3).
assert (VFL3 : val_mem tfibsegs (mrestrict (w_H W3) mem3) (F + 56) 8 FL).
{ apply (crcs_val_keep_call B _ _ _ ly S2 U W (ms_mem msB) md4 ly3 S3 U W3 mem3 md5 0 0 pos (F + 56) 8 FL HJc3 HARU2 OK3 PO3
    Hin2 ltac:(lia)); [fold F; lia | fold F; change (fs_frame_bytes 0) with 64; cbn; lia | intros x _ Hx; exact (inFP_nil x Hx) | exact VFL]. }
set (fcs1 := [YP09.mkChunk 56 (CVal 8 (SOff 45 0))]).
assert (HSf3 : st_ok tfibsegs (Ereg regs3 ext) (crcs_fs 0x82778 fcs1)
  (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 0x82778) mem3 (seg_rom tfibsegs)))).
{ apply (crcs_readd ly3 S3 U W3 md5 regs3 mem3 ext 0x82778 fcs1 pos sp0 HARU3 Hin3 HSr3); rewrite ?EA3.
  - exact C3_25.
  - exact C3_24.
  - exact C3_8.
  - lia.
  - lia.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    apply (chunk_ok_val tfibsegs _ _ F 56 8 (SOff 45 0) FL); [| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | cbn; lia | exact VFL3].
    change 45%nat with (32 + 13)%nat. rewrite fsw_SOff0, ew_Ereg_extra. reflexivity. }
(* frame bytes are image bytes of no callee footprint at FS_PSTAT_FP *)
assert (NFP : forall x, F <= x < F + 64 -> ~ inFP FS_PSTAT_FP x)
  by (intros x Hx Hf; exact (NIF x Hx (crcs_pstat_img x Hf))).
(* ---- 0x82778 .. 0x8278c: s6 := live, n's shadow byte := 0, n := SIZE_MAX; jal fuzz_alloc_fail (0) (fs.c:213) ---- *)
let res := eval vm_compute in (sym_run_toN tfibsegs crcs_tbl FUEL A_fuzz_alloc_fail (crcs_fs 0x82778 fcs1)) in
lazymatch res with (?ssC, ?stC) =>
  apply (crcs_seg ly S U W mem md pos ly3 S3 W3 regs3 mem3 md5 (0 + 0) ext sp0 0x82778 fcs1 [] (crcs_fs 0x82778 fcs1)
    A_fuzz_alloc_fail ssC stC _ HSf3 eq_refl HJ3 HARU3 C3_8 ltac:(rewrite EA3; exact C3_25) ltac:(rewrite EA3; exact C3_24)
    ltac:(vm_compute; reflexivity) I)
end.
intros msD matD HSD HJD HARUD HID.
set (mdD := with_vm_backing (m_vm_lazy md5) matD md5) in *.
destruct (crcs_site ly S U W mem md regs ch pos FL ly3 S3 W3 regs3 msD mdD (0 + 0) _ 0x82790 sp1 STK_fuzz_alloc HPREU HTOP
  HRO0 HSD ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) C3_2 C3_3 C3_4 C3_8
  ltac:(lia) Hm16 ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(change STK_fuzz_alloc with 0; lia)
  ltac:(change STK_fuzz_alloc with 0; lia) HJD HARUD) as (HPRED & RD1 & RD8 & HspD & CsD & ExD).
assert (RD10 : getr (ms_regs msD) 10%bv = w64 0)
  by exact (fsw_reg_lit (w_H W3) _ _ msD 10%bv 0 HSD ltac:(vm_compute; reflexivity) ltac:(lia)).
assert (GD : fs_glob tfibsegs W3 (ms_mem msD) live peak cnt SIZE_MAXZ)
  by exact (crcs_glob_keep W3 mem3 (ms_mem msD) _ _ _ _ HID Qglob).
assert (VD32 : val_mem tfibsegs (mrestrict (w_H W3) (ms_mem msD)) (F + 32) 8 (2 ^ 64 - 1)).
{ eapply (crcs_val_at (Ereg regs3 ext) _ (w_H W3) msD 0 _ _ _ _ _ _ 32 8%N (SLit (2 ^ 64 - 1)) (2 ^ 64 - 1) F);
    [exact HSD | reflexivity | cbn; repeat (first [left; reflexivity | right]) | | | |].
  - rewrite (ew_Ereg_nat regs3 ext 25 25%bv eq_refl), C3_25. apply unsigned_lit_small. lia.
  - apply bv_eq. rewrite unsigned_lit_small by lia. change (bv_unsigned (sv_denot (Ereg regs3 ext) (SLit (2 ^ 64 - 1))))
      with (YP0e.U (Ereg regs3 ext) (SLit (2 ^ 64 - 1))). rewrite U_lit by lia. reflexivity.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - cbn. lia. }
assert (VD56 : val_mem tfibsegs (mrestrict (w_H W3) (ms_mem msD)) (F + 56) 8 FL).
{ eapply (crcs_val_at (Ereg regs3 ext) _ (w_H W3) msD 0 _ _ _ _ _ _ 56 8%N (SOff 45 0) FL F);
    [exact HSD | reflexivity | cbn; repeat (first [left; reflexivity | right]) | | | |].
  - rewrite (ew_Ereg_nat regs3 ext 25 25%bv eq_refl), C3_25. apply unsigned_lit_small. lia.
  - change 45%nat with (32 + 13)%nat. rewrite fsw_SOff0, ew_Ereg_extra. reflexivity.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - cbn. lia. }
(* n's shadow byte (frame + 32's granule) is 00 since 0x82780 *)
assert (VDsh : val_mem tfibsegs (mrestrict (w_H W3) (ms_mem msD)) (shadow_addr F + 4) 1 0).
{ eapply (crcs_val_at (Ereg regs3 ext) _ (w_H W3) msD 1 _ _ _ _ _ _ 4 1%N (SLit 0) 0 (shadow_addr F));
    [exact HSD | reflexivity | cbn; repeat (first [left; reflexivity | right]) | | | |].
  - rewrite (ew_Ereg_nat regs3 ext 24 24%bv eq_refl), C3_24. apply unsigned_lit_small. unfold shadow_addr, SHADOW_OFF; lia.
  - apply bv_eq. rewrite unsigned_lit_small by lia. change (bv_unsigned (sv_denot (Ereg regs3 ext) (SLit 0)))
      with (YP0e.U (Ereg regs3 ext) (SLit 0)). rewrite U_lit by lia. reflexivity.
  - change (2 ^ (8 * Z.of_N 1)) with 256. lia.
  - cbn. lia. }
refine (crcs_call STK_check_reject_clean_starved sp0 FS_PSTAT_FP ly S U W mem md [(0, pos)] ly3 S3 W3 msD mdD (0 + 0)
  (Ereg regs3 ext) _ STK_fuzz_alloc FS_PSTAT_FP 0 _ _ ext 0x82790 HSD eq_refl HJD HARUD
  (FAIL ly3 S3 U W3 (ms_regs msD) (ms_mem msD) mdD ch1 live peak cnt SIZE_MAXZ 0 HPRED Qheads GD RD10 ltac:(lia))
  ltac:(intros a Ha; right; right; left; split; [exact Ha | exact (crcs_pstat_img a Ha)]) RD1 RD8
  ltac:(rewrite HspD; change STK_fuzz_alloc with 0; lia) ltac:(rewrite HspD; lia) ltac:(lia) CsD ExD _).
intros ly4 S4 W4 regs4 mem4 md6 (Qab4 & Qheads4 & Qglob4) HP4 HJc4 HJ4 HARU4 HSr4.
rewrite (crcs_fail0 cnt ltac:(lia)) in Qglob4.
(* ---- after fuzz_alloc_fail (0): 0x82790 ---- *)
pose proof HJ4 as (HAR4 & Hly4 & _ & _ & _ & Hfrs4 & Hnev4 & _).
pose proof Hly4 as (_ & _ & _ & _ & _ & EF4 & _).
assert (EA4 : frame_addr ly4 0 pos = F) by (unfold F, frame_addr; rewrite EF4; reflexivity).
assert (Hin4 : In (0, pos) (frames S4)) by (rewrite Hfrs4; left; reflexivity).
assert (CSD : crcs_csr regs (ms_regs msD) sp0 sp1 F)
  by exact (crcs_csr_run (w_H W3) regs regs3 ext _ msD sp0 sp1 F HSD CS3 ltac:(vm_compute; reflexivity)).
pose proof (crcs_csr_call regs (ms_regs msD) regs4 sp0 sp1 F HP4 CSD) as CS4.
pose proof CS4 as (C4_2 & C4_3 & C4_4 & C4_8 & C4_18 & C4_20 & C4_23 & C4_24 & C4_25 & C4_26 & C4_27).
pose proof HARU4 as (HAR4' & OK4 & PO4).
assert (HSf4 : st_ok tfibsegs (Ereg regs4 ext) (crcs_fs 0x82790 (crcs_fcs2 (2 ^ 64 - 1)))
  (restrict (w_H W4) (mkst regs4 (Z_to_bv 64 0x82790) mem4 (seg_rom tfibsegs)))).
{ apply (crcs_readd2 ly4 S4 U W4 md6 regs regs4 mem4 FL 0x82790 pos sp0 (2 ^ 64 - 1) HARU4 Hin4 HSr4);
    rewrite ?EA4; try assumption; try lia.
  - apply (crcs_val_keep_call B _ _ _ ly3 S3 U W3 (ms_mem msD) mdD ly4 S4 U W4 mem4 md6 0 0 pos (F + 32) 8 _ HJc4 HARUD OK4 PO4
      Hin3 ltac:(lia)); [rewrite EA3; lia | rewrite EA3; change (fs_frame_bytes 0) with 64; cbn; lia
      | intros x Hx; apply NFP; cbn in Hx; lia | exact VD32].
  - apply (crcs_val_keep_call B _ _ _ ly3 S3 U W3 (ms_mem msD) mdD ly4 S4 U W4 mem4 md6 0 0 pos (F + 56) 8 _ HJc4 HARUD OK4 PO4
      Hin3 ltac:(lia)); [rewrite EA3; lia | rewrite EA3; change (fs_frame_bytes 0) with 64; cbn; lia
      | intros x Hx; apply NFP; cbn in Hx; lia | exact VD56]. }
(* n's shadow byte across fuzz_alloc_fail (FP = the image statics, below the shadow) *)
assert (VDsh4 : val_mem tfibsegs (mrestrict (w_H W4) mem4) (shadow_addr F + 4) 1 0).
{ rewrite <- EA3. apply (crcs_sh_keep_call B _ _ _ ly3 S3 U W3 (ms_mem msD) mdD ly4 S4 U W4 mem4 md6 0 0 pos 4 0 HJc4 HARUD
    OK4 PO4 Hin3 ltac:(lia) ltac:(change (fs_frame_bytes 0 / 8) with 8; lia)); [|rewrite EA3; exact VDsh].
  intros Hf. pose proof (crcs_pstat_img _ Hf) as Hi. revert Hi. apply NIH.
  rewrite EA3. unfold FS_IMG_END, shadow_addr, SHADOW_OFF. lia. }
(* ... and back into the after-call state, at the frame's shadow region (atom 24) *)
assert (HSf4s : st_ok tfibsegs (Ereg regs4 ext) (crcs_fsS 0x82790 (crcs_fcs2 (2 ^ 64 - 1)) [crcs_nsh])
  (restrict (w_H W4) (mkst regs4 (Z_to_bv 64 0x82790) mem4 (seg_rom tfibsegs)))).
{ assert (Hadd : YN3u.add_chunk_sem (ss_mem (crcs_fs 0x82790 (crcs_fcs2 (2 ^ 64 - 1)))) (Some 24%nat) crcs_nsh
    = Some (ss_mem (crcs_fsS 0x82790 (crcs_fcs2 (2 ^ 64 - 1)) [crcs_nsh]), [])) by (vm_compute; reflexivity).
  pose proof (YN3u.st_ok_add_chunk_sem tfibsegs _ _ _ _ _ _ _ HSf4 Hadd) as HS'.
  apply HS'. intros _. cbn [base_val ms_mem restrict mkst]. unfold crcs_nsh.
  apply (chunk_ok_val tfibsegs _ _ _ 4 1 (SLit 0) 0); [| change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia |].
  - apply bv_eq. rewrite unsigned_lit_small by lia. change (bv_unsigned (sv_denot (Ereg regs4 ext) (SLit 0)))
      with (YP0e.U (Ereg regs4 ext) (SLit 0)). rewrite U_lit by lia. reflexivity.
  - rewrite (ew_Ereg_nat regs4 ext 24 24%bv eq_refl), C4_24, unsigned_lit_small by (unfold shadow_addr, SHADOW_OFF; lia).
    exact VDsh4. }
assert (Eab4 : ablocks B ly4 S4 = ablocks B ly S) by (rewrite Qab4, Qab; exact Eab2).
assert (RD21 : getr (ms_regs msD) 21%bv = getr regs3 21%bv)
  by exact (fsw_reg_atom (w_H W3) regs3 ext _ msD 21%bv 21%bv 21 HSD ltac:(vm_compute; reflexivity) eq_refl).
assert (RD19 : getr (ms_regs msD) 19%bv = getr regs3 19%bv)
  by exact (fsw_reg_atom (w_H W3) regs3 ext _ msD 19%bv 19%bv 19 HSD ltac:(vm_compute; reflexivity) eq_refl).
assert (RD22 : getr (ms_regs msD) 22%bv = getr regs3 10%bv)
  by exact (fsw_reg_atom (w_H W3) regs3 ext _ msD 22%bv 10%bv 10 HSD ltac:(vm_compute; reflexivity) eq_refl).
assert (R4_21 : getr regs4 21%bv = getr regs 10%bv) by (rewrite (fsw_pres _ _ 21%bv HP4 ltac:(crcs_cs)), RD21; exact R3_21).
assert (R4_19 : getr regs4 19%bv = getr regs 12%bv) by (rewrite (fsw_pres _ _ 19%bv HP4 ltac:(crcs_cs)), RD19; exact R3_19).
assert (R4_22 : getr regs4 22%bv = w64 live) by (rewrite (fsw_pres _ _ 22%bv HP4 ltac:(crcs_cs)), RD22; exact Q10).
assert (F32 : (F + 32) mod 8 = 0).
{ pose proof HFal as Hq. fold F in Hq. apply (Z.mod_divide _ 32 ltac:(lia)) in Hq as [q Hq].
  assert (F + 32 = (4 * q + 4) * 8) as -> by lia. apply Z.mod_mul. lia. }
(* ---- 0x82790 .. 0x82798: a0 := t (s5), a1 := &n (s7); jal preset_base64_decode (fs.c:214) ---- *)
let res := eval vm_compute in
  (sym_run_toN tfibsegs crcs_tbl FUEL A_preset_base64_decode (crcs_fsS 0x82790 (crcs_fcs2 (2 ^ 64 - 1)) [crcs_nsh])) in
lazymatch res with (?ssC, ?stC) =>
  apply (crcs_seg ly S U W mem md pos ly4 S4 W4 regs4 mem4 md6 (0 + 0 + 0) ext sp0 0x82790 (crcs_fcs2 (2 ^ 64 - 1))
    [crcs_nsh] (crcs_fsS 0x82790 (crcs_fcs2 (2 ^ 64 - 1)) [crcs_nsh]) A_preset_base64_decode ssC stC _ HSf4s eq_refl HJ4
    HARU4 C4_8
    ltac:(rewrite EA4; exact C4_25) ltac:(rewrite EA4; exact C4_24)
    ltac:(vm_compute; reflexivity) I)
end.
intros msE matE HSE HJE HARUE HIE.
set (mdE := with_vm_backing (m_vm_lazy md6) matE md6) in *.
assert (SDEC : STK_preset_base64_decode = 16544) by reflexivity.
destruct (crcs_site ly S U W mem md regs ch pos FL ly4 S4 W4 regs4 msE mdE (0 + 0 + 0) _ 0x8279c sp1
  STK_preset_base64_decode HPREU HTOP HRO0 HSE ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) C4_2 C4_3 C4_4 C4_8 ltac:(lia) Hm16 ltac:(lia) ltac:(vm_compute; reflexivity)
  ltac:(rewrite SDEC; lia) ltac:(rewrite SDEC; lia) HJE HARUE) as (HPREE & RE1 & RE8 & HspE & CsE & ExE).
assert (RE10 : getr (ms_regs msE) 10%bv = w64 t).
{ crcs_reg HSE (10%bv : bv 5). rewrite fsw_SOff0, (ew_Ereg_nat regs4 ext 21 21%bv eq_refl), R4_21. exact Ht. }
assert (RE11 : getr (ms_regs msE) 11%bv = w64 (F + 32)).
{ crcs_reg HSE (11%bv : bv 5). rewrite fsw_SOff0, (ew_Ereg_nat regs4 ext 23 23%bv eq_refl). exact C4_23. }
assert (GE : fs_glob tfibsegs W4 (ms_mem msE) live peak cnt cnt)
  by exact (crcs_glob_keep W4 mem4 (ms_mem msE) _ _ _ _ HIE Qglob4).
pose proof HARUE as (HARE & OKE & POE).
pose proof HJE as (_ & _ & _ & _ & _ & _ & HnevE & _).
assert (AROE : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W4) (ms_mem msE))).
{ apply (proj2 (crcs_aro_unp ly4 S4 U W4 (ms_mem msE) mdE HARUE)).
  eapply crcs_arodata_j; [exact HJE|]. apply (proj1 (crcs_aro_unp ly S U W mem md HARU0)). exact HRO0. }
assert (HkeptE : cstr_kept B ly4 S4 U t tb).
{ apply (cstr_kept_kept B ly S U ly4 S4 U t tb); [intros x Hx; rewrite Eab4; exact Hx | intros r Hr; left; exact Hr | exact Hkept]. }
assert (VE32 : val_mem tfibsegs (mrestrict (w_H W4) (ms_mem msE)) (F + 32) 8 (2 ^ 64 - 1)).
{ eapply (crcs_val_at (Ereg regs4 ext) _ (w_H W4) msE 0 _ _ _ _ _ _ 32 8%N (SLit (2 ^ 64 - 1)) (2 ^ 64 - 1) F);
    [exact HSE | reflexivity | cbn; repeat (first [left; reflexivity | right]) | | | |].
  - rewrite (ew_Ereg_nat regs4 ext 25 25%bv eq_refl), C4_25. apply unsigned_lit_small. lia.
  - apply bv_eq. rewrite unsigned_lit_small by lia. change (bv_unsigned (sv_denot (Ereg regs4 ext) (SLit (2 ^ 64 - 1))))
      with (YP0e.U (Ereg regs4 ext) (SLit (2 ^ 64 - 1))). rewrite U_lit by lia. reflexivity.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - cbn. lia. }
assert (VE56 : val_mem tfibsegs (mrestrict (w_H W4) (ms_mem msE)) (F + 56) 8 FL).
{ eapply (crcs_val_at (Ereg regs4 ext) _ (w_H W4) msE 0 _ _ _ _ _ _ 56 8%N (SOff 45 0) FL F);
    [exact HSE | reflexivity | cbn; repeat (first [left; reflexivity | right]) | | | |].
  - rewrite (ew_Ereg_nat regs4 ext 25 25%bv eq_refl), C4_25. apply unsigned_lit_small. lia.
  - change 45%nat with (32 + 13)%nat. rewrite fsw_SOff0, ew_Ereg_extra. reflexivity.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - cbn. lia. }
assert (VEsh : val_mem tfibsegs (mrestrict (w_H W4) (ms_mem msE)) (shadow_addr F + 4) 1 0).
{ eapply (crcs_val_at (Ereg regs4 ext) _ (w_H W4) msE 1 _ _ _ _ _ _ 4 1%N (SLit 0) 0 (shadow_addr F));
    [exact HSE | reflexivity | cbn; repeat (first [left; reflexivity | right]) | | | |].
  - rewrite (ew_Ereg_nat regs4 ext 24 24%bv eq_refl), C4_24. apply unsigned_lit_small. unfold shadow_addr, SHADOW_OFF; lia.
  - apply bv_eq. rewrite unsigned_lit_small by lia. change (bv_unsigned (sv_denot (Ereg regs4 ext) (SLit 0)))
      with (YP0e.U (Ereg regs4 ext) (SLit 0)). rewrite U_lit by lia. reflexivity.
  - change (2 ^ (8 * Z.of_N 1)) with 256. lia.
  - cbn. lia. }
assert (HSPE : SRr tfibsegs W4 (cfg_at tfibsegs A_preset_base64_decode (ms_regs msE) (ms_mem msE) mdE)
  (@fpostU fx rc SK tfibsegs B STK_preset_base64_decode (spZ (ms_regs msE)) (FS_PSTAT_FP ++ [(F + 32, F + 32 + 8)]) (ms_regs msE)
     ly4 S4 U W4 (ms_mem msE) mdE 0 U
     (fun ly' S' W' regs' mem' md' => getr regs' 10 = w64 0 /\ ablocks B ly' S' = ablocks B ly4 S4 /\
        val_mem tfibsegs (mrestrict (w_H W') mem') (F + 32) 8 (2 ^ 64 - 1) /\
        fs_glob tfibsegs W' mem' live peak ((cnt + 1) mod 2 ^ 64) SIZE_MAXZ))).
{ eapply SRr_mono; [apply (DEC ly4 S4 U W4 (ms_regs msE) (ms_mem msE) mdE ch1 t (F + 32) tb live peak cnt cnt (2 ^ 64 - 1))|].
  - exact HPREE.
  - exact Qheads4.
  - rewrite Hfrs4. exact (crcs_frames_callee (0, pos) (frames S) HFRL).
  - exact RE10.
  - exact RE11.
  - apply (cstr_ok_keptU B _ _ FS_PSTAT_FP ly S U W mem md [(0, pos)] ly4 S4 U W4 (ms_mem msE) mdE _ t tb IMG HARU0 HJE OKE POE).
    + intros x Hx. rewrite Eab4. exact Hx.
    + exact crcs_pstat_img.
    + exact AROE.
    + exact Hkept.
    + intros r Hr. left. exact Hr.
    + exact Hcstr.
  - exact (crcs_wsrc_keep _ _ FS_PSTAT_FP ly S U W mem md [(0, pos)] ly4 S4 W4 (ms_mem msE) mdE _ 0 t (tb ++ [0])
      HJE HARU0 HARUE Eab4 crcs_pstat_img HWS).
  - exact Hbytes.
  - unfold PRESET_FILE_MAX_BYTES in Htb. lia.
  - exact F32.
  - exists 0, pos. split; [exact Hin4|]. intros a Ha. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EA4.
    change (fs_frame_bytes 0) with 64. lia.
  - destruct (al_frames _ _ LAWS ly4 S4 W4 (unpoison U (ms_mem msE)) mdE 0 pos HARE Hin4) as (_ & _ & HfpE & _).
    intros a Ha. rewrite EA4 in HfpE. change (fs_frame_bytes 0) with 64 in HfpE. destruct (HfpE a ltac:(lia)) as (Hp & Hno).
    exact (fsw_apresent_notowned B ly4 S4 U W4 (ms_mem msE) mdE a HARUE ltac:(lia) Hno Hp).
  - apply (crcs_shadow_addressable W4 (ms_mem msE) F ltac:(fold F in HFal; exact HFal) ltac:(lia) VEsh).
  - exact VE32.
  - lia.
  - destruct (Z_le_gt_dec (F + 32 + 8) t) as [Hle|Hgt]; [left; exact Hle|]. right.
    destruct (Z_le_gt_dec (t + Z.of_nat (length tb) + 1) (F + 32)) as [Hle2|Hgt2]; [exact Hle2|]. exfalso.
    apply (crcs_text_nf ly4 S4 U W4 (unpoison U (ms_mem msE)) mdE t tb 0 pos HARE
      (proj1 (crcs_aro_unp ly4 S4 U W4 (ms_mem msE) mdE HARUE) AROE) HkeptE Hin4 (Z.max t (F + 32))); [lia|].
    rewrite EA4. change (fs_frame_bytes 0) with 64. lia.
  - exact GE.
  - pose proof HJE as (_ & _ & _ & _ & _ & _ & HnevE' & _). unfold EV_preset_base64_encode in Hev.
    pose proof (crcs_ev_nonneg tb). lia.
  - rewrite (blocks_bytes_bsum B ly4 S4), Eab4, <- (blocks_bytes_bsum B ly S). exact Hbb.
  - exact Hlive.
  - lia.
  - intros W' c' _ [[_ HP] | [[Hne _] | (q & out & Hne & _)]]; [exact HP | exfalso; exact (Hne eq_refl) | exfalso; exact (Hne eq_refl)]. }
refine (crcs_call STK_check_reject_clean_starved sp0 FS_PSTAT_FP ly S U W mem md [(0, pos)] ly4 S4 W4 msE mdE (0 + 0 + 0)
  (Ereg regs4 ext) _ STK_preset_base64_decode (FS_PSTAT_FP ++ [(F + 32, F + 32 + 8)]) 0 _ _ ext 0x8279c HSE eq_refl HJE HARUE
  HSPE _ RE1 RE8 ltac:(rewrite HspE, SDEC; lia) ltac:(rewrite HspE; lia) ltac:(lia) CsE ExE _).
{ intros a (r & Hr & H1 & H2). apply in_app_or in Hr. destruct Hr as [Hr|Hr].
  - right; right; left. split; [exists r; split; [exact Hr | lia]|]. exact (crcs_pstat_img a (ex_intro _ r (conj Hr (conj H1 H2)))).
  - right; right; right. destruct Hr as [<-|[]]. cbn [fst snd] in H1, H2. apply crcs_in_fr. rewrite EA4. lia. }
intros ly5 S5 W5 regs5 mem5 md7 (Q10e & QabE & QvE & QglobE) HP5 HJc5 HJ5 HARU5 HSr5.
rewrite (crcs_tick cnt ltac:(lia) ltac:(lia)) in QglobE.
(* ---- after preset_base64_decode (refused): 0x8279c ---- *)
pose proof HJ5 as (HAR5 & Hly5 & _ & _ & _ & Hfrs5 & Hnev5 & _).
pose proof Hly5 as (_ & _ & _ & _ & _ & EF5 & _).
assert (EA5 : frame_addr ly5 0 pos = F) by (unfold F, frame_addr; rewrite EF5; reflexivity).
assert (Hin5 : In (0, pos) (frames S5)) by (rewrite Hfrs5; left; reflexivity).
assert (CSE : crcs_csr regs (ms_regs msE) sp0 sp1 F)
  by exact (crcs_csr_run (w_H W4) regs regs4 ext _ msE sp0 sp1 F HSE CS4 ltac:(vm_compute; reflexivity)).
pose proof (crcs_csr_call regs (ms_regs msE) regs5 sp0 sp1 F HP5 CSE) as CS5.
pose proof CS5 as (C5_2 & C5_3 & C5_4 & C5_8 & C5_18 & C5_20 & C5_23 & C5_24 & C5_25 & C5_26 & C5_27).
assert (R5_19 : getr regs5 19%bv = getr regs 12%bv).
{ rewrite (fsw_pres _ _ 19%bv HP5 ltac:(crcs_cs)).
  rewrite (fsw_reg_atom (w_H W4) regs4 ext _ msE 19%bv 19%bv 19 HSE ltac:(vm_compute; reflexivity) eq_refl). exact R4_19. }
assert (R5_22 : getr regs5 22%bv = w64 live).
{ rewrite (fsw_pres _ _ 22%bv HP5 ltac:(crcs_cs)).
  rewrite (fsw_reg_atom (w_H W4) regs4 ext _ msE 22%bv 22%bv 22 HSE ltac:(vm_compute; reflexivity) eq_refl). exact R4_22. }
pose proof HARU5 as (HAR5' & OK5 & PO5).
assert (Eab5 : ablocks B ly5 S5 = ablocks B ly S) by (rewrite QabE; exact Eab4).
assert (NFPd : forall x, F + 56 <= x < F + 64 -> ~ inFP (FS_PSTAT_FP ++ [(F + 32, F + 32 + 8)]) x).
{ intros x Hx (r & Hr & H1 & H2). apply in_app_or in Hr. destruct Hr as [Hr|Hr].
  - exact (NFP x ltac:(lia) (ex_intro _ r (conj Hr (conj H1 H2)))).
  - destruct Hr as [<-|[]]. cbn [fst snd] in H1, H2. lia. }
assert (HSf5 : st_ok tfibsegs (Ereg regs5 ext) (crcs_fs 0x8279c (crcs_fcs2 (2 ^ 64 - 1)))
  (restrict (w_H W5) (mkst regs5 (Z_to_bv 64 0x8279c) mem5 (seg_rom tfibsegs)))).
{ apply (crcs_readd2 ly5 S5 U W5 md7 regs regs5 mem5 FL 0x8279c pos sp0 (2 ^ 64 - 1) HARU5 Hin5 HSr5);
    rewrite ?EA5; try assumption; try lia.
  apply (crcs_val_keep_call B _ _ _ ly4 S4 U W4 (ms_mem msE) mdE ly5 S5 U W5 mem5 md7 0 0 pos (F + 56) 8 _ HJc5 HARUE OK5 PO5
    Hin4 ltac:(lia)); [rewrite EA4; lia | rewrite EA4; change (fs_frame_bytes 0) with 64; cbn; lia
    | intros x Hx; apply NFPd; cbn in Hx; lia | exact VE56]. }
(* ---- 0x8279c .. 0x827a4: s5 := 0 (decode's NULL), a0 := SIZE_MAX; jal fuzz_alloc_fail (SIZE_MAX) (fs.c:215) ---- *)
let res := eval vm_compute in
  (sym_run_toN tfibsegs crcs_tbl FUEL A_fuzz_alloc_fail (crcs_fs 0x8279c (crcs_fcs2 (2 ^ 64 - 1)))) in
lazymatch res with (?ssC, ?stC) =>
  apply (crcs_seg ly S U W mem md pos ly5 S5 W5 regs5 mem5 md7 (0 + 0 + 0 + 0) ext sp0 0x8279c (crcs_fcs2 (2 ^ 64 - 1)) []
    (crcs_fs 0x8279c (crcs_fcs2 (2 ^ 64 - 1))) A_fuzz_alloc_fail ssC stC _ HSf5 eq_refl HJ5 HARU5 C5_8
    ltac:(rewrite EA5; exact C5_25) ltac:(rewrite EA5; exact C5_24)
    ltac:(vm_compute; reflexivity) I)
end.
intros msF matF HSF HJF HARUF HIF.
set (mdF := with_vm_backing (m_vm_lazy md7) matF md7) in *.
destruct (crcs_site ly S U W mem md regs ch pos FL ly5 S5 W5 regs5 msF mdF (0 + 0 + 0 + 0) _ 0x827a8 sp1 STK_fuzz_alloc
  HPREU HTOP HRO0 HSF ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) C5_2 C5_3 C5_4 C5_8
  ltac:(lia) Hm16 ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(change STK_fuzz_alloc with 0; lia)
  ltac:(change STK_fuzz_alloc with 0; lia) HJF HARUF) as (HPREF & RF1 & RF8 & HspF & CsF & ExF).
assert (RF10 : getr (ms_regs msF) 10%bv = w64 SIZE_MAXZ)
  by exact (fsw_reg_lit (w_H W5) _ _ msF 10%bv SIZE_MAXZ HSF ltac:(vm_compute; reflexivity) ltac:(unfold SIZE_MAXZ; lia)).
assert (RF21 : getr (ms_regs msF) 21%bv = w64 0).
{ crcs_reg HSF (21%bv : bv 5). rewrite fsw_SOff0, (ew_Ereg_nat regs5 ext 10 10%bv eq_refl). exact Q10e. }
assert (GF : fs_glob tfibsegs W5 (ms_mem msF) live peak (cnt + 1) SIZE_MAXZ)
  by exact (crcs_glob_keep W5 mem5 (ms_mem msF) _ _ _ _ HIF QglobE).
pose proof (crcs_heads B ly S ly5 S5 U Eab5 HHEADS) as Hheads5.
assert (VF32 : val_mem tfibsegs (mrestrict (w_H W5) (ms_mem msF)) (F + 32) 8 (2 ^ 64 - 1)).
{ eapply (crcs_val_at (Ereg regs5 ext) _ (w_H W5) msF 0 _ _ _ _ _ _ 32 8%N (SLit (2 ^ 64 - 1)) (2 ^ 64 - 1) F);
    [exact HSF | reflexivity | cbn; repeat (first [left; reflexivity | right]) | | | |].
  - rewrite (ew_Ereg_nat regs5 ext 25 25%bv eq_refl), C5_25. apply unsigned_lit_small. lia.
  - apply bv_eq. rewrite unsigned_lit_small by lia. change (bv_unsigned (sv_denot (Ereg regs5 ext) (SLit (2 ^ 64 - 1))))
      with (YP0e.U (Ereg regs5 ext) (SLit (2 ^ 64 - 1))). rewrite U_lit by lia. reflexivity.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - cbn. lia. }
assert (VF56 : val_mem tfibsegs (mrestrict (w_H W5) (ms_mem msF)) (F + 56) 8 FL).
{ eapply (crcs_val_at (Ereg regs5 ext) _ (w_H W5) msF 0 _ _ _ _ _ _ 56 8%N (SOff 45 0) FL F);
    [exact HSF | reflexivity | cbn; repeat (first [left; reflexivity | right]) | | | |].
  - rewrite (ew_Ereg_nat regs5 ext 25 25%bv eq_refl), C5_25. apply unsigned_lit_small. lia.
  - change 45%nat with (32 + 13)%nat. rewrite fsw_SOff0, ew_Ereg_extra. reflexivity.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - cbn. lia. }
refine (crcs_call STK_check_reject_clean_starved sp0 FS_PSTAT_FP ly S U W mem md [(0, pos)] ly5 S5 W5 msF mdF (0 + 0 + 0 + 0)
  (Ereg regs5 ext) _ STK_fuzz_alloc FS_PSTAT_FP 0 _ _ ext 0x827a8 HSF eq_refl HJF HARUF
  (FAIL ly5 S5 U W5 (ms_regs msF) (ms_mem msF) mdF ch1 live peak (cnt + 1) SIZE_MAXZ SIZE_MAXZ HPREF Hheads5 GF RF10
    ltac:(unfold SIZE_MAXZ; lia))
  ltac:(intros a Ha; right; right; left; split; [exact Ha | exact (crcs_pstat_img a Ha)]) RF1 RF8
  ltac:(rewrite HspF; change STK_fuzz_alloc with 0; lia) ltac:(rewrite HspF; lia) ltac:(lia) CsF ExF _).
intros ly6 S6 W6 regs6 mem6 md8 (Qab6 & Qheads6 & Qglob6) HP6 HJc6 HJ6 HARU6 HSr6.
rewrite (crcs_failmax (cnt + 1) ltac:(lia)) in Qglob6.
(* ---- after fuzz_alloc_fail (SIZE_MAX): 0x827a8 ---- *)
pose proof HJ6 as (HAR6 & Hly6 & _ & _ & _ & Hfrs6 & Hnev6 & _).
pose proof Hly6 as (_ & _ & _ & _ & _ & EF6 & _).
assert (EA6 : frame_addr ly6 0 pos = F) by (unfold F, frame_addr; rewrite EF6; reflexivity).
assert (Hin6 : In (0, pos) (frames S6)) by (rewrite Hfrs6; left; reflexivity).
assert (CSF : crcs_csr regs (ms_regs msF) sp0 sp1 F)
  by exact (crcs_csr_run (w_H W5) regs regs5 ext _ msF sp0 sp1 F HSF CS5 ltac:(vm_compute; reflexivity)).
pose proof (crcs_csr_call regs (ms_regs msF) regs6 sp0 sp1 F HP6 CSF) as CS6.
pose proof CS6 as (C6_2 & C6_3 & C6_4 & C6_8 & C6_18 & C6_20 & C6_23 & C6_24 & C6_25 & C6_26 & C6_27).
assert (R6_19 : getr regs6 19%bv = getr regs 12%bv).
{ rewrite (fsw_pres _ _ 19%bv HP6 ltac:(crcs_cs)).
  rewrite (fsw_reg_atom (w_H W5) regs5 ext _ msF 19%bv 19%bv 19 HSF ltac:(vm_compute; reflexivity) eq_refl). exact R5_19. }
assert (R6_22 : getr regs6 22%bv = w64 live).
{ rewrite (fsw_pres _ _ 22%bv HP6 ltac:(crcs_cs)).
  rewrite (fsw_reg_atom (w_H W5) regs5 ext _ msF 22%bv 22%bv 22 HSF ltac:(vm_compute; reflexivity) eq_refl). exact R5_22. }
assert (R6_21 : getr regs6 21%bv = w64 0) by (rewrite (fsw_pres _ _ 21%bv HP6 ltac:(crcs_cs)); exact RF21).
pose proof HARU6 as (HAR6' & OK6 & PO6).
assert (Eab6 : ablocks B ly6 S6 = ablocks B ly S) by (rewrite Qab6; exact Eab5).
assert (HSf6 : st_ok tfibsegs (Ereg regs6 ext) (crcs_fs 0x827a8 (crcs_fcs2 (2 ^ 64 - 1)))
  (restrict (w_H W6) (mkst regs6 (Z_to_bv 64 0x827a8) mem6 (seg_rom tfibsegs)))).
{ apply (crcs_readd2 ly6 S6 U W6 md8 regs regs6 mem6 FL 0x827a8 pos sp0 (2 ^ 64 - 1) HARU6 Hin6 HSr6);
    rewrite ?EA6; try assumption; try lia.
  - apply (crcs_val_keep_call B _ _ _ ly5 S5 U W5 (ms_mem msF) mdF ly6 S6 U W6 mem6 md8 0 0 pos (F + 32) 8 _ HJc6 HARUF OK6 PO6
      Hin5 ltac:(lia)); [rewrite EA5; lia | rewrite EA5; change (fs_frame_bytes 0) with 64; cbn; lia
      | intros x Hx; apply NFP; cbn in Hx; lia | exact VF32].
  - apply (crcs_val_keep_call B _ _ _ ly5 S5 U W5 (ms_mem msF) mdF ly6 S6 U W6 mem6 md8 0 0 pos (F + 56) 8 _ HJc6 HARUF OK6 PO6
      Hin5 ltac:(lia)); [rewrite EA5; lia | rewrite EA5; change (fs_frame_bytes 0) with 64; cbn; lia
      | intros x Hx; apply NFP; cbn in Hx; lia | exact VF56]. }
(* ---- 0x827a8 .. 0x827b4: a1 := n (SIZE_MAX), a0 := s5 (NULL), a2 := s6 (live); jal check_reject_clean (fs.c:216) ---- *)
let res := eval vm_compute in
  (sym_run_toN tfibsegs crcs_tbl FUEL A_check_reject_clean (crcs_fs 0x827a8 (crcs_fcs2 (2 ^ 64 - 1)))) in
lazymatch res with (?ssC, ?stC) =>
  apply (crcs_seg ly S U W mem md pos ly6 S6 W6 regs6 mem6 md8 (0 + 0 + 0 + 0 + 0) ext sp0 0x827a8 (crcs_fcs2 (2 ^ 64 - 1)) []
    (crcs_fs 0x827a8 (crcs_fcs2 (2 ^ 64 - 1))) A_check_reject_clean ssC stC _ HSf6 eq_refl HJ6 HARU6 C6_8
    ltac:(rewrite EA6; exact C6_25) ltac:(rewrite EA6; exact C6_24)
    ltac:(vm_compute; reflexivity) I)
end.
intros msG matG HSG HJG HARUG HIG.
set (mdG := with_vm_backing (m_vm_lazy md8) matG md8) in *.
destruct (crcs_site ly S U W mem md regs ch pos FL ly6 S6 W6 regs6 msG mdG (0 + 0 + 0 + 0 + 0) _ 0x827b8 sp1
  STK_check_reject_clean HPREU HTOP HRO0 HSG ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) C6_2 C6_3 C6_4 C6_8 ltac:(lia) Hm16 ltac:(lia) ltac:(vm_compute; reflexivity)
  ltac:(change STK_check_reject_clean with 16; lia) ltac:(change STK_check_reject_clean with 16; lia) HJG HARUG)
  as (HPREG & RG1 & RG8 & HspG & CsG & ExG).
assert (RG10 : getr (ms_regs msG) 10%bv = w64 0).
{ crcs_reg HSG (10%bv : bv 5). rewrite fsw_SOff0, (ew_Ereg_nat regs6 ext 21 21%bv eq_refl). exact R6_21. }
assert (RG11 : getr (ms_regs msG) 11%bv = w64 SIZE_MAXZ)
  by exact (fsw_reg_lit (w_H W6) _ _ msG 11%bv SIZE_MAXZ HSG ltac:(vm_compute; reflexivity) ltac:(unfold SIZE_MAXZ; lia)).
assert (RG12 : getr (ms_regs msG) 12%bv = w64 live).
{ crcs_reg HSG (12%bv : bv 5). rewrite fsw_SOff0, (ew_Ereg_nat regs6 ext 22 22%bv eq_refl). exact R6_22. }
assert (GG : fs_glob tfibsegs W6 (ms_mem msG) live peak (cnt + 1) SIZE_MAXZ)
  by exact (crcs_glob_keep W6 mem6 (ms_mem msG) _ _ _ _ HIG Qglob6).
refine (crcs_call STK_check_reject_clean_starved sp0 FS_PSTAT_FP ly S U W mem md [(0, pos)] ly6 S6 W6 msG mdG
  (0 + 0 + 0 + 0 + 0) (Ereg regs6 ext) _ STK_check_reject_clean [] 0 _ _ ext 0x827b8 HSG eq_refl HJG HARUG
  (CRC ly6 S6 U W6 (ms_regs msG) (ms_mem msG) mdG ch1 live peak (cnt + 1) SIZE_MAXZ HPREG Qheads6 GG RG10 RG11 RG12)
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) RG1 RG8
  ltac:(rewrite HspG; change STK_check_reject_clean with 16; lia) ltac:(rewrite HspG; lia) ltac:(lia) CsG ExG _).
intros ly7 S7 W7 regs7 mem7 md9 (Qab7 & Qglob7) HP7 HJc7 HJ7 HARU7 HSr7.
(* ---- after check_reject_clean: 0x827b8 ---- *)
assert (VG32 : val_mem tfibsegs (mrestrict (w_H W6) (ms_mem msG)) (F + 32) 8 (2 ^ 64 - 1)).
{ eapply (crcs_val_at (Ereg regs6 ext) _ (w_H W6) msG 0 _ _ _ _ _ _ 32 8%N (SLit (2 ^ 64 - 1)) (2 ^ 64 - 1) F);
    [exact HSG | reflexivity | cbn; repeat (first [left; reflexivity | right]) | | | |].
  - rewrite (ew_Ereg_nat regs6 ext 25 25%bv eq_refl), C6_25. apply unsigned_lit_small. lia.
  - apply bv_eq. rewrite unsigned_lit_small by lia. change (bv_unsigned (sv_denot (Ereg regs6 ext) (SLit (2 ^ 64 - 1))))
      with (YP0e.U (Ereg regs6 ext) (SLit (2 ^ 64 - 1))). rewrite U_lit by lia. reflexivity.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - cbn. lia. }
assert (VG56 : val_mem tfibsegs (mrestrict (w_H W6) (ms_mem msG)) (F + 56) 8 FL).
{ eapply (crcs_val_at (Ereg regs6 ext) _ (w_H W6) msG 0 _ _ _ _ _ _ 56 8%N (SOff 45 0) FL F);
    [exact HSG | reflexivity | cbn; repeat (first [left; reflexivity | right]) | | | |].
  - rewrite (ew_Ereg_nat regs6 ext 25 25%bv eq_refl), C6_25. apply unsigned_lit_small. lia.
  - change 45%nat with (32 + 13)%nat. rewrite fsw_SOff0, ew_Ereg_extra. reflexivity.
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - cbn. lia. }
pose proof HJ7 as (HAR7 & Hly7 & _ & _ & _ & Hfrs7 & Hnev7 & _).
pose proof Hly7 as (_ & _ & _ & _ & _ & EF7 & _).
assert (EA7 : frame_addr ly7 0 pos = F) by (unfold F, frame_addr; rewrite EF7; reflexivity).
assert (EFL7 : FL = flag_addr ly7 0 pos) by (unfold FL, flag_addr; rewrite EF7; reflexivity).
assert (Hin7 : In (0, pos) (frames S7)) by (rewrite Hfrs7; left; reflexivity).
assert (CSG : crcs_csr regs (ms_regs msG) sp0 sp1 F)
  by exact (crcs_csr_run (w_H W6) regs regs6 ext _ msG sp0 sp1 F HSG CS6 ltac:(vm_compute; reflexivity)).
pose proof (crcs_csr_call regs (ms_regs msG) regs7 sp0 sp1 F HP7 CSG) as CS7.
pose proof CS7 as (C7_2 & C7_3 & C7_4 & C7_8 & C7_18 & C7_20 & C7_23 & C7_24 & C7_25 & C7_26 & C7_27).
assert (R7_19 : getr regs7 19%bv = getr regs 12%bv).
{ rewrite (fsw_pres _ _ 19%bv HP7 ltac:(crcs_cs)).
  rewrite (fsw_reg_atom (w_H W6) regs6 ext _ msG 19%bv 19%bv 19 HSG ltac:(vm_compute; reflexivity) eq_refl). exact R6_19. }
assert (R7_22 : getr regs7 22%bv = w64 live).
{ rewrite (fsw_pres _ _ 22%bv HP7 ltac:(crcs_cs)).
  rewrite (fsw_reg_atom (w_H W6) regs6 ext _ msG 22%bv 22%bv 22 HSG ltac:(vm_compute; reflexivity) eq_refl). exact R6_22. }
pose proof HARU7 as (HAR7' & OK7 & PO7).
assert (Eab7 : ablocks B ly7 S7 = ablocks B ly S) by (rewrite Qab7; exact Eab6).
pose proof (crcs_heads B ly S ly7 S7 U Eab7 HHEADS) as Hheads7.
assert (HSf7 : st_ok tfibsegs (Ereg regs7 ext) (crcs_fs 0x827b8 (crcs_fcs2 (2 ^ 64 - 1)))
  (restrict (w_H W7) (mkst regs7 (Z_to_bv 64 0x827b8) mem7 (seg_rom tfibsegs)))).
{ apply (crcs_readd2 ly7 S7 U W7 md9 regs regs7 mem7 FL 0x827b8 pos sp0 (2 ^ 64 - 1) HARU7 Hin7 HSr7);
    rewrite ?EA7; try assumption; try lia.
  - apply (crcs_val_keep_call B _ _ _ ly6 S6 U W6 (ms_mem msG) mdG ly7 S7 U W7 mem7 md9 0 0 pos (F + 32) 8 _ HJc7 HARUG OK7
      PO7 Hin6 ltac:(lia)); [rewrite EA6; lia | rewrite EA6; change (fs_frame_bytes 0) with 64; cbn; lia
      | intros x _ Hx; exact (inFP_nil x Hx) | exact VG32].
  - apply (crcs_val_keep_call B _ _ _ ly6 S6 U W6 (ms_mem msG) mdG ly7 S7 U W7 mem7 md9 0 0 pos (F + 56) 8 _ HJc7 HARUG OK7
      PO7 Hin6 ltac:(lia)); [rewrite EA6; lia | rewrite EA6; change (fs_frame_bytes 0) with 64; cbn; lia
      | intros x _ Hx; exact (inFP_nil x Hx) | exact VG56]. }
(* sp1 in the epilogue's form *)
assert (Esp1e : spZ regs - 128 - (spZ regs - 128) mod 32 = sp1) by (unfold sp1; rewrite (Z.mod_eq _ 32) by lia; lia).
assert (RG20 : getr regs7 20%bv = w64 bd) by (rewrite C7_20; exact Hbd).
destruct (Z.eqb_spec bd 0) as [Hbd0 | Hbd0].
- (* ---- bd = NULL: `beqz s4` (0x827b8) is taken, the epilogue; fuzz_alloc_fail (SIZE_MAX) was the last tick ---- *)
  subst bd.
  assert (HS80 : st_ok tfibsegs (Ereg regs7 ext)
    (add_cond (crcs_fs 0x827b8 (crcs_fcs2 (2 ^ 64 - 1))) (mkAC BC_EQ (SOff 20 0) (SLit 0)))
    (restrict (w_H W7) (mkst regs7 (Z_to_bv 64 0x827b8) mem7 (seg_rom tfibsegs)))).
  { apply (st_ok_add_cond tfibsegs _ _ _ BC_EQ (SOff 20 0) (SLit 0) HSf7).
    rewrite branch_eq_U, (U_atom (Ereg regs7 ext) 20 0 ltac:(rewrite (ew_Ereg_nat regs7 ext 20 20%bv eq_refl); exact RG20)
      ltac:(lia)), U_SLit.
    reflexivity. }
  let res := eval vm_compute in (sym_runN tfibsegs crcs_tbl FUEL
    (crcs_epi_ss (add_cond (crcs_fs 0x827b8 (crcs_fcs2 (2 ^ 64 - 1))) (mkAC BC_EQ (SOff 20 0) (SLit 0))))) in
  lazymatch res with (?ssR, ?stR) =>
    exact (crcs_epi ly S U W mem md regs pos FL ly7 S7 W7 regs7 (mkst regs7 (Z_to_bv 64 0x827b8) mem7 (seg_rom tfibsegs)) md9
      (0 + 0 + 0 + 0 + 0 + 0) (add_cond (crcs_fs 0x827b8 (crcs_fcs2 (2 ^ 64 - 1))) (mkAC BC_EQ (SOff 20 0) (SLit 0)))
      ssR stR live peak (cnt + 1) (or_intror I) Hra0 HS80 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) I
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(rewrite Esp1e, EA7; exact CS7) EFL7 HJ7 HARU7 Eab7 Qglob7)
  end.
- (* ---- bd <> NULL: fs.c:219-222, fuzz_alloc_fail (0), preset_base64_encode (bd, l) refused, fuzz_alloc_fail
     (SIZE_MAX), `bnez s3` dead, fuzz_alloc_live, `bne a0, s6` dead, the epilogue ---- *)
  replace (cnt + 2) with (cnt + 1 + 1) by lia.
  destruct (crcs_body B ly S U W mem tb bd l Hcaw Hbd0 Htb)
    as (bs & m & Hbs & Hlen & Hl0 & Hl27 & Hz & Hbd4096 & Hbdc & Hrb & Hlm).
  destruct (Henc Hbd0) as (HbbE & HliveE).
  assert (HS7c : st_ok tfibsegs (Ereg regs7 ext)
    (add_cond (crcs_fs 0x827b8 (crcs_fcs2 (2 ^ 64 - 1))) (mkAC BC_NE (SOff 20 0) (SLit 0)))
    (restrict (w_H W7) (mkst regs7 (Z_to_bv 64 0x827b8) mem7 (seg_rom tfibsegs)))).
  { apply (st_ok_add_cond tfibsegs _ _ _ BC_NE (SOff 20 0) (SLit 0) HSf7).
    rewrite branch_ne_U, (U_atom (Ereg regs7 ext) 20 bd ltac:(rewrite (ew_Ereg_nat regs7 ext 20 20%bv eq_refl); exact RG20)
      ltac:(lia)), U_SLit.
    change (zcanon 0) with 0. apply Bool.negb_true_iff. apply Z.eqb_neq. exact Hbd0. }
  (* ---- 0x827b8 .. 0x827c0: a0 := 0; jal fuzz_alloc_fail (0) (fs.c:219) ---- *)
  let res := eval vm_compute in (sym_run_toN tfibsegs crcs_tbl FUEL A_fuzz_alloc_fail
    (add_cond (crcs_fs 0x827b8 (crcs_fcs2 (2 ^ 64 - 1))) (mkAC BC_NE (SOff 20 0) (SLit 0)))) in
  lazymatch res with (?ssC, ?stC) =>
    apply (crcs_seg ly S U W mem md pos ly7 S7 W7 regs7 mem7 md9 (0 + 0 + 0 + 0 + 0 + 0) ext sp0 0x827b8
      (crcs_fcs2 (2 ^ 64 - 1)) [] (add_cond (crcs_fs 0x827b8 (crcs_fcs2 (2 ^ 64 - 1))) (mkAC BC_NE (SOff 20 0) (SLit 0)))
      A_fuzz_alloc_fail ssC stC _ HS7c eq_refl HJ7 HARU7 C7_8 ltac:(rewrite EA7; exact C7_25)
      ltac:(rewrite EA7; exact C7_24) ltac:(vm_compute; reflexivity) I)
  end.
  intros msH matH HSH HJH HARUH HIH.
  set (mdH := with_vm_backing (m_vm_lazy md9) matH md9) in *.
  destruct (crcs_site ly S U W mem md regs ch pos FL ly7 S7 W7 regs7 msH mdH (0 + 0 + 0 + 0 + 0 + 0) _ 0x827c4 sp1
    STK_fuzz_alloc HPREU HTOP HRO0 HSH ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) C7_2 C7_3 C7_4 C7_8 ltac:(lia) Hm16 ltac:(lia) ltac:(vm_compute; reflexivity)
    ltac:(change STK_fuzz_alloc with 0; lia) ltac:(change STK_fuzz_alloc with 0; lia) HJH HARUH)
    as (HPREH & RH1 & RH8 & HspH & CsH & ExH).
  assert (RH10 : getr (ms_regs msH) 10%bv = w64 0)
    by exact (fsw_reg_lit (w_H W7) _ _ msH 10%bv 0 HSH ltac:(vm_compute; reflexivity) ltac:(lia)).
  assert (GH : fs_glob tfibsegs W7 (ms_mem msH) live peak (cnt + 1) SIZE_MAXZ)
    by exact (crcs_glob_keep W7 mem7 (ms_mem msH) _ _ _ _ HIH Qglob7).
  assert (VH32 : val_mem tfibsegs (mrestrict (w_H W7) (ms_mem msH)) (F + 32) 8 (2 ^ 64 - 1)).
  { eapply (crcs_val_at (Ereg regs7 ext) _ (w_H W7) msH 0 _ _ _ _ _ _ 32 8%N (SLit (2 ^ 64 - 1)) (2 ^ 64 - 1) F);
      [exact HSH | reflexivity | cbn; repeat (first [left; reflexivity | right]) | | | |].
    - rewrite (ew_Ereg_nat regs7 ext 25 25%bv eq_refl), C7_25. apply unsigned_lit_small. lia.
    - apply bv_eq. rewrite unsigned_lit_small by lia. change (bv_unsigned (sv_denot (Ereg regs7 ext) (SLit (2 ^ 64 - 1))))
        with (YP0e.U (Ereg regs7 ext) (SLit (2 ^ 64 - 1))). rewrite U_lit by lia. reflexivity.
    - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    - cbn. lia. }
  assert (VH56 : val_mem tfibsegs (mrestrict (w_H W7) (ms_mem msH)) (F + 56) 8 FL).
  { eapply (crcs_val_at (Ereg regs7 ext) _ (w_H W7) msH 0 _ _ _ _ _ _ 56 8%N (SOff 45 0) FL F);
      [exact HSH | reflexivity | cbn; repeat (first [left; reflexivity | right]) | | | |].
    - rewrite (ew_Ereg_nat regs7 ext 25 25%bv eq_refl), C7_25. apply unsigned_lit_small. lia.
    - change 45%nat with (32 + 13)%nat. rewrite fsw_SOff0, ew_Ereg_extra. reflexivity.
    - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    - cbn. lia. }
  refine (crcs_call STK_check_reject_clean_starved sp0 FS_PSTAT_FP ly S U W mem md [(0, pos)] ly7 S7 W7 msH mdH
    (0 + 0 + 0 + 0 + 0 + 0) (Ereg regs7 ext) _ STK_fuzz_alloc FS_PSTAT_FP 0 _ _ ext 0x827c4 HSH eq_refl HJH HARUH
    (FAIL ly7 S7 U W7 (ms_regs msH) (ms_mem msH) mdH ch1 live peak (cnt + 1) SIZE_MAXZ 0 HPREH Hheads7 GH RH10 ltac:(lia))
    ltac:(intros a Ha; right; right; left; split; [exact Ha | exact (crcs_pstat_img a Ha)]) RH1 RH8
    ltac:(rewrite HspH; change STK_fuzz_alloc with 0; lia) ltac:(rewrite HspH; lia) ltac:(lia) CsH ExH _).
  intros ly8 S8 W8 regs8 mem8 md10 (Qab8 & Qheads8 & Qglob8) HP8 HJc8 HJ8 HARU8 HSr8.
  rewrite (crcs_fail0 (cnt + 1) ltac:(lia)) in Qglob8.
  (* ---- after fuzz_alloc_fail (0): 0x827c4 ---- *)
  pose proof HJ8 as (HAR8 & Hly8 & _ & _ & _ & Hfrs8 & Hnev8 & _).
  pose proof Hly8 as (_ & _ & _ & _ & _ & EF8 & _).
  assert (EA8 : frame_addr ly8 0 pos = F) by (unfold F, frame_addr; rewrite EF8; reflexivity).
  assert (Hin8 : In (0, pos) (frames S8)) by (rewrite Hfrs8; left; reflexivity).
  assert (CSH : crcs_csr regs (ms_regs msH) sp0 sp1 F)
    by exact (crcs_csr_run (w_H W7) regs regs7 ext _ msH sp0 sp1 F HSH CS7 ltac:(vm_compute; reflexivity)).
  pose proof (crcs_csr_call regs (ms_regs msH) regs8 sp0 sp1 F HP8 CSH) as CS8.
  pose proof CS8 as (C8_2 & C8_3 & C8_4 & C8_8 & C8_18 & C8_20 & C8_23 & C8_24 & C8_25 & C8_26 & C8_27).
  assert (R8_19 : getr regs8 19%bv = getr regs 12%bv).
  { rewrite (fsw_pres _ _ 19%bv HP8 ltac:(crcs_cs)).
    rewrite (fsw_reg_atom (w_H W7) regs7 ext _ msH 19%bv 19%bv 19 HSH ltac:(vm_compute; reflexivity) eq_refl). exact R7_19. }
  assert (R8_22 : getr regs8 22%bv = w64 live).
  { rewrite (fsw_pres _ _ 22%bv HP8 ltac:(crcs_cs)).
    rewrite (fsw_reg_atom (w_H W7) regs7 ext _ msH 22%bv 22%bv 22 HSH ltac:(vm_compute; reflexivity) eq_refl). exact R7_22. }
  pose proof HARU8 as (HAR8' & OK8 & PO8).
  assert (Eab8 : ablocks B ly8 S8 = ablocks B ly S) by (rewrite Qab8; exact Eab7).
  assert (HSf8 : st_ok tfibsegs (Ereg regs8 ext) (crcs_fs 0x827c4 (crcs_fcs2 (2 ^ 64 - 1)))
    (restrict (w_H W8) (mkst regs8 (Z_to_bv 64 0x827c4) mem8 (seg_rom tfibsegs)))).
  { apply (crcs_readd2 ly8 S8 U W8 md10 regs regs8 mem8 FL 0x827c4 pos sp0 (2 ^ 64 - 1) HARU8 Hin8 HSr8);
      rewrite ?EA8; try assumption; try lia.
    - apply (crcs_val_keep_call B _ _ _ ly7 S7 U W7 (ms_mem msH) mdH ly8 S8 U W8 mem8 md10 0 0 pos (F + 32) 8 _ HJc8 HARUH
        OK8 PO8 Hin7 ltac:(lia)); [rewrite EA7; lia | rewrite EA7; change (fs_frame_bytes 0) with 64; cbn; lia
        | intros x Hx; apply NFP; cbn in Hx; lia | exact VH32].
    - apply (crcs_val_keep_call B _ _ _ ly7 S7 U W7 (ms_mem msH) mdH ly8 S8 U W8 mem8 md10 0 0 pos (F + 56) 8 _ HJc8 HARUH
        OK8 PO8 Hin7 ltac:(lia)); [rewrite EA7; lia | rewrite EA7; change (fs_frame_bytes 0) with 64; cbn; lia
        | intros x Hx; apply NFP; cbn in Hx; lia | exact VH56]. }
  (* ---- 0x827c4 .. 0x827cc: a0 := s4 (bd), a1 := s3 (l); jal preset_base64_encode (fs.c:220) ---- *)
  let res := eval vm_compute in
    (sym_run_toN tfibsegs crcs_tbl FUEL A_preset_base64_encode (crcs_fs 0x827c4 (crcs_fcs2 (2 ^ 64 - 1)))) in
  lazymatch res with (?ssC, ?stC) =>
    apply (crcs_seg ly S U W mem md pos ly8 S8 W8 regs8 mem8 md10 (0 + 0 + 0 + 0 + 0 + 0 + 0) ext sp0 0x827c4
      (crcs_fcs2 (2 ^ 64 - 1)) [] (crcs_fs 0x827c4 (crcs_fcs2 (2 ^ 64 - 1))) A_preset_base64_encode ssC stC _ HSf8 eq_refl
      HJ8 HARU8 C8_8 ltac:(rewrite EA8; exact C8_25) ltac:(rewrite EA8; exact C8_24) ltac:(vm_compute; reflexivity) I)
  end.
  intros msI matI HSI HJI HARUI HII.
  set (mdI := with_vm_backing (m_vm_lazy md10) matI md10) in *.
  assert (SENC : STK_preset_base64_encode = ltac:(let v := eval vm_compute in STK_preset_base64_encode in exact v))
    by (vm_compute; reflexivity).
  destruct (crcs_site ly S U W mem md regs ch pos FL ly8 S8 W8 regs8 msI mdI (0 + 0 + 0 + 0 + 0 + 0 + 0) _ 0x827d0 sp1
    STK_preset_base64_encode HPREU HTOP HRO0 HSI ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) C8_2 C8_3 C8_4 C8_8 ltac:(lia) Hm16 ltac:(lia) ltac:(vm_compute; reflexivity)
    ltac:(rewrite SENC; lia) ltac:(rewrite SENC; lia) HJI HARUI) as (HPREI & RI1 & RI8 & HspI & CsI & ExI).
  assert (RI10 : getr (ms_regs msI) 10%bv = w64 bd).
  { crcs_reg HSI (10%bv : bv 5). rewrite fsw_SOff0, (ew_Ereg_nat regs8 ext 20 20%bv eq_refl), C8_20. exact Hbd. }
  assert (RI11 : getr (ms_regs msI) 11%bv = w64 l).
  { crcs_reg HSI (11%bv : bv 5). rewrite fsw_SOff0, (ew_Ereg_nat regs8 ext 19 19%bv eq_refl), R8_19. exact Hl. }
  assert (GI : fs_glob tfibsegs W8 (ms_mem msI) live peak (cnt + 1) (cnt + 1))
    by exact (crcs_glob_keep W8 mem8 (ms_mem msI) _ _ _ _ HII Qglob8).
  pose proof HARUI as (HARI & OKI & POI).
  pose proof HJI as (_ & _ & _ & _ & _ & _ & HnevI & _).
  destruct (crcs_rblock_keep _ sp0 ly S U W mem md [(0, pos)] ly8 S8 W8 (ms_mem msI) mdI _ bd m bs HJI HARU0 HARUI Eab8 Hrb
    ltac:(lia) Hz) as (HrbI & HzI).
  assert (VI32 : val_mem tfibsegs (mrestrict (w_H W8) (ms_mem msI)) (F + 32) 8 (2 ^ 64 - 1)).
  { eapply (crcs_val_at (Ereg regs8 ext) _ (w_H W8) msI 0 _ _ _ _ _ _ 32 8%N (SLit (2 ^ 64 - 1)) (2 ^ 64 - 1) F);
      [exact HSI | reflexivity | cbn; repeat (first [left; reflexivity | right]) | | | |].
    - rewrite (ew_Ereg_nat regs8 ext 25 25%bv eq_refl), C8_25. apply unsigned_lit_small. lia.
    - apply bv_eq. rewrite unsigned_lit_small by lia. change (bv_unsigned (sv_denot (Ereg regs8 ext) (SLit (2 ^ 64 - 1))))
        with (YP0e.U (Ereg regs8 ext) (SLit (2 ^ 64 - 1))). rewrite U_lit by lia. reflexivity.
    - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    - cbn. lia. }
  assert (VI56 : val_mem tfibsegs (mrestrict (w_H W8) (ms_mem msI)) (F + 56) 8 FL).
  { eapply (crcs_val_at (Ereg regs8 ext) _ (w_H W8) msI 0 _ _ _ _ _ _ 56 8%N (SOff 45 0) FL F);
      [exact HSI | reflexivity | cbn; repeat (first [left; reflexivity | right]) | | | |].
    - rewrite (ew_Ereg_nat regs8 ext 25 25%bv eq_refl), C8_25. apply unsigned_lit_small. lia.
    - change 45%nat with (32 + 13)%nat. rewrite fsw_SOff0, ew_Ereg_extra. reflexivity.
    - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    - cbn. lia. }
  (* the encoder under its refusal arm: g_count = g_fail_at = cnt + 1 *)
  assert (HSPI : SRr tfibsegs W8 (cfg_at tfibsegs A_preset_base64_encode (ms_regs msI) (ms_mem msI) mdI)
    (@fpostU fx rc SK tfibsegs B STK_preset_base64_encode (spZ (ms_regs msI)) FS_PSTAT_FP (ms_regs msI) ly8 S8 U W8 (ms_mem msI) mdI 0 U
       (fun ly' S' W' regs' mem' md' => getr regs' 10 = w64 0 /\ ablocks B ly' S' = ablocks B ly8 S8 /\
          fs_glob tfibsegs W' mem' live peak ((cnt + 1 + 1) mod 2 ^ 64) SIZE_MAXZ))).
  { eapply SRr_mono; [apply (ENC ly8 S8 U W8 (ms_regs msI) (ms_mem msI) mdI ch1 bd l bs live peak (cnt + 1) (cnt + 1))|].
    - exact HPREI.
    - exact Qheads8.
    - rewrite Hfrs8. exact (crcs_frames_callee (0, pos) (frames S) HFRL).
    - exact RI10.
    - exact RI11.
    - exact Hbs.
    - exact Hlen.
    - lia.
    - exact HzI.
    - split; lia.
    - intros _. exists m. split; [exact HrbI | exact Hlm].
    - exact GI.
    - unfold EV_preset_base64_encode in *. pose proof (crcs_ev_nonneg tb). lia.
    - rewrite (blocks_bytes_bsum B ly8 S8), Eab8, <- (blocks_bytes_bsum B ly S). exact HbbE.
    - exact HliveE.
    - lia.
    - intros W' c' _ [[_ HP] | (q & Hne & _)]; [exact HP | exfalso; exact (Hne eq_refl)]. }
  refine (crcs_call STK_check_reject_clean_starved sp0 FS_PSTAT_FP ly S U W mem md [(0, pos)] ly8 S8 W8 msI mdI
    (0 + 0 + 0 + 0 + 0 + 0 + 0) (Ereg regs8 ext) _ STK_preset_base64_encode FS_PSTAT_FP 0 _ _ ext 0x827d0 HSI eq_refl HJI
    HARUI HSPI ltac:(intros a Ha; right; right; left; split; [exact Ha | exact (crcs_pstat_img a Ha)]) RI1 RI8
    ltac:(rewrite HspI, SENC; lia) ltac:(rewrite HspI; lia) ltac:(lia) CsI ExI _).
  intros ly9 S9 W9 regs9 mem9 md11 (Q10i & Qab9 & Qglob9) HP9 HJc9 HJ9 HARU9 HSr9.
  rewrite (crcs_tick (cnt + 1) ltac:(lia) ltac:(lia)) in Qglob9.
  (* ---- after preset_base64_encode (refused): 0x827d0 ---- *)
  pose proof HJ9 as (HAR9 & Hly9 & _ & _ & _ & Hfrs9 & Hnev9 & _).
  pose proof Hly9 as (_ & _ & _ & _ & _ & EF9 & _).
  assert (EA9 : frame_addr ly9 0 pos = F) by (unfold F, frame_addr; rewrite EF9; reflexivity).
  assert (Hin9 : In (0, pos) (frames S9)) by (rewrite Hfrs9; left; reflexivity).
  assert (CSI : crcs_csr regs (ms_regs msI) sp0 sp1 F)
    by exact (crcs_csr_run (w_H W8) regs regs8 ext _ msI sp0 sp1 F HSI CS8 ltac:(vm_compute; reflexivity)).
  pose proof (crcs_csr_call regs (ms_regs msI) regs9 sp0 sp1 F HP9 CSI) as CS9.
  pose proof CS9 as (C9_2 & C9_3 & C9_4 & C9_8 & C9_18 & C9_20 & C9_23 & C9_24 & C9_25 & C9_26 & C9_27).
  assert (R9_22 : getr regs9 22%bv = w64 live).
  { rewrite (fsw_pres _ _ 22%bv HP9 ltac:(crcs_cs)).
    rewrite (fsw_reg_atom (w_H W8) regs8 ext _ msI 22%bv 22%bv 22 HSI ltac:(vm_compute; reflexivity) eq_refl). exact R8_22. }
  pose proof HARU9 as (HAR9' & OK9 & PO9).
  assert (Eab9 : ablocks B ly9 S9 = ablocks B ly S) by (rewrite Qab9; exact Eab8).
  pose proof (crcs_heads B ly S ly9 S9 U Eab9 HHEADS) as Hheads9.
  assert (HSf9 : st_ok tfibsegs (Ereg regs9 ext) (crcs_fs 0x827d0 (crcs_fcs2 (2 ^ 64 - 1)))
    (restrict (w_H W9) (mkst regs9 (Z_to_bv 64 0x827d0) mem9 (seg_rom tfibsegs)))).
  { apply (crcs_readd2 ly9 S9 U W9 md11 regs regs9 mem9 FL 0x827d0 pos sp0 (2 ^ 64 - 1) HARU9 Hin9 HSr9);
      rewrite ?EA9; try assumption; try lia.
    - apply (crcs_val_keep_call B _ _ _ ly8 S8 U W8 (ms_mem msI) mdI ly9 S9 U W9 mem9 md11 0 0 pos (F + 32) 8 _ HJc9 HARUI
        OK9 PO9 Hin8 ltac:(lia)); [rewrite EA8; lia | rewrite EA8; change (fs_frame_bytes 0) with 64; cbn; lia
        | intros x Hx; apply NFP; cbn in Hx; lia | exact VI32].
    - apply (crcs_val_keep_call B _ _ _ ly8 S8 U W8 (ms_mem msI) mdI ly9 S9 U W9 mem9 md11 0 0 pos (F + 56) 8 _ HJc9 HARUI
        OK9 PO9 Hin8 ltac:(lia)); [rewrite EA8; lia | rewrite EA8; change (fs_frame_bytes 0) with 64; cbn; lia
        | intros x Hx; apply NFP; cbn in Hx; lia | exact VI56]. }
  (* ---- 0x827d0 .. 0x827d8: s3 := a0 (encode's NULL), a0 := SIZE_MAX; jal fuzz_alloc_fail (SIZE_MAX) (fs.c:221) ---- *)
  let res := eval vm_compute in
    (sym_run_toN tfibsegs crcs_tbl FUEL A_fuzz_alloc_fail (crcs_fs 0x827d0 (crcs_fcs2 (2 ^ 64 - 1)))) in
  lazymatch res with (?ssC, ?stC) =>
    apply (crcs_seg ly S U W mem md pos ly9 S9 W9 regs9 mem9 md11 (0 + 0 + 0 + 0 + 0 + 0 + 0 + 0) ext sp0 0x827d0
      (crcs_fcs2 (2 ^ 64 - 1)) [] (crcs_fs 0x827d0 (crcs_fcs2 (2 ^ 64 - 1))) A_fuzz_alloc_fail ssC stC _ HSf9 eq_refl
      HJ9 HARU9 C9_8 ltac:(rewrite EA9; exact C9_25) ltac:(rewrite EA9; exact C9_24) ltac:(vm_compute; reflexivity) I)
  end.
  intros msJ matJ HSJ HJJ HARUJ HIJ.
  set (mdJ := with_vm_backing (m_vm_lazy md11) matJ md11) in *.
  destruct (crcs_site ly S U W mem md regs ch pos FL ly9 S9 W9 regs9 msJ mdJ (0 + 0 + 0 + 0 + 0 + 0 + 0 + 0) _ 0x827dc sp1
    STK_fuzz_alloc HPREU HTOP HRO0 HSJ ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) C9_2 C9_3 C9_4 C9_8 ltac:(lia) Hm16 ltac:(lia) ltac:(vm_compute; reflexivity)
    ltac:(change STK_fuzz_alloc with 0; lia) ltac:(change STK_fuzz_alloc with 0; lia) HJJ HARUJ)
    as (HPREJ & RJ1 & RJ8 & HspJ & CsJ & ExJ).
  assert (RJ10 : getr (ms_regs msJ) 10%bv = w64 SIZE_MAXZ)
    by exact (fsw_reg_lit (w_H W9) _ _ msJ 10%bv SIZE_MAXZ HSJ ltac:(vm_compute; reflexivity) ltac:(unfold SIZE_MAXZ; lia)).
  assert (RJ19 : getr (ms_regs msJ) 19%bv = w64 0).
  { crcs_reg HSJ (19%bv : bv 5). rewrite fsw_SOff0, (ew_Ereg_nat regs9 ext 10 10%bv eq_refl). exact Q10i. }
  assert (RJ22 : getr (ms_regs msJ) 22%bv = w64 live)
    by (rewrite (fsw_reg_atom (w_H W9) regs9 ext _ msJ 22%bv 22%bv 22 HSJ ltac:(vm_compute; reflexivity) eq_refl);
        exact R9_22).
  assert (GJ : fs_glob tfibsegs W9 (ms_mem msJ) live peak (cnt + 1 + 1) SIZE_MAXZ)
    by exact (crcs_glob_keep W9 mem9 (ms_mem msJ) _ _ _ _ HIJ Qglob9).
  assert (VJ32 : val_mem tfibsegs (mrestrict (w_H W9) (ms_mem msJ)) (F + 32) 8 (2 ^ 64 - 1)).
  { eapply (crcs_val_at (Ereg regs9 ext) _ (w_H W9) msJ 0 _ _ _ _ _ _ 32 8%N (SLit (2 ^ 64 - 1)) (2 ^ 64 - 1) F);
      [exact HSJ | reflexivity | cbn; repeat (first [left; reflexivity | right]) | | | |].
    - rewrite (ew_Ereg_nat regs9 ext 25 25%bv eq_refl), C9_25. apply unsigned_lit_small. lia.
    - apply bv_eq. rewrite unsigned_lit_small by lia. change (bv_unsigned (sv_denot (Ereg regs9 ext) (SLit (2 ^ 64 - 1))))
        with (YP0e.U (Ereg regs9 ext) (SLit (2 ^ 64 - 1))). rewrite U_lit by lia. reflexivity.
    - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    - cbn. lia. }
  assert (VJ56 : val_mem tfibsegs (mrestrict (w_H W9) (ms_mem msJ)) (F + 56) 8 FL).
  { eapply (crcs_val_at (Ereg regs9 ext) _ (w_H W9) msJ 0 _ _ _ _ _ _ 56 8%N (SOff 45 0) FL F);
      [exact HSJ | reflexivity | cbn; repeat (first [left; reflexivity | right]) | | | |].
    - rewrite (ew_Ereg_nat regs9 ext 25 25%bv eq_refl), C9_25. apply unsigned_lit_small. lia.
    - change 45%nat with (32 + 13)%nat. rewrite fsw_SOff0, ew_Ereg_extra. reflexivity.
    - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    - cbn. lia. }
  refine (crcs_call STK_check_reject_clean_starved sp0 FS_PSTAT_FP ly S U W mem md [(0, pos)] ly9 S9 W9 msJ mdJ
    (0 + 0 + 0 + 0 + 0 + 0 + 0 + 0) (Ereg regs9 ext) _ STK_fuzz_alloc FS_PSTAT_FP 0 _ _ ext 0x827dc HSJ eq_refl HJJ HARUJ
    (FAIL ly9 S9 U W9 (ms_regs msJ) (ms_mem msJ) mdJ ch1 live peak (cnt + 1 + 1) SIZE_MAXZ SIZE_MAXZ HPREJ Hheads9 GJ RJ10
      ltac:(unfold SIZE_MAXZ; lia))
    ltac:(intros a Ha; right; right; left; split; [exact Ha | exact (crcs_pstat_img a Ha)]) RJ1 RJ8
    ltac:(rewrite HspJ; change STK_fuzz_alloc with 0; lia) ltac:(rewrite HspJ; lia) ltac:(lia) CsJ ExJ _).
  intros ly10 S10 W10 regs10 mem10 md12 (Qab10 & Qheads10 & Qglob10) HP10 HJc10 HJ10 HARU10 HSr10.
  rewrite (crcs_failmax (cnt + 1 + 1) ltac:(lia)) in Qglob10.
  (* ---- after fuzz_alloc_fail (SIZE_MAX): 0x827dc, `bnez s3` not taken (s3 = encode's NULL) ---- *)
  pose proof HJ10 as (HAR10 & Hly10 & _ & _ & _ & Hfrs10 & Hnev10 & _).
  pose proof Hly10 as (_ & _ & _ & _ & _ & EF10 & _).
  assert (EA10 : frame_addr ly10 0 pos = F) by (unfold F, frame_addr; rewrite EF10; reflexivity).
  assert (Hin10 : In (0, pos) (frames S10)) by (rewrite Hfrs10; left; reflexivity).
  assert (CSJ : crcs_csr regs (ms_regs msJ) sp0 sp1 F)
    by exact (crcs_csr_run (w_H W9) regs regs9 ext _ msJ sp0 sp1 F HSJ CS9 ltac:(vm_compute; reflexivity)).
  pose proof (crcs_csr_call regs (ms_regs msJ) regs10 sp0 sp1 F HP10 CSJ) as CS10.
  pose proof CS10 as (C10_2 & C10_3 & C10_4 & C10_8 & C10_18 & C10_20 & C10_23 & C10_24 & C10_25 & C10_26 & C10_27).
  assert (R10_19 : getr regs10 19%bv = w64 0) by (rewrite (fsw_pres _ _ 19%bv HP10 ltac:(crcs_cs)); exact RJ19).
  assert (R10_22 : getr regs10 22%bv = w64 live) by (rewrite (fsw_pres _ _ 22%bv HP10 ltac:(crcs_cs)); exact RJ22).
  pose proof HARU10 as (HAR10' & OK10 & PO10).
  assert (Eab10 : ablocks B ly10 S10 = ablocks B ly S) by (rewrite Qab10; exact Eab9).
  assert (HSf10 : st_ok tfibsegs (Ereg regs10 ext) (crcs_fs 0x827dc (crcs_fcs2 (2 ^ 64 - 1)))
    (restrict (w_H W10) (mkst regs10 (Z_to_bv 64 0x827dc) mem10 (seg_rom tfibsegs)))).
  { apply (crcs_readd2 ly10 S10 U W10 md12 regs regs10 mem10 FL 0x827dc pos sp0 (2 ^ 64 - 1) HARU10 Hin10 HSr10);
      rewrite ?EA10; try assumption; try lia.
    - apply (crcs_val_keep_call B _ _ _ ly9 S9 U W9 (ms_mem msJ) mdJ ly10 S10 U W10 mem10 md12 0 0 pos (F + 32) 8 _ HJc10
        HARUJ OK10 PO10 Hin9 ltac:(lia)); [rewrite EA9; lia | rewrite EA9; change (fs_frame_bytes 0) with 64; cbn; lia
        | intros x Hx; apply NFP; cbn in Hx; lia | exact VJ32].
    - apply (crcs_val_keep_call B _ _ _ ly9 S9 U W9 (ms_mem msJ) mdJ ly10 S10 U W10 mem10 md12 0 0 pos (F + 56) 8 _ HJc10
        HARUJ OK10 PO10 Hin9 ltac:(lia)); [rewrite EA9; lia | rewrite EA9; change (fs_frame_bytes 0) with 64; cbn; lia
        | intros x Hx; apply NFP; cbn in Hx; lia | exact VJ56]. }
  assert (HS10c : st_ok tfibsegs (Ereg regs10 ext)
    (add_cond (crcs_fs 0x827dc (crcs_fcs2 (2 ^ 64 - 1))) (mkAC BC_EQ (SOff 19 0) (SLit 0)))
    (restrict (w_H W10) (mkst regs10 (Z_to_bv 64 0x827dc) mem10 (seg_rom tfibsegs)))).
  { apply (st_ok_add_cond tfibsegs _ _ _ BC_EQ (SOff 19 0) (SLit 0) HSf10).
    rewrite branch_eq_U, (U_atom (Ereg regs10 ext) 19 0
      ltac:(rewrite (ew_Ereg_nat regs10 ext 19 19%bv eq_refl); exact R10_19) ltac:(lia)), U_SLit.
    reflexivity. }
  (* ---- 0x827dc .. 0x827e0: jal fuzz_alloc_live (fs.c:222) ---- *)
  let res := eval vm_compute in (sym_run_toN tfibsegs crcs_tbl FUEL A_fuzz_alloc_live
    (add_cond (crcs_fs 0x827dc (crcs_fcs2 (2 ^ 64 - 1))) (mkAC BC_EQ (SOff 19 0) (SLit 0)))) in
  lazymatch res with (?ssC, ?stC) =>
    apply (crcs_seg ly S U W mem md pos ly10 S10 W10 regs10 mem10 md12 (0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0) ext sp0 0x827dc
      (crcs_fcs2 (2 ^ 64 - 1)) [] (add_cond (crcs_fs 0x827dc (crcs_fcs2 (2 ^ 64 - 1))) (mkAC BC_EQ (SOff 19 0) (SLit 0)))
      A_fuzz_alloc_live ssC stC _ HS10c eq_refl HJ10 HARU10 C10_8 ltac:(rewrite EA10; exact C10_25)
      ltac:(rewrite EA10; exact C10_24) ltac:(vm_compute; reflexivity) I)
  end.
  intros msK matK HSK HJK HARUK HIK.
  set (mdK := with_vm_backing (m_vm_lazy md12) matK md12) in *.
  destruct (crcs_site ly S U W mem md regs ch pos FL ly10 S10 W10 regs10 msK mdK (0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0) _
    0x827e4 sp1 STK_fuzz_alloc HPREU HTOP HRO0 HSK ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) C10_2 C10_3 C10_4 C10_8 ltac:(lia) Hm16 ltac:(lia) ltac:(vm_compute; reflexivity)
    ltac:(change STK_fuzz_alloc with 0; lia) ltac:(change STK_fuzz_alloc with 0; lia) HJK HARUK)
    as (HPREK & RK1 & RK8 & HspK & CsK & ExK).
  assert (RK22 : getr (ms_regs msK) 22%bv = w64 live)
    by (rewrite (fsw_reg_atom (w_H W10) regs10 ext _ msK 22%bv 22%bv 22 HSK ltac:(vm_compute; reflexivity) eq_refl);
        exact R10_22).
  assert (GK : fs_glob tfibsegs W10 (ms_mem msK) live peak (cnt + 1 + 1) SIZE_MAXZ)
    by exact (crcs_glob_keep W10 mem10 (ms_mem msK) _ _ _ _ HIK Qglob10).
  pose proof (crcs_heads B ly S ly10 S10 U Eab10 HHEADS) as Hheads10.
  assert (VK32 : val_mem tfibsegs (mrestrict (w_H W10) (ms_mem msK)) (F + 32) 8 (2 ^ 64 - 1)).
  { eapply (crcs_val_at (Ereg regs10 ext) _ (w_H W10) msK 0 _ _ _ _ _ _ 32 8%N (SLit (2 ^ 64 - 1)) (2 ^ 64 - 1) F);
      [exact HSK | reflexivity | cbn; repeat (first [left; reflexivity | right]) | | | |].
    - rewrite (ew_Ereg_nat regs10 ext 25 25%bv eq_refl), C10_25. apply unsigned_lit_small. lia.
    - apply bv_eq. rewrite unsigned_lit_small by lia. change (bv_unsigned (sv_denot (Ereg regs10 ext) (SLit (2 ^ 64 - 1))))
        with (YP0e.U (Ereg regs10 ext) (SLit (2 ^ 64 - 1))). rewrite U_lit by lia. reflexivity.
    - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    - cbn. lia. }
  assert (VK56 : val_mem tfibsegs (mrestrict (w_H W10) (ms_mem msK)) (F + 56) 8 FL).
  { eapply (crcs_val_at (Ereg regs10 ext) _ (w_H W10) msK 0 _ _ _ _ _ _ 56 8%N (SOff 45 0) FL F);
      [exact HSK | reflexivity | cbn; repeat (first [left; reflexivity | right]) | | | |].
    - rewrite (ew_Ereg_nat regs10 ext 25 25%bv eq_refl), C10_25. apply unsigned_lit_small. lia.
    - change 45%nat with (32 + 13)%nat. rewrite fsw_SOff0, ew_Ereg_extra. reflexivity.
    - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    - cbn. lia. }
  refine (crcs_call STK_check_reject_clean_starved sp0 FS_PSTAT_FP ly S U W mem md [(0, pos)] ly10 S10 W10 msK mdK
    (0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0) (Ereg regs10 ext) _ STK_fuzz_alloc [] 0 _ _ ext 0x827e4 HSK eq_refl HJK HARUK
    (LIVE ly10 S10 U W10 (ms_regs msK) (ms_mem msK) mdK ch1 live peak (cnt + 1 + 1) SIZE_MAXZ HPREK Hheads10 GK)
    ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) RK1 RK8
    ltac:(rewrite HspK; change STK_fuzz_alloc with 0; lia) ltac:(rewrite HspK; lia) ltac:(lia) CsK ExK _).
  intros ly11 S11 W11 regs11 mem11 md13 (Q10l & Qab11 & Qglob11 & Qheads11) HP11 HJc11 HJ11 HARU11 HSr11.
  (* ---- after fuzz_alloc_live: 0x827e4, `bne a0, s6` not taken (both g_live), the epilogue ---- *)
  pose proof HJ11 as (HAR11 & Hly11 & _ & _ & _ & Hfrs11 & Hnev11 & _).
  pose proof Hly11 as (_ & _ & _ & _ & _ & EF11 & _).
  assert (EA11 : frame_addr ly11 0 pos = F) by (unfold F, frame_addr; rewrite EF11; reflexivity).
  assert (EFL11 : FL = flag_addr ly11 0 pos) by (unfold FL, flag_addr; rewrite EF11; reflexivity).
  assert (Hin11 : In (0, pos) (frames S11)) by (rewrite Hfrs11; left; reflexivity).
  assert (CSK : crcs_csr regs (ms_regs msK) sp0 sp1 F)
    by exact (crcs_csr_run (w_H W10) regs regs10 ext _ msK sp0 sp1 F HSK CS10 ltac:(vm_compute; reflexivity)).
  pose proof (crcs_csr_call regs (ms_regs msK) regs11 sp0 sp1 F HP11 CSK) as CS11.
  pose proof CS11 as (C11_2 & C11_3 & C11_4 & C11_8 & C11_18 & C11_20 & C11_23 & C11_24 & C11_25 & C11_26 & C11_27).
  assert (R11_22 : getr regs11 22%bv = w64 live) by (rewrite (fsw_pres _ _ 22%bv HP11 ltac:(crcs_cs)); exact RK22).
  pose proof HARU11 as (HAR11' & OK11 & PO11).
  assert (Eab11 : ablocks B ly11 S11 = ablocks B ly S) by (rewrite Qab11; exact Eab10).
  assert (HSf11 : st_ok tfibsegs (Ereg regs11 ext) (crcs_fs 0x827e4 (crcs_fcs2 (2 ^ 64 - 1)))
    (restrict (w_H W11) (mkst regs11 (Z_to_bv 64 0x827e4) mem11 (seg_rom tfibsegs)))).
  { apply (crcs_readd2 ly11 S11 U W11 md13 regs regs11 mem11 FL 0x827e4 pos sp0 (2 ^ 64 - 1) HARU11 Hin11 HSr11);
      rewrite ?EA11; try assumption; try lia.
    - apply (crcs_val_keep_call B _ _ _ ly10 S10 U W10 (ms_mem msK) mdK ly11 S11 U W11 mem11 md13 0 0 pos (F + 32) 8 _ HJc11
        HARUK OK11 PO11 Hin10 ltac:(lia)); [rewrite EA10; lia | rewrite EA10; change (fs_frame_bytes 0) with 64; cbn; lia
        | intros x _ Hx; exact (inFP_nil x Hx) | exact VK32].
    - apply (crcs_val_keep_call B _ _ _ ly10 S10 U W10 (ms_mem msK) mdK ly11 S11 U W11 mem11 md13 0 0 pos (F + 56) 8 _ HJc11
        HARUK OK11 PO11 Hin10 ltac:(lia)); [rewrite EA10; lia | rewrite EA10; change (fs_frame_bytes 0) with 64; cbn; lia
        | intros x _ Hx; exact (inFP_nil x Hx) | exact VK56]. }
  assert (HS11c : st_ok tfibsegs (Ereg regs11 ext)
    (add_cond (crcs_fs 0x827e4 (crcs_fcs2 (2 ^ 64 - 1))) (mkAC BC_EQ (SOff 10 0) (SOff 22 0)))
    (restrict (w_H W11) (mkst regs11 (Z_to_bv 64 0x827e4) mem11 (seg_rom tfibsegs)))).
  { apply (st_ok_add_cond tfibsegs _ _ _ BC_EQ (SOff 10 0) (SOff 22 0) HSf11).
    rewrite branch_eq_U. unfold YP0e.U. rewrite !fsw_SOff0, (ew_Ereg_nat regs11 ext 10 10%bv eq_refl),
      (ew_Ereg_nat regs11 ext 22 22%bv eq_refl), Q10l, R11_22.
    apply Z.eqb_refl. }
  let res := eval vm_compute in (sym_runN tfibsegs crcs_tbl FUEL
    (crcs_epi_ss (add_cond (crcs_fs 0x827e4 (crcs_fcs2 (2 ^ 64 - 1))) (mkAC BC_EQ (SOff 10 0) (SOff 22 0))))) in
  lazymatch res with (?ssR, ?stR) =>
    exact (crcs_epi ly S U W mem md regs pos FL ly11 S11 W11 regs11 (mkst regs11 (Z_to_bv 64 0x827e4) mem11 (seg_rom tfibsegs))
      md13 (0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0)
      (add_cond (crcs_fs 0x827e4 (crcs_fcs2 (2 ^ 64 - 1))) (mkAC BC_EQ (SOff 10 0) (SOff 22 0)))
      ssR stR live peak (cnt + 1 + 1) (or_intror I) Hra0 HS11c eq_refl ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) I
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(rewrite Esp1e, EA11; exact CS11) EFL11 HJ11 HARU11 Eab11 Qglob11)
  end.
Qed.
End W.
