(* preset_base64_encode 0x84390 (preset_file.c:577-608) on fs.asan: S0's encode_spec (lib/A/FSH_Fn_writer.v) proved
   over the walk kit lib/A/FSW_K.v + lib/A/FSW_ret.v, with the one callee contract (fuzz_malloc, lib/A/FSH_Fn_alloc.v)
   as a Section hypothesis. The model half (what the instructions compute) is lib/A/FSW_preset_base64_encode_blocks.v.

   Route (MEASURED, capstone over the pinned fs.asan 64b53ff8...):
     0x84390..0x843d0  prologue: 32-byte frame, s0 := len, s1 := data, s2 := the ASan shadow base through the GOT
                       (0x9f6f0 -> 0xa7f38), a0 := enc_size len (mulhu by the .rodata word 0x10320)
     0x843d4           jal fuzz_malloc (0x828ac); 0x843d8 beqz a0 -> the refused-allocation arm
     0x843f8..0x84534  the 3-byte main loop: eight inline shadow checks per round, four table reads, four stores
     0x845c4..0x846fc  the tail (one or two leftover bytes, '=' padding)
     0x84700..0x84728  the terminating 0 and the epilogue
   Every inline shadow check falls through: the walk runs them through FSW_K's token run (fsw_aj_run_tokU at
   Bx := the shadow-base register s2, Bspan := fs_Bspan), whose shents / obligations are discharged from
   range_addressable of the input block (encode_spec's block clause), of the output block (fuzz_malloc's post) and of
   g_b64 (fs_img_facts' cstr_ok for FS_RO_STRS). No __asan_report_* call is reached.

   Rule 24 (proof-index v5 built 2026-10-28T21:58:24Z, exit 0, read from a file, not a pipe):
   preset_base64_encode has RELEASED proofs for fs's PLAIN and UBSAN builds only (lib/Prog, lib/U/Prog,
   ossv/recipes@566eb6ffa5, release/pau-projects-recipes@b6a0088adc), none for an ASan build. *)
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
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSH_Fn_writer FSH_Fn_alloc
FSW_K FSW_K3 FSW_rres FSW_ret FSW_writer_tbl FSW_preset_base64_encode_blocks.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the .rodata word 0x10320 the size arithmetic multiplies by, as a region of the entry state *)
Definition ENC_MAGIC_A : Z := 0x10320.
Definition enc_magic_region : YP09.region :=
  YP09.mkRegion None ENC_MAGIC_A (ENC_MAGIC_A + 8) 0 0 [YP09.mkChunk ENC_MAGIC_A (CVal 8 (SLit ENC_MAGIC))].
(* the 64 letters of g_b64, as FSH_Rt.FS_RO_STRS lists them at G_B64 *)
Definition enc_b64_bytes : list Z := map WriterSpec.b64c (map Z.of_nat (seq 0 64)).

(* ---- the round's symbolic state (atoms: 8 len, 9 data, 11/17 the output pointer, 12 the input pointer
   data + i, 14 i, 15 g_b64, 18 the shadow base, 36..38 the round's three input bytes; 100/200/300/400 the
   four table seats and 101/201/301/401 their bytes). The round touches no stack byte, so the state carries
   no stack region at all and the run's own frame_of keeps the frame's four saved words. Pointer atoms are
   bounded by PTOP, which keeps every shadow byte the token run needs inside fs_Bspan (a heap block ends below
   2^47 - 4096: enc_blk_bounds). ---- *)
Definition PTOP : Z := 2 ^ 47 - 4096.
(* a byte range outside the shadow band [SHADOW_OFF, SHADOW_OFF + 2^44): a heap block may sit below the band
   (kLowMemEnd) or above it (kHighMemBeg), never in it (enc_blk_bounds) *)
Definition enc_apart (lo hi : Z) : Prop :=
  forall x, lo <= x < hi -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416).
Definition enc_rin : YP09.region :=
  YP09.mkRegion (Some 12%nat) (-2) 1 0 0
    [YP09.mkChunk (-2) (CVal 1 (SOff 36 0)); YP09.mkChunk (-1) (CVal 1 (SOff 37 0));
     YP09.mkChunk 0 (CVal 1 (SOff 38 0))].
Definition enc_rout : YP09.region := YP09.mkRegion (Some 17%nat) 0 4 0 4 [].
Definition enc_gf : list (nat * afact) :=
  [(18%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (12%nat, mkAF 4096 PTOP 0); (17%nat, mkAF 4096 PTOP 0);
   (11%nat, mkAF 4096 PTOP 0); (8%nat, mkAF 0 (2 ^ 27) 0); (14%nat, mkAF 0 (2 ^ 27) 0);
   (15%nat, mkAF G_B64 G_B64 0); (36%nat, mkAF 0 255 0); (37%nat, mkAF 0 255 0); (38%nat, mkAF 0 255 0)].
Definition enc_round_ss (pc : Z) : sstate :=
  mkSS pc sr_atoms [enc_rin; enc_rout] None (mkFacts enc_gf [] []).
(* the shents: the three input bytes at a2, the four output bytes reached through a7 and through a1, and one
   per table seat *)
Definition enc_SH : list shent := [mkSHE 12%nat (-2) 1; mkSHE 17%nat 0 4; mkSHE 11%nat 0 4].
Definition enc_SH1 : list shent := enc_SH ++ [mkSHE 100 0 1].
Definition enc_SH2 : list shent := enc_SH1 ++ [mkSHE 200 0 1].
Definition enc_SH3 : list shent := enc_SH2 ++ [mkSHE 300 0 1].
Definition enc_SH4 : list shent := enc_SH3 ++ [mkSHE 400 0 1].
Definition enc_Bx : sv := SOff 18 0.
(* a register re-seated on a fresh atom whose one-byte read-only region holds the byte it points at: the four
   g_b64 reads of a round, whose address - the table base plus a six-bit index - the engine cannot name *)
Definition enc_seat (ss : sstate) (r : bv 5) (n : nat) (lo hi : Z) : sstate :=
  add_atom (add_atom
    (mkSS (ss_pc ss) (sr_set (ss_regs ss) r (SOff n 0))
       (YP09.mkRegion (Some n) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff (S n) 0))] :: ss_mem ss)
       (ss_resv ss) (ss_facts ss)) n (mkAF lo hi 0)) (S n) (mkAF 0 255 0).

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the shadow-cell pair (S0 lib/A/FSH_Base.v FsShadowSyms; discharged by lib/A/ACeg.v's TfibLib) *)
Hypothesis HSS : FsShadowSyms B.
(* the image facts (S0 lib/A/FSH_Rt.v): rom_view, the canary cells, and cstr_ok / str_homeA for FS_RO_STRS,
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
(* 5. the symbolic state of one round of the 3-byte loop (0x843fc .. 0x84534), rebuilt at every round from the  *)
(*    machine's registers: the three input bytes at a2 (atoms 36..38) and the four output bytes at a7. The      *)
(*    shadow base is the register s2 (atom 18), which is the token run's Bx. The round touches no stack byte,   *)
(*    so the state carries no stack region and the run's own frame_of keeps the frame's four saved words.       *)
(* ---------------------------------------------------------------------------------------------------------- *)

Lemma enc_round_state : forall (W : world tfibsegs) mem regs (E : env) out b0 b1 b2 p len i pc,
  (* the env: atoms 0..31 are the registers, 36..38 the three input bytes *)
  regs_ok E sr_atoms regs ->
  ew E 36 = w64 b0 -> ew E 37 = w64 b1 -> ew E 38 = w64 b2 ->
  (* the registers the round reads *)
  getr regs 8 = w64 len -> getr regs 11 = w64 out -> getr regs 12 = w64 p -> getr regs 14 = w64 i ->
  getr regs 15 = w64 G_B64 -> getr regs 17 = w64 out -> getr regs 18 = w64 SHADOW_OFF ->
  (* the input window and the output window *)
  val_mem tfibsegs (mrestrict (w_H W) mem) (p - 2) 1 b0 ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (p - 1) 1 b1 ->
  val_mem tfibsegs (mrestrict (w_H W) mem) p 1 b2 ->
  (forall o, 0 <= o < 4 -> writable_at tfibsegs (mrestrict (w_H W) mem) (out + o)) ->
  (* the numerals *)
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 ->
  4096 <= p - 2 -> p + 1 <= PTOP -> 4096 <= out -> out + 4 <= PTOP ->
  0 <= len <= 2 ^ 27 -> 0 <= i <= 2 ^ 27 ->
  (* the two heap windows are apart *)
  (p + 1 <= out \/ out + 4 <= p - 2) ->
  st_ok tfibsegs E (enc_round_ss pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfibsegs))).
Proof.
intros W mem regs E out b0 b1 b2 p len i pc HR E36 E37 E38
  R8 R11 R12 R14 R15 R17 R18 Vb0 Vb1 Vb2 HWout Hb0 Hb1 Hb2 Hp0 Hp1 Ho0 Ho1 Hlen Hi Hsep.
assert (EW : forall (r : bv 5) (n : nat), sr_get sr_atoms r = SOff n 0 -> ew E n = getr regs r).
{ intros r n Hn. rewrite (HR r), Hn, fsw_SOff0. reflexivity. }
assert (A8 : ew E 8 = w64 len) by (rewrite (EW 8%bv 8%nat ltac:(vm_compute; reflexivity)); exact R8).
assert (A11 : ew E 11 = w64 out) by (rewrite (EW 11%bv 11%nat ltac:(vm_compute; reflexivity)); exact R11).
assert (A12 : ew E 12 = w64 p) by (rewrite (EW 12%bv 12%nat ltac:(vm_compute; reflexivity)); exact R12).
assert (A14 : ew E 14 = w64 i) by (rewrite (EW 14%bv 14%nat ltac:(vm_compute; reflexivity)); exact R14).
assert (A15 : ew E 15 = w64 G_B64) by (rewrite (EW 15%bv 15%nat ltac:(vm_compute; reflexivity)); exact R15).
assert (A17 : ew E 17 = w64 out) by (rewrite (EW 17%bv 17%nat ltac:(vm_compute; reflexivity)); exact R17).
assert (A18 : ew E 18 = w64 SHADOW_OFF) by (rewrite (EW 18%bv 18%nat ltac:(vm_compute; reflexivity)); exact R18).
assert (U8 : bv_unsigned (ew E 8) = len) by (rewrite A8; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew E 11) = out)
  by (rewrite A11; apply unsigned_lit_small; unfold PTOP in *; lia).
assert (U12 : bv_unsigned (ew E 12) = p)
  by (rewrite A12; apply unsigned_lit_small; unfold PTOP in *; lia).
assert (U14 : bv_unsigned (ew E 14) = i) by (rewrite A14; apply unsigned_lit_small; lia).
assert (U15 : bv_unsigned (ew E 15) = G_B64)
  by (rewrite A15; apply unsigned_lit_small; unfold G_B64; lia).
assert (U17 : bv_unsigned (ew E 17) = out)
  by (rewrite A17; apply unsigned_lit_small; unfold PTOP in *; lia).
assert (U18 : bv_unsigned (ew E 18) = SHADOW_OFF)
  by (rewrite A18; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U36 : bv_unsigned (ew E 36) = b0) by (rewrite E36; apply unsigned_lit_small; lia).
assert (U37 : bv_unsigned (ew E 37) = b1) by (rewrite E37; apply unsigned_lit_small; lia).
assert (U38 : bv_unsigned (ew E 38) = b2) by (rewrite E38; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold enc_round_ss, st_ok.
cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst
     ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [reflexivity|]). split; [exact HR|].
split.
- split; [vm_compute; reflexivity|]. split.
  + constructor; [|constructor; [|constructor]].
    * (* the three input bytes *)
      unfold enc_rin, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U12. split; [lia|]. split; [unfold PTOP in *; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor; [|constructor]]].
      -- apply (chunk_ok_val tfibsegs E _ p (-2) 1%N (SOff 36 0) b0);
          [rewrite fsw_SOff0, E36; reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
          | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; exact Vb0].
      -- apply (chunk_ok_val tfibsegs E _ p (-1) 1%N (SOff 37 0) b1);
          [rewrite fsw_SOff0, E37; reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
          | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; exact Vb1].
      -- apply (chunk_ok_val tfibsegs E _ p 0 1%N (SOff 38 0) b2);
          [rewrite fsw_SOff0, E38; reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
          | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_r; exact Vb2].
    * (* the output window *)
      unfold enc_rout, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U17. split; [lia|]. split; [unfold PTOP in *; lia|].
      split; [intros o Ho; apply HWout; lia|]. constructor.
  + (* the two regions are apart *)
    apply pairwise_disjoint_of_extents.
    unfold enc_rin, enc_rout, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U12, U17.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold PTOP in *.
    repeat match goal with |- _ /\ _ => split end; try exact I; try lia.
- (* the atom facts *)
  split; [|split; exact I].
  unfold enc_gf. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U18, U12, U17, U11, U8, U14, U15, U36, U37, U38.
  rewrite !Z.pow_0_r.
  unfold PTOP, G_B64, SHADOW_OFF in *.
  repeat split; try lia; try (apply Z.mod_1_r).
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* 6. the shents of a round: the three input bytes, the four output bytes and the live table seat are           *)
(*    addressable, so the token run answers every inline shadow check with 0 and takes no __asan_report_*       *)
(*    branch; and what a run keeps: every byte outside the four output bytes.                                   *)
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

Lemma enc_sh_ok : forall (W : world tfibsegs) mem (E : env) p out,
  U E enc_Bx = SHADOW_OFF -> U E (SOff 12 0) = p -> U E (SOff 17 0) = out -> U E (SOff 11 0) = out ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF (p - 2) 3 ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF out 4 ->
  enc_apart (p - 2) (p + 1) -> enc_apart out (out + 4) ->
  sh_ok tfibsegs enc_Bx enc_SH E (mrestrict (w_H W) mem).
Proof.
intros W mem E p out HB H12 H17 H11 HRAin HRAout Hp Ho.
unfold sh_ok, enc_SH. constructor; [|constructor; [|constructor; [|constructor]]].
- apply (enc_she W mem E 12%nat p (-2) 1 (p - 2) 3 HB H12 HRAin); [lia | lia | lia|].
  intros x Hx. apply Hp. lia.
- apply (enc_she W mem E 17%nat out 0 4 out 4 HB H17 HRAout); [lia | lia | lia|].
  intros x Hx. apply Ho. lia.
- apply (enc_she W mem E 11%nat out 0 4 out 4 HB H11 HRAout); [lia | lia | lia|].
  intros x Hx. apply Ho. lia.
Qed.

Lemma enc_sh_seat : forall (W : world tfibsegs) mem (E : env) p out (n : nat) v,
  U E enc_Bx = SHADOW_OFF -> U E (SOff 12 0) = p -> U E (SOff 17 0) = out -> U E (SOff 11 0) = out ->
  U E (SOff n 0) = G_B64 + v -> 0 <= v < 64 ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF (p - 2) 3 ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF out 4 ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF G_B64 65 ->
  enc_apart (p - 2) (p + 1) -> enc_apart out (out + 4) ->
  sh_ok tfibsegs enc_Bx (enc_SH ++ [mkSHE n 0 1]) E (mrestrict (w_H W) mem).
Proof.
intros W mem E p out n v HB H12 H17 H11 Hn Hv HRAin HRAout HRAt Hp Ho.
unfold sh_ok. apply Forall_app. split.
- exact (enc_sh_ok W mem E p out HB H12 H17 H11 HRAin HRAout Hp Ho).
- constructor; [|constructor].
  apply (enc_she W mem E n (G_B64 + v) 0 1 G_B64 65 HB Hn HRAt); [lia | lia | lia|].
  intros x Hx. unfold G_B64, SHADOW_OFF in *. lia.
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
(* 8. the four table addresses of a round, as the engine leaves them: g_b64 + one of b64_enc's four six-bit     *)
(*    indices (FSW_preset_base64_encode_blocks' enc_ix0 / enc_ix1 / enc_ix2 / enc_ix3 over the engine's own     *)
(*    shift / or / and shapes). Each is the value the register holds at the seat (enc_seat_ro1's `av`).         *)
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

(* g_b64 + a six-bit index is small, so the add does not wrap *)
Lemma enc_U_addG : forall E (y : sv) v, ew E 15 = w64 G_B64 -> U E y = v -> 0 <= v < 64 ->
  U E (SAlu ALU_ADD (SOff 15 0) y) = G_B64 + v.
Proof.
intros E y v H15 Hy Hv. rewrite U_SAlu. cbn [zalu_raw].
rewrite Hy, (U_atom E 15 G_B64 H15 ltac:(unfold G_B64; lia)).
apply zcanon_id. unfold M64, G_B64. lia.
Qed.

Lemma enc_denot_of_U : forall E (x : sv) v, U E x = v -> sv_denot E x = w64 v.
Proof. intros E x v H. rewrite denot_lit_U, H. reflexivity. Qed.

(* 0x84440  srli a3,t0,2 *)
Lemma enc_U_t0 : forall E b0, ew E 36 = w64 b0 -> 0 <= b0 < 256 ->
  U E (SAlu ALU_SRL (SOff 36 0) (SLit 2)) = b0 / 4.
Proof.
intros E b0 H36 Hb.
rewrite (enc_U_srl E (SOff 36 0) 2 b0 ltac:(lia) (U_atom E 36 b0 H36 ltac:(lia))).
exact (enc_ix0 b0 Hb).
Qed.

(* 0x84470..0x84484  slli t0,t0,0x10; slli t1,t1,8; or a3,t1,t0; slli a3,a3,0x2e; srli a2,a3,0x3a *)
Lemma enc_U_t1 : forall E b0 b1, ew E 36 = w64 b0 -> ew E 37 = w64 b1 -> 0 <= b0 < 256 -> 0 <= b1 < 256 ->
  U E (SAlu ALU_SRL (SAlu ALU_SLL
         (SAlu ALU_OR (SAlu ALU_SLL (SOff 37 0) (SLit 8)) (SAlu ALU_SLL (SOff 36 0) (SLit 16))) (SLit 46))
       (SLit 58))
  = (b0 mod 4) * 16 + b1 / 16.
Proof.
intros E b0 b1 H36 H37 H0 H1.
assert (A1 : U E (SAlu ALU_SLL (SOff 37 0) (SLit 8)) = Z.shiftl b1 8 mod 2 ^ 64)
  by (apply (enc_U_sll E (SOff 37 0) 8 b1); [lia | apply (U_atom E 37 b1 H37); lia]).
assert (A0 : U E (SAlu ALU_SLL (SOff 36 0) (SLit 16)) = Z.shiftl b0 16 mod 2 ^ 64)
  by (apply (enc_U_sll E (SOff 36 0) 16 b0); [lia | apply (U_atom E 36 b0 H36); lia]).
assert (AO : U E (SAlu ALU_OR (SAlu ALU_SLL (SOff 37 0) (SLit 8)) (SAlu ALU_SLL (SOff 36 0) (SLit 16)))
             = b0 * 65536 + b1 * 256).
{ rewrite (enc_U_or E _ _ _ _ A1 A0), (enc_or1 b0 b1 H0 H1). apply Z.mod_small. lia. }
rewrite (enc_U_srl E _ 58 _ ltac:(lia) (enc_U_sll E _ 46 _ ltac:(lia) AO)).
exact (enc_ix1 b0 b1 H0 H1).
Qed.

(* 0x844b4..0x844c0  or a3,t1,a7; slli a3,a3,0x34; srli a2,a3,0x3a *)
Lemma enc_U_t2 : forall E b1 b2, ew E 37 = w64 b1 -> ew E 38 = w64 b2 -> 0 <= b1 < 256 -> 0 <= b2 < 256 ->
  U E (SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_OR (SAlu ALU_SLL (SOff 37 0) (SLit 8)) (SOff 38 0)) (SLit 52))
       (SLit 58))
  = (b1 mod 16) * 4 + b2 / 64.
Proof.
intros E b1 b2 H37 H38 H1 H2.
assert (A1 : U E (SAlu ALU_SLL (SOff 37 0) (SLit 8)) = Z.shiftl b1 8 mod 2 ^ 64)
  by (apply (enc_U_sll E (SOff 37 0) 8 b1); [lia | apply (U_atom E 37 b1 H37); lia]).
assert (AO : U E (SAlu ALU_OR (SAlu ALU_SLL (SOff 37 0) (SLit 8)) (SOff 38 0)) = b1 * 256 + b2).
{ rewrite (enc_U_or E _ _ _ _ A1 (U_atom E 38 b2 H38 ltac:(lia))), (enc_or2 b1 b2 H1 H2).
  apply Z.mod_small. lia. }
rewrite (enc_U_srl E _ 58 _ ltac:(lia) (enc_U_sll E _ 52 _ ltac:(lia) AO)).
exact (enc_ix2 b1 b2 H1 H2).
Qed.

(* 0x844f4  andi a2,a7,0x3f *)
Lemma enc_U_t3 : forall E b2, ew E 38 = w64 b2 -> 0 <= b2 < 256 ->
  U E (SAlu ALU_AND (SOff 38 0) (SLit 63)) = b2 mod 64.
Proof.
intros E b2 H38 H2.
rewrite (U_and_lit E (SOff 38 0) 63 ltac:(lia)), (U_atom E 38 b2 H38 ltac:(lia)).
exact (enc_ix3 b2 H2).
Qed.

(* `add rd, rm, rn` on two atoms, as the loop head recomputes the input pointer *)
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

(* every byte of fs.asan's four loaded segments is an image byte (the segments are contiguous) *)
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

(* ---------------------------------------------------------------------------------------------------------- *)
(* 10. THE CALL. Everything below is one call of preset_base64_encode: its entry (ly0 / St0 / U0 / W0 / mem0 /   *)
(*     md0 / regs0), the state the one fuzz_malloc call left (lyc / Sc / Wc / memc / mdc, the output block q of  *)
(*     enc_size len bytes), and its numerals. Only the output block's bytes are written after the call, so the   *)
(*     walk's whole invariant is: the journal, ARU, memory AGREEMENT with memc outside [q, q + enc_size len),    *)
(*     and the base64 prefix written so far.                                                                     *)
(* ---------------------------------------------------------------------------------------------------------- *)
Section R.
Variable ly0 : alayout.  Variable St0 : astate.  Variable U0 : list (Z * Z).
Variable W0 : world tfibsegs.  Variable mem0 : word -> option byte.  Variable md0 : Model.
Variable regs0 : bvmap 5 word.
Variable lyc : alayout.  Variable Sc : astate.  Variable Wc : world tfibsegs.
Variable memc : word -> option byte.  Variable mdc : Model.
Variable data len q live peak cnt fail kd : Z.
Variable bs : list Z.

Hypothesis HLN : 0 <= len <= 2 ^ 27.
Hypothesis HBS : WriterSpec.bytes_ok bs.
Hypothesis HBSL : Z.of_nat (length bs) = len.
Hypothesis HDLO : 4096 <= data.
Hypothesis HDHI : data + len <= alloc_ceiling.
(* the state after the call *)
Hypothesis HARUc : ARU tfibsegs B lyc Sc (U0 ++ [(q - HEAD, HEAD)]) Wc memc mdc.
Hypothesis HHEADS : fs_heads B lyc Sc (U0 ++ [(q - HEAD, HEAD)]).
Hypothesis HQB : In (q - HEAD, enc_size len + HEAD) (ablocks B lyc Sc).
Hypothesis HAB : ablocks B lyc Sc = ablocks B ly0 St0 ++ [(q - HEAD, enc_size len + HEAD)].
Hypothesis HQ16 : 4096 + HEAD <= q.
(* the input block, when there is one: an ENTRY block, so the call's new block is a different entry of the list *)
Hypothesis HDB : 0 < len -> In (data - HEAD, kd + HEAD) (ablocks B ly0 St0) /\ len <= kd /\ 0 < kd.

Definition encR_out (a : Z) : Prop := q <= a < q + enc_size len.

Lemma encR_size_pos : 1 <= enc_size len <= 2 ^ 28.
Proof.
unfold enc_size. pose proof (Z.div_le_mono 0 (len + 2) 3 ltac:(lia) ltac:(lia)) as H1.
pose proof (Z.div_le_mono (len + 2) (2 ^ 27 + 2) 3 ltac:(lia) ltac:(lia)) as H2.
change (0 / 3) with 0 in H1. lia.
Qed.

(* the output block's extent: apart from the band, below the ceiling, never an image byte *)
Lemma encR_out_facts :
  enc_apart q (q + enc_size len) /\ q + enc_size len <= alloc_ceiling /\
  (forall a, encR_out a -> ~ in_img tfibsegs a).
Proof.
pose proof encR_size_pos as HM.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (ARU_AR tfibsegs B lyc Sc _ Wc memc mdc HARUc) as HAR.
assert (Hrq : req_size (enc_size len + HEAD) = enc_size len + HEAD)
  by (unfold req_size; destruct (enc_size len + HEAD =? 0) eqn:E;
      [apply Z.eqb_eq in E; unfold HEAD in *; lia | reflexivity]).
destruct (al_blocks tfibsegs B LAWS lyc Sc Wc (unpoison (U0 ++ [(q - HEAD, HEAD)]) memc) mdc _ _ HAR HQB)
  as (_ & _ & Hceil & _).
rewrite Hrq in Hceil.
split; [|split].
- intros x Hx.
  destruct (enc_blk_bounds lyc Sc Wc (unpoison (U0 ++ [(q - HEAD, HEAD)]) memc) mdc _ _ x HAR HQB
    ltac:(rewrite Hrq; unfold HEAD in *; lia)) as (_ & _ & A3). exact A3.
- unfold HEAD in *. lia.
- intros a Ha. unfold encR_out in Ha.
  exact (enc_blk_not_img lyc Sc Wc (unpoison (U0 ++ [(q - HEAD, HEAD)]) memc) mdc _ _ a HAR HQB
    ltac:(rewrite Hrq; unfold HEAD in *; lia)).
Qed.

Lemma encR_band_not_out : forall i, SHADOW_OFF <= i < SHADOW_OFF + 17592186044416 -> ~ encR_out i.
Proof. intros i Hi Hout. exact (proj1 encR_out_facts i Hout Hi). Qed.
Lemma encR_img_not_out : forall a, in_img tfibsegs a -> ~ encR_out a.
Proof. intros a Ha Hout. exact (proj2 (proj2 encR_out_facts) a Hout Ha). Qed.
Lemma encR_high_not_out : forall a, alloc_ceiling <= a -> ~ encR_out a.
Proof. intros a Ha Hout. pose proof (proj1 (proj2 encR_out_facts)). unfold encR_out in Hout. lia. Qed.

(* the output window at any state of the walk: addressable, present and writable *)
Lemma encR_ra_out : forall mem md, ARU tfibsegs B lyc Sc (U0 ++ [(q - HEAD, HEAD)]) Wc mem md ->
  range_addressable (aview tfibsegs (w_H Wc) mem) SHADOW_OFF q (enc_size len).
Proof.
intros mem md HARU. pose proof encR_size_pos as HM.
exact (enc_ra_block lyc Sc _ Wc mem md q (enc_size len) q (enc_size len) HARU HHEADS HQB ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.

Lemma encR_wr_out : forall mem md, ARU tfibsegs B lyc Sc (U0 ++ [(q - HEAD, HEAD)]) Wc mem md ->
  forall o, 0 <= o < enc_size len -> writable_at tfibsegs (mrestrict (w_H Wc) mem) (q + o).
Proof.
intros mem md HARU o Ho. pose proof encR_size_pos as HM.
assert (Hrq : req_size (enc_size len + HEAD) = enc_size len + HEAD)
  by (unfold req_size; destruct (enc_size len + HEAD =? 0) eqn:E;
      [apply Z.eqb_eq in E; unfold HEAD in *; lia | reflexivity]).
exact (proj2 (enc_blk_present lyc Sc _ Wc mem md (q - HEAD) (enc_size len + HEAD) (q + o) HARU HQB
  ltac:(rewrite Hrq; unfold HEAD in *; lia))).
Qed.

(* the input window at any state of the walk *)
Lemma encR_ra_in : forall mem md, ARU tfibsegs B lyc Sc (U0 ++ [(q - HEAD, HEAD)]) Wc mem md -> 0 < len ->
  range_addressable (aview tfibsegs (w_H Wc) mem) SHADOW_OFF data len.
Proof.
intros mem md HARU Hlen. destruct (HDB Hlen) as (Hin & Hkd & Hkd0).
exact (enc_ra_block lyc Sc _ Wc mem md data kd data len HARU HHEADS
  ltac:(rewrite HAB; apply in_or_app; left; exact Hin) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
Qed.

(* the input block and the output block are two entries of AR's pairwise-disjoint block list *)
Lemma encR_in_out : 0 < len -> forall i, data <= i < data + len -> ~ encR_out i.
Proof.
intros Hlen i Hi Hout. unfold encR_out in Hout. destruct (HDB Hlen) as (Hin & Hkd & Hkd0).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (ARU_AR tfibsegs B lyc Sc _ Wc memc mdc HARUc) as HAR.
pose proof encR_size_pos as HM.
destruct (al_sep tfibsegs B LAWS lyc Sc Wc (unpoison (U0 ++ [(q - HEAD, HEAD)]) memc) mdc HAR) as (Hpw & _).
destruct (in_split _ _ Hin) as (l1 & l2 & Hsp).
set (fb := fun b : Z * Z => (fst b, req_size (snd b))) in *.
set (ff := fun fr : Z * Z => (frame_addr lyc (fst fr) (snd fr), fs_frame_bytes (fst fr))) in *.
assert (Hl : map fb (ablocks B lyc Sc) ++ map ff (frames Sc)
           = map fb l1 ++ fb (data - HEAD, kd + HEAD) ::
             (map fb l2 ++ fb (q - HEAD, enc_size len + HEAD) :: map ff (frames Sc)))
  by (rewrite HAB, Hsp, !map_app, <- !app_assoc; cbn [map app]; reflexivity).
pose proof (YCbq.pairwise_In2 zdisjoint _ (fb (data - HEAD, kd + HEAD)) (fb (q - HEAD, enc_size len + HEAD))
  (map fb l1) (map fb l2) (map ff (frames Sc)) Hpw Hl) as Hdj.
unfold zdisjoint, fb in Hdj. cbn [fst snd] in Hdj.
assert (Hrq : forall n, 0 < n -> req_size (n + HEAD) = n + HEAD)
  by (intros n Hn; unfold req_size; destruct (n + HEAD =? 0) eqn:E;
      [apply Z.eqb_eq in E; unfold HEAD in *; lia | reflexivity]).
rewrite (Hrq kd ltac:(lia)), (Hrq (enc_size len) ltac:(lia)) in Hdj.
unfold HEAD in *. lia.
Qed.

(* the call's new block is NOT one of the entry blocks: the list would hold it twice, against AR's pairwise
   disjointness (a block of at least HEAD bytes is not disjoint from itself) *)
Lemma encR_new_block : ~ In (q - HEAD, enc_size len + HEAD) (ablocks B ly0 St0).
Proof.
intros Hin. pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof encR_size_pos as HM.
pose proof (ARU_AR tfibsegs B lyc Sc _ Wc memc mdc HARUc) as HAR.
destruct (al_sep tfibsegs B LAWS lyc Sc Wc (unpoison (U0 ++ [(q - HEAD, HEAD)]) memc) mdc HAR) as (Hpw & _).
destruct (in_split _ _ Hin) as (l1 & l2 & Hsp).
set (fb := fun b : Z * Z => (fst b, req_size (snd b))) in *.
set (ff := fun fr : Z * Z => (frame_addr lyc (fst fr) (snd fr), fs_frame_bytes (fst fr))) in *.
assert (Hl : map fb (ablocks B lyc Sc) ++ map ff (frames Sc)
           = map fb l1 ++ fb (q - HEAD, enc_size len + HEAD) ::
             (map fb l2 ++ fb (q - HEAD, enc_size len + HEAD) :: map ff (frames Sc)))
  by (rewrite HAB, Hsp, !map_app, <- !app_assoc; cbn [map app]; reflexivity).
pose proof (YCbq.pairwise_In2 zdisjoint _ (fb (q - HEAD, enc_size len + HEAD))
  (fb (q - HEAD, enc_size len + HEAD)) (map fb l1) (map fb l2) (map ff (frames Sc)) Hpw Hl) as Hdj.
unfold zdisjoint, fb in Hdj. cbn [fst snd] in Hdj.
assert (Hrq : req_size (enc_size len + HEAD) = enc_size len + HEAD)
  by (unfold req_size; destruct (enc_size len + HEAD =? 0) eqn:E;
      [apply Z.eqb_eq in E; unfold HEAD in *; lia | reflexivity]).
rewrite Hrq in Hdj. unfold HEAD in *. lia.
Qed.

(* ---- the walk's invariant after the call: the journal over the unpoisoned memories, ARU, and AGREEMENT with
   the call's memory everywhere but the output block ---- *)
Definition encR_agree (mem : word -> option byte) : Prop :=
  forall x : word, ~ encR_out (bv_unsigned x) -> mem x = memc x.
Definition encR_J (mem : word -> option byte) (md : Model) : Prop :=
  ajournal tfibsegs B STK_preset_base64_encode (spZ regs0) FS_PSTAT_FP ly0 St0 W0 (unpoison U0 mem0) md0 []
    lyc Sc Wc (unpoison (U0 ++ [(q - HEAD, HEAD)]) mem) md EV_preset_base64_encode.
Definition encR_inv (mem : word -> option byte) (md : Model) : Prop :=
  encR_J mem md /\ ARU tfibsegs B lyc Sc (U0 ++ [(q - HEAD, HEAD)]) Wc mem md /\ encR_agree mem.

Lemma encR_mb : forall mem a, encR_agree mem -> ~ encR_out a -> 0 <= a < 2 ^ 64 ->
  mbyte tfibsegs (mrestrict (w_H Wc) mem) a = mbyte tfibsegs (mrestrict (w_H Wc) memc) a.
Proof.
intros mem a HA Ha Hr. unfold mbyte, mrestrict.
rewrite (HA (Z_to_bv 64 a) ltac:(rewrite (wz a Hr); exact Ha)). reflexivity.
Qed.

Lemma encR_val : forall mem a (n : nat) v, encR_agree mem -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, a <= i < a + Z.of_nat n -> ~ encR_out i) ->
  val_mem tfibsegs (mrestrict (w_H Wc) memc) a n v -> val_mem tfibsegs (mrestrict (w_H Wc) mem) a n v.
Proof.
intros mem a n v HA Ha Han HX HV k Hk.
rewrite (encR_mb mem (a + Z.of_nat k) HA (HX (a + Z.of_nat k) ltac:(lia)) ltac:(lia)). exact (HV k Hk).
Qed.

(* the four allocator statics and the table are image bytes, so the walk never writes them *)
Lemma encR_stat_keep : forall mem a (n : nat) v, encR_agree mem ->
  65536 <= a -> a + Z.of_nat n <= 6279168 ->
  val_mem tfibsegs (mrestrict (w_H Wc) memc) a n v -> val_mem tfibsegs (mrestrict (w_H Wc) mem) a n v.
Proof.
intros mem a n v HA Hlo Hhi HV.
apply (encR_val mem a n v HA ltac:(lia) ltac:(lia)); [|exact HV].
intros i Hi. apply encR_img_not_out. apply enc_img_rng. lia.
Qed.

Lemma encR_glob_keep : forall mem l p c f, encR_agree mem ->
  fs_glob tfibsegs Wc memc l p c f -> fs_glob tfibsegs Wc mem l p c f.
Proof.
intros mem l p c f HA (G1 & G2 & G3 & G4 & Hr).
unfold fs_glob, fs_glob_at, G_LIVE, G_PEAK, G_COUNT, G_FAIL in *.
split; [apply (encR_stat_keep mem _ 8%nat); [exact HA | lia | cbn [Z.of_nat]; lia | exact G1]|].
split; [apply (encR_stat_keep mem _ 8%nat); [exact HA | lia | cbn [Z.of_nat]; lia | exact G2]|].
split; [apply (encR_stat_keep mem _ 8%nat); [exact HA | lia | cbn [Z.of_nat]; lia | exact G3]|].
split; [apply (encR_stat_keep mem _ 8%nat); [exact HA | lia | cbn [Z.of_nat]; lia | exact G4] | exact Hr].
Qed.

Lemma encR_tab_keep : forall mem, encR_agree mem ->
  (forall v, 0 <= v < 64 -> val_mem tfibsegs (mrestrict (w_H Wc) memc) (G_B64 + v) 1 (WriterSpec.b64c v)) ->
  forall v, 0 <= v < 64 -> val_mem tfibsegs (mrestrict (w_H Wc) mem) (G_B64 + v) 1 (WriterSpec.b64c v).
Proof.
intros mem HA HT v Hv.
apply (encR_stat_keep mem (G_B64 + v) 1%nat); [exact HA | unfold G_B64; lia | unfold G_B64; cbn [Z.of_nat]; lia
  | exact (HT v Hv)].
Qed.

(* a stack byte is never an output byte *)
Lemma encR_hi_keep : forall mem a (n : nat) v, encR_agree mem -> alloc_ceiling <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  val_mem tfibsegs (mrestrict (w_H Wc) memc) a n v -> val_mem tfibsegs (mrestrict (w_H Wc) mem) a n v.
Proof.
intros mem a n v HA Hlo Hhi HV.
apply (encR_val mem a n v HA ltac:(pose proof alloc_ceiling_val as (CR & _); lia) ltac:(lia)); [|exact HV].
intros i Hi. apply encR_high_not_out. lia.
Qed.

(* the shadow of a range outside the output block, and of the output block itself, at an invariant memory *)
Lemma encR_ra_keep : forall mem a n, encR_agree mem -> 0 <= a -> a + n <= 2 ^ 47 ->
  range_addressable (aview tfibsegs (w_H Wc) memc) SHADOW_OFF a n ->
  range_addressable (aview tfibsegs (w_H Wc) mem) SHADOW_OFF a n.
Proof.
intros mem a n HA Ha Han HRA.
exact (enc_ra_agree (w_H Wc) memc mem encR_out a n HA Ha Han encR_band_not_out HRA).
Qed.

(* ---- what the call's entry memory holds (the fuzz_malloc call's post, read at memc) ---- *)
Hypothesis HRBc : fs_rblock tfibsegs B lyc Sc Wc memc q (enc_size len).
Hypothesis HGLOBc : fs_glob tfibsegs Wc memc (live + enc_size len) (Z.max peak (live + enc_size len))
  ((cnt + 1) mod 2 ^ 64) fail.
Hypothesis HTABc : forall v, 0 <= v < 64 ->
  val_mem tfibsegs (mrestrict (w_H Wc) memc) (G_B64 + v) 1 (WriterSpec.b64c v).
Hypothesis HRATc : range_addressable (aview tfibsegs (w_H Wc) memc) SHADOW_OFF G_B64 65.
Hypothesis HDATc : garr8 tfibsegs (mrestrict (w_H Wc) memc) data bs.
Hypothesis HKEEPc : forall i, 0 <= i < len ->
  mbyte tfibsegs (mrestrict (w_H Wc) memc) (data + i) = mbyte tfibsegs (mrestrict (w_H W0) mem0) (data + i).
(* the entry frame: ra, s0, s1, s2 saved by the prologue, still there after the call *)
Hypothesis HFRAMEc :
  val_mem tfibsegs (mrestrict (w_H Wc) memc) (spZ regs0 - 8) 8 (bv_unsigned (getr regs0 1)) /\
  val_mem tfibsegs (mrestrict (w_H Wc) memc) (spZ regs0 - 16) 8 (bv_unsigned (getr regs0 8)) /\
  val_mem tfibsegs (mrestrict (w_H Wc) memc) (spZ regs0 - 24) 8 (bv_unsigned (getr regs0 9)) /\
  val_mem tfibsegs (mrestrict (w_H Wc) memc) (spZ regs0 - 32) 8 (bv_unsigned (getr regs0 18)).
Hypothesis HSP0 : spZ regs0 mod 16 = 0 /\ alloc_ceiling + STK_preset_base64_encode <= spZ regs0 /\
  spZ regs0 <= 2 ^ 47.
Hypothesis HRA0 : YK0s.ret_ok (getr regs0 1).

(* the four saved registers of the entry, as the resumed states' extra atoms 32 .. 35 *)
Definition encR_extra : list word := [getr regs0 1; getr regs0 8; getr regs0 9; getr regs0 18].
Definition encR_cs : list YP09.chunk :=
  [YP09.mkChunk 24 (CVal 8 (SOff 32 0)); YP09.mkChunk 16 (CVal 8 (SOff 33 0));
   YP09.mkChunk 8 (CVal 8 (SOff 34 0)); YP09.mkChunk 0 (CVal 8 (SOff 35 0))].
(* what the callee-saved registers hold at `ret`: sp back up by the frame, s0 / s1 / s2 reloaded, the rest untouched *)
Definition encR_expect (r : bv 5) : sv :=
  match bv_unsigned r with
  | 2 => SOff 2 32 | 8 => SOff 33 0 | 9 => SOff 34 0 | 18 => SOff 35 0
  | z => SOff (Z.to_nat z) 0
  end.

Lemma encR_chunks : forall mem (regsX : bvmap 5 word), encR_agree mem ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regsX encR_extra) (mrestrict (w_H Wc) mem) (spZ regs0 - 32)) encR_cs.
Proof.
intros mem regsX HA. pose proof HSP0 as (Hal16 & Hceil & H47). pose proof alloc_ceiling_val as (CR & _).
destruct HFRAMEc as (V1 & V8 & V9 & V18).
assert (HSTK : STK_preset_base64_encode
  = ltac:(let v := eval vm_compute in STK_preset_base64_encode in exact v)) by reflexivity.
assert (F : forall (j : nat) (r : bv 5) od, nth j encR_extra (Z_to_bv 64 0) = getr regs0 r ->
  val_mem tfibsegs (mrestrict (w_H Wc) memc) (spZ regs0 - 32 + od) 8 (bv_unsigned (getr regs0 r)) ->
  0 <= od -> od + 8 <= 32 ->
  YP09.chunk_ok tfibsegs (Ereg regsX encR_extra) (mrestrict (w_H Wc) mem) (spZ regs0 - 32)
    (YP09.mkChunk od (CVal 8 (SOff (32 + j) 0)))).
{ intros j r od Hj Hv Ho1 Ho2.
  apply (chunk_ok_val tfibsegs _ _ _ od 8%N (SOff (32 + j) 0) (bv_unsigned (getr regs0 r)));
    first [ solve [apply u64_range]
          | lazymatch goal with |- sv_denot _ _ = _ =>
              rewrite fsw_SOff0, ew_Ereg_extra, Hj; symmetry; apply Z_to_bv_bv_unsigned end
          | solve [cbn; lia]
          | idtac ].
  cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add].
  apply (encR_hi_keep mem (spZ regs0 - 32 + od) 8%nat _ HA); [lia | cbn [Z.of_nat]; lia | exact Hv]. }
unfold encR_cs. repeat constructor.
- apply (F 0%nat 1%bv 24 eq_refl); [replace (spZ regs0 - 32 + 24) with (spZ regs0 - 8) by lia; exact V1 | lia | lia].
- apply (F 1%nat 8%bv 16 eq_refl); [replace (spZ regs0 - 32 + 16) with (spZ regs0 - 16) by lia; exact V8 | lia | lia].
- apply (F 2%nat 9%bv 8 eq_refl); [replace (spZ regs0 - 32 + 8) with (spZ regs0 - 24) by lia; exact V9 | lia | lia].
- apply (F 3%nat 18%bv 0 eq_refl); [replace (spZ regs0 - 32 + 0) with (spZ regs0 - 32) by lia; exact V18 | lia | lia].
Qed.

(* the call's post, as encode_spec's success arm states it *)
Definition encR_Q : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' W' regs' mem' md' =>
    getr regs' 10 = w64 q /\ 4096 + HEAD <= q /\
    ablocks B ly' S' = ablocks B ly0 St0 ++ [(q - HEAD, enc_size len + HEAD)] /\
    fs_rblock tfibsegs B ly' S' W' mem' q (enc_size len) /\
    zbytes_at tfibsegs W' mem' q (WriterSpec.b64_enc bs ++ [0]) /\
    (forall i, 0 <= i < len -> mbyte tfibsegs (mrestrict (w_H W') mem') (data + i)
                             = mbyte tfibsegs (mrestrict (w_H W0) mem0) (data + i)) /\
    fs_glob tfibsegs W' mem' (live + enc_size len) (Z.max peak (live + enc_size len)) ((cnt + 1) mod 2 ^ 64) fail.

(* ---- the terminating 0 and the epilogue (0x84700 .. 0x84728) ---- *)
Definition encR_nul_ss : sstate :=
  mkSS 0x84700 sr_atoms [YP09.mkRegion (Some 11%nat) 0 1 0 1 []; fstk_ret 32 encR_cs] None
    (mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (11%nat, mkAF 4096 PTOP 0);
              (18%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] []).
Definition encR_nul_SH : list shent := [mkSHE 11 0 1].

Lemma encR_nul : forall ms md,
  encR_inv (ms_mem ms) md ->
  garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) q (WriterSpec.b64_enc bs) ->
  ms = mkst (ms_regs ms) (w64 0x84700) (ms_mem ms) (seg_rom tfibsegs) ->
  getr (ms_regs ms) 10 = w64 q ->
  getr (ms_regs ms) 11 = w64 (q + 4 * ((len + 2) / 3)) ->
  getr (ms_regs ms) 18 = w64 SHADOW_OFF ->
  spZ (ms_regs ms) = spZ regs0 - 32 ->
  (forall z, acallee_saved z -> z <> 2 -> z <> 8 -> z <> 9 -> z <> 18 ->
     getr (ms_regs ms) (Z_to_bv 5 z) = getr regs0 (Z_to_bv 5 z)) ->
  SRr tfibsegs Wc (mkCfg ms md)
    (fpostU tfibsegs B STK_preset_base64_encode (spZ regs0) FS_PSTAT_FP regs0 ly0 St0 U0 W0 mem0 md0
       EV_preset_base64_encode (U0 ++ [(q - HEAD, HEAD)]) encR_Q).
Proof.
intros ms md (HJ & HARU & HA) HPRE Hms R10 R11 R18 Rsp Rk.
unfold encR_J in HJ.
pose proof encR_size_pos as HM. pose proof alloc_ceiling_val as (CR & _).
pose proof HSP0 as (Hal16 & Hceil & H47).
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof encR_out_facts as (HAPq & HQceil & HQimg).
assert (HSTK : STK_preset_base64_encode
  = ltac:(let v := eval vm_compute in STK_preset_base64_encode in exact v)) by reflexivity.
assert (HQlo : 4112 <= q) by (unfold HEAD in *; lia).
assert (Hqn : q + 4 * ((len + 2) / 3) = q + enc_size len - 1) by (unfold enc_size; lia).
assert (E2 : bv_unsigned (ew (Ereg (ms_regs ms) encR_extra) 2) = spZ regs0 - 32)
  by (rewrite (ew_Ereg_nat (ms_regs ms) _ 2 2%bv eq_refl); exact Rsp).
assert (A11 : ew (Ereg (ms_regs ms) encR_extra) 11 = w64 (q + enc_size len - 1))
  by (rewrite (ew_Ereg_nat (ms_regs ms) _ 11 11%bv eq_refl), R11, Hqn; reflexivity).
assert (A18 : ew (Ereg (ms_regs ms) encR_extra) 18 = w64 SHADOW_OFF)
  by (rewrite (ew_Ereg_nat (ms_regs ms) _ 18 18%bv eq_refl); exact R18).
assert (E11 : bv_unsigned (ew (Ereg (ms_regs ms) encR_extra) 11) = q + enc_size len - 1)
  by (rewrite A11; apply unsigned_lit_small; unfold PTOP in *; lia).
assert (E18 : bv_unsigned (ew (Ereg (ms_regs ms) encR_extra) 18) = SHADOW_OFF)
  by (rewrite A18; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (HS : st_ok tfibsegs (Ereg (ms_regs ms) encR_extra) encR_nul_ss (restrict (w_H Wc) ms)).
{ rewrite Hms, restrict_mkst_fx. unfold encR_nul_ss. apply (entry_st_ok_full tfibsegs).
  - apply regs_ok_Ereg.
  - vm_compute; reflexivity.
  - constructor; [|constructor; [|constructor]].
    + unfold region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite E11. split; [lia|]. split; [unfold PTOP; lia|]. split; [|constructor].
      intros o Ho. replace (q + enc_size len - 1 + o) with (q + (enc_size len - 1)) by lia.
      exact (encR_wr_out (ms_mem ms) md HARU (enc_size len - 1) ltac:(lia)).
    + exact (fsw_resume_frame_ok B STK_preset_base64_encode (spZ regs0) FS_PSTAT_FP ly0 St0 W0
        (unpoison U0 mem0) md0 [] lyc Sc (U0 ++ [(q - HEAD, HEAD)]) Wc (ms_mem ms) md
        EV_preset_base64_encode (Ereg (ms_regs ms) encR_extra) 32 encR_cs HJ HARU E2 ltac:(lia)
        (encR_chunks (ms_mem ms) (ms_regs ms) HA)).
  - apply pairwise_disjoint_of_extents.
    unfold fstk_ret, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, E11.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat match goal with |- _ /\ _ => split end; try exact I. left. lia.
  - split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E11, E18. change (2 ^ 4) with 16. rewrite !Z.pow_0_r.
    split; [split; [lia | split; [rewrite Zminus_mod, Hal16; reflexivity | lia]]|].
    split; [|split; [|exact I]].
    + split; [unfold PTOP; lia | split; [apply Z.mod_1_r | lia]].
    + split; [lia | split; [apply Z.mod_1_r | lia]]. }
assert (SHOK : sh_ok tfibsegs enc_Bx encR_nul_SH (Ereg (ms_regs ms) encR_extra)
  (mrestrict (w_H Wc) (ms_mem ms))).
{ unfold sh_ok, encR_nul_SH. constructor; [|constructor].
  apply (enc_she Wc (ms_mem ms) (Ereg (ms_regs ms) encR_extra) 11%nat (q + enc_size len - 1) 0 1 q
    (enc_size len)).
  - apply (U_atom _ 18 SHADOW_OFF A18). unfold SHADOW_OFF. lia.
  - apply (U_atom _ 11 _ A11). unfold PTOP in *. lia.
  - exact (encR_ra_out (ms_mem ms) md HARU).
  - lia.
  - lia.
  - lia.
  - intros x Hx. apply HAPq. lia. }
fsw_aj_run_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan.
all: first
  [ solve [ cbn [encR_nul_ss ss_mem];
            eapply awr_ok_cons_gen with (k := 11%nat) (b := q + enc_size len - 1);
            first [ solve [reflexivity] | solve [exact E11]
                  | solve [fsw_awr_ret E2 32]
                  | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha; left; right; right; left;
                    exists (q - HEAD), (enc_size len + HEAD);
                    split; [exact HQB|]; split; [exact encR_new_block|];
                    unfold req_size; destruct (enc_size len + HEAD =? 0) eqn:EQ;
                    [apply Z.eqb_eq in EQ; unfold HEAD in *; lia | unfold HEAD in *; lia] ] ]
  | idtac ].
(* the run stored the 0 at a1 and read the frame back; the rest of the output block is as the walk left it *)
assert (EX : forall n, (n < 36)%nat ->
  ew (ewset (ewset (Ereg (ms_regs ms) encR_extra) 36 w) 37 w0) n = ew (Ereg (ms_regs ms) encR_extra) n)
  by (intros n Hn; rewrite !ew_ewset_other by lia; reflexivity).
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (q + enc_size len - 1 <= a < q + enc_size len) ->
  ~ (spZ regs0 - 32 <= a < spZ regs0) ->
  mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms0)) a = mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) a).
{ intros a Ha H1 H2. unfold mbyte.
  rewrite (enc_frame_X (Ereg (ms_regs ms) encR_extra) (ss_mem encR_nul_ss)
    (mrestrict (w_H Wc) (ms_mem ms)) (mrestrict (w_H Wc) (ms_mem ms0))
    (fun x => (q + enc_size len - 1 <= x < q + enc_size len) \/ (spZ regs0 - 32 <= x < spZ regs0)) HFr);
    [reflexivity | | rewrite (wz a Ha); intros [Hx|Hx]; [exact (H1 Hx) | exact (H2 Hx)]].
  intros x (r & Hin & Hr). cbn [encR_nul_ss ss_mem In] in Hin.
  destruct Hin as [<-|[<-|[]]];
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val fstk_ret] in Hr;
    [rewrite E11 in Hr; left; lia | rewrite E2 in Hr; right; lia]. }
assert (VK : forall a (n : nat) v, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall i, a <= i < a + Z.of_nat n -> ~ encR_out i) ->
  (forall i, a <= i < a + Z.of_nat n -> ~ (spZ regs0 - 32 <= i < spZ regs0)) ->
  val_mem tfibsegs (mrestrict (w_H Wc) memc) a n v ->
  val_mem tfibsegs (mrestrict (w_H Wc) (ms_mem ms0)) a n v).
{ intros a n v Ha Han X1 X3 HV k Hk.
  rewrite (KEEP (a + Z.of_nat k) ltac:(lia)
    ltac:(intros Hc; apply (X1 (a + Z.of_nat k) ltac:(lia)); unfold encR_out; lia)
    (X3 (a + Z.of_nat k) ltac:(lia))).
  exact (encR_val (ms_mem ms) a n v HA Ha Han X1 HV k Hk). }
(* the NUL byte the run stored *)
assert (VNUL : val_mem tfibsegs (mrestrict (w_H Wc) (ms_mem ms0)) (q + enc_size len - 1) 1 0).
{ pose proof (fsw_region_nth (ewset (ewset (Ereg (ms_regs ms) encR_extra) 36 w) 37 w0) _
    (restrict (w_H Wc) ms0) 0 (YP09.mkRegion (Some 11%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 0))])
    HS ltac:(vm_compute; reflexivity)) as HR.
  cbn [ms_mem restrict] in HR.
  replace (q + enc_size len - 1) with (q + enc_size len - 1 + 0) at 1 by lia.
  apply (fsw_field (ewset (ewset (Ereg (ms_regs ms) encR_extra) 36 w) 37 w0) _ 11
    (q + enc_size len - 1) _ 0 1 0 1 0 1%N (SLit 0) 0 HR);
    first [ solve [rewrite EX by lia; exact E11] | solve [cbn; tauto] | solve [reflexivity]
          | solve [cbn [Z.of_N]; lia] ]. }
(* the registers at the ret *)
assert (R1F : getr (ms_regs ms0) 1 = getr regs0 1).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) _ _ ms0 1%bv HS).
  lazymatch goal with |- sv_denot _ ?t = _ => let t' := eval vm_compute in t in change t with t' end.
  rewrite fsw_SOff0, EX by lia. change 32%nat with (32 + 0)%nat. rewrite ew_Ereg_extra. reflexivity. }
assert (Ra0 : getr (ms_regs ms0) 10 = w64 q).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) _ _ ms0 10%bv HS).
  lazymatch goal with |- sv_denot _ ?t = _ => let t' := eval vm_compute in t in change t with t' end.
  rewrite fsw_SOff0, EX by lia. rewrite (ew_Ereg_nat (ms_regs ms) _ 10 10%bv eq_refl). exact R10. }
apply (fsw_retU B fsw_wr_tbl fsw_wr_tbl_ok Wc _ _ ms0 _ STK_preset_base64_encode (spZ regs0) FS_PSTAT_FP
  regs0 ly0 St0 U0 W0 mem0 md0 lyc Sc (U0 ++ [(q - HEAD, HEAD)]) EV_preset_base64_encode encR_Q HS).
- reflexivity.
- vm_compute. reflexivity.
- rewrite R1F. exact HRA0.
- exact HJ.
- exact HARU.
- (* the callee-saved registers *)
  apply (fsw_preserved _ _ _ ms0 regs0 encR_expect HS ltac:(vm_compute; reflexivity)).
  intros r Hr. cbv [CALLEE_SAVED In] in Hr.
  repeat (destruct Hr as [<-|Hr]); [..|destruct Hr];
  lazymatch goal with |- sv_denot _ (encR_expect ?z) = _ =>
    let e := eval vm_compute in (encR_expect z) in change (encR_expect z) with e end;
  first
  [ solve [apply bv_eq; rewrite denot_SOff; rewrite EX by lia; rewrite E2; unfold spZ;
           replace (bv_unsigned (getr regs0 2) - 32 + 32) with (bv_unsigned (getr regs0 2)) by lia;
           apply zcanon_id; unfold M64; apply u64_range]
  | solve [rewrite fsw_SOff0, EX by lia; change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity]
  | solve [rewrite fsw_SOff0, EX by lia; change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity]
  | solve [rewrite fsw_SOff0, EX by lia; change 35%nat with (32 + 3)%nat; rewrite ew_Ereg_extra; reflexivity]
  | solve [rewrite fsw_SOff0, EX by lia;
           lazymatch goal with |- ew _ ?n = getr _ ?r =>
             rewrite (ew_Ereg_nat (ms_regs ms) _ n r eq_refl);
             let z := eval vm_compute in (bv_unsigned r) in
             exact (Rk z ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) end] ].
- (* the post *)
  intros mat2. unfold encR_Q.
  pose proof encR_size_pos as HM2.
  split; [exact Ra0|]. split; [unfold HEAD in *; lia|]. split; [exact HAB|].
  split.
  { destruct HRBc as (Hin & H16 & Hpos & Hhd). split; [exact Hin|]. split; [exact H16|].
    split; [exact Hpos|].
    apply (VK (q - HEAD) 8%nat); first
      [ solve [unfold HEAD in *; lia]
      | solve [intros i Hi; unfold encR_out, HEAD in *; cbn [Z.of_nat] in *; lia]
      | solve [intros i Hi; unfold HEAD in *; cbn [Z.of_nat] in *; lia]
      | solve [exact Hhd] ]. }
  split.
  { (* the output bytes and the terminating 0 *)
    intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
    pose proof (b64_enc_len bs) as HBL. rewrite HBSL in HBL.
    destruct (Nat.lt_ge_cases j (length (WriterSpec.b64_enc bs))) as [Hlt|Hge].
    - rewrite app_nth1 by exact Hlt.
      destruct (HPRE j Hlt) as (HV & HB256). split; [|exact HB256].
      intros k Hk. rewrite (KEEP (q + Z.of_nat j + Z.of_nat k) ltac:(lia) ltac:(lia) ltac:(lia)).
      exact (HV k Hk).
    - assert (Hje : j = length (WriterSpec.b64_enc bs)) by lia.
      subst j. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
      split; [|lia].
      replace (q + Z.of_nat (length (WriterSpec.b64_enc bs))) with (q + enc_size len - 1)
        by (unfold enc_size; lia).
      exact VNUL. }
  split.
  { intros i Hi.
    rewrite (KEEP (data + i) ltac:(lia)
      ltac:(intros Hc; apply (encR_in_out ltac:(lia) (data + i) ltac:(lia)); unfold encR_out; lia)
      ltac:(lia)).
    rewrite (encR_mb (ms_mem ms) (data + i) HA ltac:(apply encR_in_out; lia) ltac:(lia)).
    exact (HKEEPc i Hi). }
  { destruct HGLOBc as (G1 & G2 & G3 & G4 & Hr).
    unfold fs_glob, fs_glob_at, G_LIVE, G_PEAK, G_COUNT, G_FAIL in *.
    assert (VG : forall a v, 65536 <= a -> a + 8 <= 6279168 ->
      val_mem tfibsegs (mrestrict (w_H Wc) memc) a 8 v ->
      val_mem tfibsegs (mrestrict (w_H Wc) (ms_mem ms0)) a 8 v).
    { intros a v Hlo Hhi HV. apply (VK a 8%nat); first
        [ solve [lia] | solve [cbn [Z.of_nat]; lia]
        | solve [intros i Hi; apply encR_img_not_out; apply enc_img_rng; cbn [Z.of_nat] in *; lia]
        | solve [intros i Hi; cbn [Z.of_nat] in *; lia]
        | solve [exact HV] ]. }
    split; [apply VG; [lia | lia | exact G1]|]. split; [apply VG; [lia | lia | exact G2]|].
    split; [apply VG; [lia | lia | exact G3]|]. split; [apply VG; [lia | lia | exact G4] | exact Hr]. }
Qed.

(* ---- the 3-byte loop (0x843fc .. 0x84534). At the head of round r: a1 = a7 = q + 4r (the four output bytes of
   this round), a2 = data + 3r + 2 (the third input byte), a4 = 3r + 2, a5 = g_b64, s0 = len, s1 = data, a0 = q.
   The three input bytes of the round are bs[3r], bs[3r+1], bs[3r+2]. ---- *)
Definition encR_extra3 (b0 b1 b2 : Z) : list word := [w64 0; w64 0; w64 0; w64 0; w64 b0; w64 b1; w64 b2].
Definition encR_kept (ms : machine_state) : Prop :=
  forall z, acallee_saved z -> z <> 2 -> z <> 8 -> z <> 9 -> z <> 18 ->
    getr (ms_regs ms) (Z_to_bv 5 z) = getr regs0 (Z_to_bv 5 z).
Definition encR_loop_regs (ms : machine_state) (r : Z) : Prop :=
  getr (ms_regs ms) 8 = w64 len /\ getr (ms_regs ms) 9 = w64 data /\ getr (ms_regs ms) 10 = w64 q /\
  getr (ms_regs ms) 11 = w64 (q + 4 * r) /\ getr (ms_regs ms) 12 = w64 (data + 3 * r + 2) /\
  getr (ms_regs ms) 14 = w64 (3 * r + 2) /\ getr (ms_regs ms) 15 = w64 G_B64 /\
  getr (ms_regs ms) 17 = w64 (q + 4 * r) /\ getr (ms_regs ms) 18 = w64 SHADOW_OFF /\
  spZ (ms_regs ms) = spZ regs0 - 32 /\ encR_kept ms.

(* the input block and the output block are two intervals that do not meet *)
Lemma encR_dj : 0 < len -> data + len <= q \/ q + enc_size len <= data.
Proof.
intros Hlen. pose proof encR_size_pos as HM.
destruct (Z_le_gt_dec (data + len) q) as [H1|H1]; [left; exact H1|].
destruct (Z_le_gt_dec (q + enc_size len) data) as [H2|H2]; [right; exact H2|].
exfalso. apply (encR_in_out Hlen (Z.max data q)); [lia|]. unfold encR_out. lia.
Qed.

(* g_b64 is image, the two blocks are not: the table meets neither window *)
Lemma encR_img_not_in : 0 < len -> forall a, in_img tfibsegs a -> ~ (data <= a < data + len).
Proof.
intros Hlen a Ha Hin. destruct (HDB Hlen) as (Hb & Hkd & Hkd0).
pose proof (ARU_AR tfibsegs B lyc Sc _ Wc memc mdc HARUc) as HAR.
assert (Hrq : req_size (kd + HEAD) = kd + HEAD)
  by (unfold req_size; destruct (kd + HEAD =? 0) eqn:E;
      [apply Z.eqb_eq in E; unfold HEAD in *; lia | reflexivity]).
apply (enc_blk_not_img lyc Sc Wc (unpoison (U0 ++ [(q - HEAD, HEAD)]) memc) mdc (data - HEAD) (kd + HEAD) a HAR
  ltac:(rewrite HAB; apply in_or_app; left; exact Hb) ltac:(rewrite Hrq; unfold HEAD in *; lia)).
exact Ha.
Qed.

Lemma encR_dj_in_tab : 0 < len -> data + len <= G_B64 \/ G_B64 + 65 <= data.
Proof.
intros Hlen.
destruct (Z_le_gt_dec (data + len) G_B64) as [H1|H1]; [left; exact H1|].
destruct (Z_le_gt_dec (G_B64 + 65) data) as [H2|H2]; [right; exact H2|].
exfalso. apply (encR_img_not_in Hlen (Z.max data G_B64)); [|lia].
apply enc_img_rng. unfold G_B64 in *. lia.
Qed.

Lemma encR_dj_out_tab : q + enc_size len <= G_B64 \/ G_B64 + 65 <= q.
Proof.
pose proof encR_size_pos as HM.
destruct (Z_le_gt_dec (q + enc_size len) G_B64) as [H1|H1]; [left; exact H1|].
destruct (Z_le_gt_dec (G_B64 + 65) q) as [H2|H2]; [right; exact H2|].
exfalso. apply (encR_img_not_out (Z.max q G_B64)); [|unfold encR_out; lia].
apply enc_img_rng. unfold G_B64 in *. lia.
Qed.

(* the round's three input bytes, read at any invariant memory *)
Lemma encR_in_byte : forall mem (j : nat), encR_agree mem -> (j < length bs)%nat ->
  val_mem tfibsegs (mrestrict (w_H Wc) mem) (data + Z.of_nat j) 1 (nth j bs 0) /\ 0 <= nth j bs 0 < 256.
Proof.
intros mem j HA Hj. pose proof alloc_ceiling_val as (CR & _).
destruct (HDATc j Hj) as (HV & HB). split; [|exact HB].
apply (encR_val mem (data + Z.of_nat j) 1%nat _ HA ltac:(lia) ltac:(cbn [Z.of_nat]; lia));
  [|exact HV].
intros i Hi. apply (encR_in_out ltac:(lia)). cbn [Z.of_nat] in *. lia.
Qed.

Lemma encR_round_state : forall ms md r b0 b1 b2,
  0 <= r -> 3 * r + 3 <= len ->
  encR_inv (ms_mem ms) md -> encR_loop_regs ms r ->
  nth (Z.to_nat (3 * r)) bs 0 = b0 -> nth (Z.to_nat (3 * r + 1)) bs 0 = b1 ->
  nth (Z.to_nat (3 * r + 2)) bs 0 = b2 ->
  st_ok tfibsegs (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) (enc_round_ss 0x843fc)
    (restrict (w_H Wc) (mkst (ms_regs ms) (w64 0x843fc) (ms_mem ms) (seg_rom tfibsegs)))
  /\ 0 <= b0 < 256 /\ 0 <= b1 < 256 /\ 0 <= b2 < 256.
Proof.
intros ms md r b0 b1 b2 Hr Hr3 (HJ & HARU & HA) HR N0 N1 N2.
pose proof encR_size_pos as HM. pose proof alloc_ceiling_val as (CR & _).
pose proof encR_out_facts as (HAPq & HQceil & HQimg).
pose proof HR as (R8 & R9 & R10 & R11 & R12 & R14 & R15 & R17 & R18 & Rsp & Rk).
assert (HBL : Z.of_nat (length bs) = len) by exact HBSL.
destruct (encR_in_byte (ms_mem ms) (Z.to_nat (3 * r)) HA ltac:(lia)) as (V0 & B0).
destruct (encR_in_byte (ms_mem ms) (Z.to_nat (3 * r + 1)) HA ltac:(lia)) as (V1 & B1).
destruct (encR_in_byte (ms_mem ms) (Z.to_nat (3 * r + 2)) HA ltac:(lia)) as (V2 & B2).
rewrite N0 in V0, B0. rewrite N1 in V1, B1. rewrite N2 in V2, B2.
assert (Hd0 : data + Z.of_nat (Z.to_nat (3 * r)) = data + 3 * r + 2 - 2) by lia.
assert (Hd1 : data + Z.of_nat (Z.to_nat (3 * r + 1)) = data + 3 * r + 2 - 1) by lia.
assert (Hd2 : data + Z.of_nat (Z.to_nat (3 * r + 2)) = data + 3 * r + 2) by lia.
rewrite Hd0 in V0. rewrite Hd1 in V1. rewrite Hd2 in V2.
split; [|split; [exact B0 | split; [exact B1 | exact B2]]].
apply (enc_round_state Wc (ms_mem ms) (ms_regs ms) (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2))
  (q + 4 * r) b0 b1 b2 (data + 3 * r + 2) len (3 * r + 2) 0x843fc).
- apply regs_ok_Ereg.
- change 36%nat with (32 + 4)%nat. rewrite ew_Ereg_extra. reflexivity.
- change 37%nat with (32 + 5)%nat. rewrite ew_Ereg_extra. reflexivity.
- change 38%nat with (32 + 6)%nat. rewrite ew_Ereg_extra. reflexivity.
- exact R8.
- exact R11.
- exact R12.
- exact R14.
- exact R15.
- exact R17.
- exact R18.
- exact V0.
- exact V1.
- exact V2.
- intros o Ho. replace (q + 4 * r + o) with (q + (4 * r + o)) by lia.
  apply (encR_wr_out (ms_mem ms) md HARU). unfold enc_size in *. lia.
- exact B0.
- exact B1.
- exact B2.
- lia.
- unfold PTOP. lia.
- unfold HEAD in *. lia.
- unfold PTOP, enc_size in *. lia.
- lia.
- lia.
- destruct (encR_dj ltac:(lia)) as [H|H]; [left | right]; unfold enc_size in *; lia.
Qed.

(* a table seat is apart from the round's two windows *)
Lemma encR_seat_dj : forall (E : env) (n : nat) (av r : Z) (cs : list YP09.chunk),
  bv_unsigned (ew E n) = av -> bv_unsigned (ew E 12) = data + 3 * r + 2 ->
  bv_unsigned (ew E 17) = q + 4 * r -> G_B64 <= av < G_B64 + 64 -> 0 <= r -> 3 * r + 3 <= len ->
  all_disjoint E (YP09.mkRegion (Some n) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff (S n) 0))])
    [enc_rin; YP09.mkRegion (Some 17%nat) 0 4 0 4 cs].
Proof.
intros E n av r cs Hn H12 H17 Hav Hr Hr3.
pose proof encR_size_pos as HM.
apply all_disjoint_of_extents. unfold enc_rin, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Hn, H12, H17.
cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
destruct (encR_dj_in_tab ltac:(lia)) as [D1|D1]; destruct encR_dj_out_tab as [D2|D2];
  repeat match goal with |- _ /\ _ => split end; try exact I; unfold G_B64, enc_size in *; lia.
Qed.


Lemma encR_U_of_bv : forall (E : env) n v, bv_unsigned (ew E n) = v -> 0 <= v < 2 ^ 64 ->
  U E (SOff n 0) = v.
Proof.
intros E n v H Hv. apply U_atom; [|exact Hv].
apply bv_eq. rewrite H. symmetry. apply unsigned_lit_small. exact Hv.
Qed.

(* every byte a round's run may write is an output byte: the only region with a write window is the output
   quad, based on atom 17 *)
Lemma encR_wr_bound : forall (E : env) (rs : list YP09.region) a r,
  Forall (fun rg => YP09.r_whi rg <= YP09.r_wlo rg \/
            (YP09.r_base rg = Some 17%nat /\ YP09.r_wlo rg = 0 /\ YP09.r_whi rg = 4)) rs ->
  bv_unsigned (ew E 17) = q + 4 * r -> 0 <= r -> 3 * r + 3 <= len ->
  in_wrange E rs a -> encR_out a.
Proof.
intros E rs a r HF H17 Hr Hr3 (rg & Hin & Hrg).
pose proof encR_size_pos as HM.
destruct (proj1 (Forall_forall _ _) HF rg Hin) as [Hro | (Hb & Hl & Hh)]; [lia|].
rewrite Hb, Hl, Hh in Hrg. cbn [base_val] in Hrg. rewrite H17 in Hrg.
unfold encR_out, enc_size in *. lia.
Qed.
(* one table seat: the register holds g_b64 + v, the byte there is the table's, and the one-byte region is
   apart from the round's two windows *)
Lemma encR_seat_ok : forall (msX : machine_state) (E : env) ss (rg : bv 5) (n : nat) v r mdx cs,
  encR_agree (ms_mem msX) -> ARU tfibsegs B lyc Sc (U0 ++ [(q - HEAD, HEAD)]) Wc (ms_mem msX) mdx ->
  0 <= r -> 3 * r + 3 <= len -> 0 <= v < 64 ->
  st_ok tfibsegs E ss (restrict (w_H Wc) msX) -> ss_atoms_lt n ss = true -> rg <> 0%bv -> (17 < n)%nat ->
  getr (ms_regs msX) rg = w64 (G_B64 + v) ->
  bv_unsigned (ew E 12) = data + 3 * r + 2 -> bv_unsigned (ew E 17) = q + 4 * r ->
  ss_mem ss = [enc_rin; YP09.mkRegion (Some 17%nat) 0 4 0 4 cs] ->
  st_ok tfibsegs (ewset (ewset E n (w64 (G_B64 + v))) (S n) (w64 (WriterSpec.b64c v)))
    (enc_seat ss rg n G_B64 (G_B64 + 63)) (restrict (w_H Wc) msX).
Proof.
intros msX E ss rg n v r mdx cs HA HARU Hr Hr3 Hv HS Hat Hrg Hn17 Hreg H12 H17 Hmem.
pose proof (b64c_range v Hv) as HB.
apply (enc_seat_ro1 E ss (restrict (w_H Wc) msX) rg n (G_B64 + v) (WriterSpec.b64c v) G_B64 (G_B64 + 63)
  HS Hat Hrg).
- cbn [ms_regs restrict]. exact Hreg.
- unfold G_B64. lia.
- lia.
- unfold G_B64. lia.
- exact HB.
- cbn [ms_mem restrict].
  exact (encR_tab_keep (ms_mem msX) HA HTABc v Hv).
- rewrite Hmem.
  apply (encR_seat_dj _ n (G_B64 + v) r cs).
  + rewrite ew_ewset_other by lia. rewrite ew_ewset_same. apply unsigned_lit_small. unfold G_B64. lia.
  + rewrite !ew_ewset_other by lia. exact H12.
  + rewrite !ew_ewset_other by lia. exact H17.
  + unfold G_B64. lia.
  + lia.
  + lia.
Qed.

(* the round's registers at the loop head, as the walk's env reads them *)
Lemma encR_round_env : forall ms r b0 b1 b2, encR_loop_regs ms r ->
  ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) 11 = w64 (q + 4 * r) /\
  ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) 12 = w64 (data + 3 * r + 2) /\
  ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) 15 = w64 G_B64 /\
  ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) 17 = w64 (q + 4 * r) /\
  ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) 18 = w64 SHADOW_OFF.
Proof.
intros ms r b0 b1 b2 (R8 & R9 & R10 & R11 & R12 & R14 & R15 & R17 & R18 & Rsp & Rk).
split; [rewrite (ew_Ereg_nat (ms_regs ms) _ 11 11%bv eq_refl); exact R11|].
split; [rewrite (ew_Ereg_nat (ms_regs ms) _ 12 12%bv eq_refl); exact R12|].
split; [rewrite (ew_Ereg_nat (ms_regs ms) _ 15 15%bv eq_refl); exact R15|].
split; [rewrite (ew_Ereg_nat (ms_regs ms) _ 17 17%bv eq_refl); exact R17|].
rewrite (ew_Ereg_nat (ms_regs ms) _ 18 18%bv eq_refl); exact R18.
Qed.

Lemma encR_in_apart : 0 < len -> enc_apart data (data + len).
Proof.
intros Hlen x Hx. destruct (HDB Hlen) as (Hb & Hkd & Hkd0).
pose proof (ARU_AR tfibsegs B lyc Sc _ Wc memc mdc HARUc) as HAR.
assert (Hrq : req_size (kd + HEAD) = kd + HEAD)
  by (unfold req_size; destruct (kd + HEAD =? 0) eqn:E;
      [apply Z.eqb_eq in E; unfold HEAD in *; lia | reflexivity]).
destruct (enc_blk_bounds lyc Sc Wc (unpoison (U0 ++ [(q - HEAD, HEAD)]) memc) mdc (data - HEAD) (kd + HEAD) x HAR
  ltac:(rewrite HAB; apply in_or_app; left; exact Hb) ltac:(rewrite Hrq; unfold HEAD in *; lia)) as (_ & _ & A3).
exact A3.
Qed.

(* a table seat's shent, at any invariant memory *)
Lemma encR_shent_seat : forall mem (E : env) (n : nat) v, encR_agree mem ->
  U E enc_Bx = SHADOW_OFF -> U E (SOff n 0) = G_B64 + v -> 0 <= v < 64 ->
  shent_ok tfibsegs enc_Bx E (mrestrict (w_H Wc) mem) (mkSHE n 0 1).
Proof.
intros mem E n v HA HB Hn Hv.
apply (enc_she Wc mem E n (G_B64 + v) 0 1 G_B64 65 HB Hn); [|lia | lia | lia|].
- apply (encR_ra_keep mem G_B64 65 HA); [unfold G_B64; lia | unfold G_B64; lia | exact HRATc].
- intros x Hx. unfold G_B64, SHADOW_OFF in *. lia.
Qed.

(* the round's shent list, at any invariant memory and any env that reads the round's registers *)
Lemma encR_sh0 : forall mem (mdx : Model) (E : env) r, encR_agree mem -> 0 <= r -> 3 * r + 3 <= len ->
  ARU tfibsegs B lyc Sc (U0 ++ [(q - HEAD, HEAD)]) Wc mem mdx ->
  U E enc_Bx = SHADOW_OFF -> U E (SOff 12 0) = data + 3 * r + 2 -> U E (SOff 17 0) = q + 4 * r ->
  U E (SOff 11 0) = q + 4 * r ->
  sh_ok tfibsegs enc_Bx enc_SH E (mrestrict (w_H Wc) mem).
Proof.
intros mem mdx E r HA Hr Hr3 HARU HB H12 H17 H11. pose proof encR_size_pos as HM.
apply (enc_sh_ok Wc mem E (data + 3 * r + 2) (q + 4 * r) HB H12 H17 H11).
- intros x Hx. apply (encR_ra_in mem mdx HARU ltac:(lia)). lia.
- intros x Hx. apply (encR_ra_out mem mdx HARU). unfold enc_size in *. lia.
- intros x Hx. apply (encR_in_apart ltac:(lia)). lia.
- intros x Hx. apply (proj1 encR_out_facts). unfold enc_size in *. lia.
Qed.

(* the three bytes a round consumes, as a prefix step *)
Lemma enc_firstn3 : forall (l : list Z) (n : nat), (n + 3 <= length l)%nat ->
  firstn (n + 3) l = firstn n l ++ [nth n l 0; nth (S n) l 0; nth (S (S n)) l 0].
Proof.
intros l n. revert l. induction n as [|n IH]; intros l Hl.
- destruct l as [|a [|b [|c t]]]; cbn [length] in Hl; try lia.
  cbn [firstn nth app]. reflexivity.
- destruct l as [|a t]; cbn [length] in Hl; [lia|].
  replace (S n + 3)%nat with (S (n + 3)) by lia.
  cbn [firstn]. rewrite (IH t ltac:(lia)). cbn [nth app]. reflexivity.
Qed.


(* the round's shent list at a state whose env reads the round's registers (A11 / A12 / A17 / A18 in context) *)
Ltac enc_shbase memx HAx rr HrA HrB HARUx A11x A12x A17x A18x :=
  apply (encR_sh0 memx _ _ rr HAx HrA HrB HARUx); apply encR_U_of_bv;
  first [ solve [repeat (rewrite ew_ewset_other by lia); rewrite A18x; apply unsigned_lit_small;
                 unfold SHADOW_OFF; lia]
        | solve [repeat (rewrite ew_ewset_other by lia); rewrite A12x; apply unsigned_lit_small; lia]
        | solve [repeat (rewrite ew_ewset_other by lia); rewrite A17x; apply unsigned_lit_small;
                 unfold enc_size in *; lia]
        | solve [repeat (rewrite ew_ewset_other by lia); rewrite A11x; apply unsigned_lit_small;
                 unfold enc_size in *; lia]
        | solve [unfold SHADOW_OFF; lia] | solve [unfold enc_size in *; lia] | solve [lia] ].
Ltac enc_shseat memx HAx n idx A18x :=
  apply (encR_shent_seat memx _ n idx HAx);
  first [ solve [apply encR_U_of_bv; [repeat (rewrite ew_ewset_other by lia); rewrite A18x;
                   apply unsigned_lit_small; unfold SHADOW_OFF; lia | unfold SHADOW_OFF; lia]]
        | solve [apply encR_U_of_bv; [repeat (rewrite ew_ewset_other by lia); rewrite ew_ewset_same;
                   apply unsigned_lit_small; unfold G_B64; lia | unfold G_B64; lia]]
        | solve [lia] ].

(* the registers at the loop's exit (0x845dc), after R = r + 1 rounds *)
Definition encR_exit_regs (ms : machine_state) (R : Z) : Prop :=
  getr (ms_regs ms) 8 = w64 len /\ getr (ms_regs ms) 9 = w64 data /\ getr (ms_regs ms) 10 = w64 q /\
  getr (ms_regs ms) 11 = w64 (q + 4 * R) /\ getr (ms_regs ms) 14 = w64 (3 * R) /\
  getr (ms_regs ms) 18 = w64 SHADOW_OFF /\ spZ (ms_regs ms) = spZ regs0 - 32 /\ encR_kept ms.

(* the model step of one round, and the two list facts the walk needs of it *)
Lemma encR_prefix_step : forall r b0 b1 b2, 0 <= r -> 3 * r + 3 <= len ->
  nth (Z.to_nat (3 * r)) bs 0 = b0 -> nth (Z.to_nat (3 * r + 1)) bs 0 = b1 ->
  nth (Z.to_nat (3 * r + 2)) bs 0 = b2 ->
  WriterSpec.b64_enc (firstn (Z.to_nat (3 * (r + 1))) bs)
  = WriterSpec.b64_enc (firstn (Z.to_nat (3 * r)) bs)
    ++ [WriterSpec.b64c (b0 / 4); WriterSpec.b64c ((b0 mod 4) * 16 + b1 / 16);
        WriterSpec.b64c ((b1 mod 16) * 4 + b2 / 64); WriterSpec.b64c (b2 mod 64)]
  /\ Z.of_nat (length (WriterSpec.b64_enc (firstn (Z.to_nat (3 * r)) bs))) = 4 * r.
Proof.
intros r b0 b1 b2 Hr Hr3 N0 N1 N2.
assert (HLP : length (firstn (Z.to_nat (3 * r)) bs) = (3 * Z.to_nat r)%nat)
  by (rewrite length_firstn; lia).
split; [|rewrite b64_enc_len, HLP; lia].
assert (HFI : firstn (Z.to_nat (3 * (r + 1))) bs = firstn (Z.to_nat (3 * r)) bs ++ [b0; b1; b2]).
{ replace (Z.to_nat (3 * (r + 1))) with (Z.to_nat (3 * r) + 3)%nat by lia.
  rewrite (enc_firstn3 bs (Z.to_nat (3 * r)) ltac:(lia)).
  rewrite N0. replace (S (Z.to_nat (3 * r))) with (Z.to_nat (3 * r + 1)) by lia.
  rewrite N1. replace (S (Z.to_nat (3 * r + 1))) with (Z.to_nat (3 * r + 2)) by lia.
  rewrite N2. reflexivity. }
rewrite HFI, (b64_enc_app (Z.to_nat r) _ _ HLP), (b64_enc_3 b0 b1 b2 []).
cbn [WriterSpec.b64_enc]. rewrite app_nil_r. reflexivity.
Qed.

(* four bytes appended to a byte array *)
Lemma encR_garr8_app4 : forall (m : word -> option byte) (pre : list Z) (c0 c1 c2 c3 base off : Z),
  garr8 tfibsegs m base pre -> Z.of_nat (length pre) = off -> 0 <= base -> base + off + 4 <= 2 ^ 64 ->
  val_mem tfibsegs m (base + off + 0) 1 c0 -> val_mem tfibsegs m (base + off + 1) 1 c1 ->
  val_mem tfibsegs m (base + off + 2) 1 c2 -> val_mem tfibsegs m (base + off + 3) 1 c3 ->
  0 <= c0 < 256 -> 0 <= c1 < 256 -> 0 <= c2 < 256 -> 0 <= c3 < 256 ->
  garr8 tfibsegs m base (pre ++ [c0; c1; c2; c3]).
Proof.
intros m pre c0 c1 c2 c3 base off HP Hoff Hb Hb4 V0 V1 V2 V3 R0 R1 R2 R3 j Hj.
rewrite length_app in Hj. cbn [length] in Hj.
destruct (Nat.lt_ge_cases j (length pre)) as [Hlt|Hge].
- rewrite app_nth1 by exact Hlt. exact (HP j Hlt).
- rewrite app_nth2 by exact Hge.
  destruct (j - length pre)%nat as [|[|[|[|k]]]] eqn:Ek; [| | | | lia]; cbn [nth];
    (split; [|lia]);
    [ replace (base + Z.of_nat j) with (base + off + 0) by lia; exact V0
    | replace (base + Z.of_nat j) with (base + off + 1) by lia; exact V1
    | replace (base + Z.of_nat j) with (base + off + 2) by lia; exact V2
    | replace (base + Z.of_nat j) with (base + off + 3) by lia; exact V3 ].
Qed.

(* a byte array survives a keep *)
Lemma encR_garr8_keep : forall (m m' : word -> option byte) (base : Z) (l : list Z) (X : Z -> Prop),
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> mbyte tfibsegs m' a = mbyte tfibsegs m a) ->
  0 <= base -> base + Z.of_nat (length l) <= 2 ^ 64 ->
  (forall i, base <= i < base + Z.of_nat (length l) -> ~ X i) ->
  garr8 tfibsegs m base l -> garr8 tfibsegs m' base l.
Proof.
intros m m' base l X HK Hb Hbl HX HP j Hj. destruct (HP j Hj) as (HV & HB). split; [|exact HB].
intros k Hk. rewrite (HK (base + Z.of_nat j + Z.of_nat k) ltac:(lia) ltac:(apply HX; lia)).
exact (HV k Hk).
Qed.
(* a callee-saved register the round never touched *)
Lemma encR_kept_reg : forall (E : env) ss msx (regsX : bvmap 5 word) (rr : bv 5),
  st_ok tfibsegs E ss (restrict (w_H Wc) msx) ->
  sr_get (ss_regs ss) rr = SOff (Z.to_nat (bv_unsigned rr)) 0 ->
  ew E (Z.to_nat (bv_unsigned rr)) = getr regsX rr ->
  getr (ms_regs msx) rr = getr regsX rr.
Proof.
intros E ss msx regsX rr HS Hsr Hew.
rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) E ss msx rr HS), Hsr, fsw_SOff0. exact Hew.
Qed.


(* ==== BEGIN the tail block (a Theorem Labs lane) ==== *)
(* ---- the TAIL, 0x845e0 .. 0x846fc: the one or two leftover bytes, their two or three table seats, the '='
   padding and the stores, ending by applying encR_nul at 0x84700.

   Route (MEASURED, capstone over the pinned fs.asan 64b53ff8...):
     0x845e0  add a2, s1, a4        a2 := data + 3R          (the leftover byte's address)
     0x845e4..0x845f0              its shadow check          (row 0x845f0)
     0x845f4  lbu a3, 0(a2)         bA := bs[3R]
     0x845f8  addi a4, a4, 1        a4 := 3R + 1
     0x845fc  bgeu a4, s0, 0x24     ONE leftover byte -> 0x84620 (a5 := 0); TWO -> 0x84600
     0x84600  add s1, s1, a4        s1 := data + 3R + 1      (the second byte's address)
     0x84604..0x84610              its shadow check          (row 0x84610)
     0x84614  lbu a5, 0(s1); slli a5, a5, 8
     0x84624..0x84634              a7 := (bA << 16) >> 18, a2 := g_b64 + a7      (the first index)
     0x84638..0x84644              the seat's shadow check   (row 0x84644)
     0x84648..0x84658              the output byte 0's check (row 0x84658)
     0x8465c..0x84660              a3 := a5 | (bA << 16); sb a2, 0(a1)           (letter 0)
     0x84664..0x8466c              a2 := g_b64 + ((a3 << 46) >> 58)              (the second index)
     0x84670..0x8467c              the seat's shadow check   (row 0x8467c)
     0x84680..0x84694              the output byte 1's check (row 0x84694)
     0x84698  sb a2, 0(a3)          letter 1
     0x8469c  bgeu a4, s0, 0x28     ONE leftover -> 0x846c4 (a3 := '='); TWO -> 0x846a0
     0x846a0..0x846ac              a2 := g_b64 + ((a5 >> 6) & 0x3c)              (the third index)
     0x846b0..0x846b8              the seat's shadow check   (row 0x846b8)
     0x846bc  lbu a3, 0(a2)         letter 2
     0x846c4  addi a3, zero, 0x3d   '=' (the one-byte arm)
     0x846c8..0x846d8              the output byte 2's check (row 0x846d8)
     0x846dc..0x846e0              sb a3, 2(a1)                                  (letter 2 or '=')
     0x846e4..0x846f0              the output byte 3's check (row 0x846f0)
     0x846f4..0x846fc              a1 := a1 + 4; sb '=', 0(a2)                   ('=' at offset 3)
   so the tail writes exactly [q + 4R, q + 4R + 4) and leaves a1 = q + 4R + 4 = q + 4 * ((len + 2) / 3).

   The nine deciding edges of report-sites-A.tsv rows 115-135 inside this range (0x845f0, 0x84610, 0x84644,
   0x84658, 0x8467c, 0x84694, 0x846b8, 0x846d8, 0x846f0) are refuted BY CONSTRUCTION: the three or four token
   runs below reach their stop pc with TS_running and an empty obligation list, so every inline shadow check
   falls through and no __asan_report_* edge is taken.

   How the engine is driven. The leftover byte's address is `add a2, s1, a4`, which the engine cannot name, so
   the state carries the ALIAS (SOff 9 0) + (SOff 14 0) = SOff 38 0 (atom 38 = data + 3R) and the input region
   sits at atom 38; `add s1, s1, a4` in the two-byte arm is then SOff 38 1 by the same alias. The leftover
   count is a CONDITION of the state (BC_GEU / BC_LTU on (SOff 14 1) and (SOff 8 0)), so the engine decides
   both bgeu's itself and no case split is left to the walk. The g_b64 reads keep the round's seat kit
   (enc_seat / enc_seat_ro1), one seat per table read, the previous seat dropped first (enc_drop_head). ---- *)

(* ---- the model: the last one or two bytes append the last four letters ---- *)
Lemma encT_skipn1 : forall (l : list Z) (n : nat), length l = (n + 1)%nat -> skipn n l = [nth n l 0].
Proof.
intros l n. revert l. induction n as [|n IH]; intros l Hl.
- destruct l as [|a [|b t]]; cbn [length] in Hl; try lia. reflexivity.
- destruct l as [|a t]; cbn [length] in Hl; [lia|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma encT_skipn2 : forall (l : list Z) (n : nat), length l = (n + 2)%nat ->
  skipn n l = [nth n l 0; nth (S n) l 0].
Proof.
intros l n. revert l. induction n as [|n IH]; intros l Hl.
- destruct l as [|a [|b [|c t]]]; cbn [length] in Hl; try lia. reflexivity.
- destruct l as [|a t]; cbn [length] in Hl; [lia|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma encT_model : forall R, 0 <= R -> 3 * R <= len ->
  WriterSpec.b64_enc bs
  = WriterSpec.b64_enc (firstn (Z.to_nat (3 * R)) bs) ++ WriterSpec.b64_enc (skipn (Z.to_nat (3 * R)) bs)
  /\ Z.of_nat (length (WriterSpec.b64_enc (firstn (Z.to_nat (3 * R)) bs))) = 4 * R.
Proof.
intros R HR HR3.
assert (HLP : length (firstn (Z.to_nat (3 * R)) bs) = (3 * Z.to_nat R)%nat)
  by (rewrite length_firstn; lia).
split; [|rewrite b64_enc_len, HLP; lia].
rewrite <- (b64_enc_app (Z.to_nat R) (firstn (Z.to_nat (3 * R)) bs) (skipn (Z.to_nat (3 * R)) bs) HLP).
rewrite firstn_skipn. reflexivity.
Qed.

Lemma encT_model1 : forall R b0, 0 <= R -> len = 3 * R + 1 -> nth (Z.to_nat (3 * R)) bs 0 = b0 ->
  WriterSpec.b64_enc bs
  = WriterSpec.b64_enc (firstn (Z.to_nat (3 * R)) bs)
    ++ [WriterSpec.b64c (b0 / 4); WriterSpec.b64c ((b0 mod 4) * 16); 61; 61]
  /\ Z.of_nat (length (WriterSpec.b64_enc (firstn (Z.to_nat (3 * R)) bs))) = 4 * R.
Proof.
intros R b0 HR Hlen N0.
destruct (encT_model R HR ltac:(lia)) as (HSp & HL). split; [|exact HL].
rewrite HSp, (encT_skipn1 bs (Z.to_nat (3 * R)) ltac:(lia)), N0. reflexivity.
Qed.

Lemma encT_model2 : forall R b0 b1, 0 <= R -> len = 3 * R + 2 ->
  nth (Z.to_nat (3 * R)) bs 0 = b0 -> nth (Z.to_nat (3 * R + 1)) bs 0 = b1 ->
  WriterSpec.b64_enc bs
  = WriterSpec.b64_enc (firstn (Z.to_nat (3 * R)) bs)
    ++ [WriterSpec.b64c (b0 / 4); WriterSpec.b64c ((b0 mod 4) * 16 + b1 / 16);
        WriterSpec.b64c ((b1 mod 16) * 4); 61]
  /\ Z.of_nat (length (WriterSpec.b64_enc (firstn (Z.to_nat (3 * R)) bs))) = 4 * R.
Proof.
intros R b0 b1 HR Hlen N0 N1.
destruct (encT_model R HR ltac:(lia)) as (HSp & HL). split; [|exact HL].
rewrite HSp, (encT_skipn2 bs (Z.to_nat (3 * R)) ltac:(lia)), N0.
replace (S (Z.to_nat (3 * R))) with (Z.to_nat (3 * R + 1)) by lia.
rewrite N1. reflexivity.
Qed.

(* R + 1 whole rounds fit in the output block whenever one leftover byte is left *)
Lemma encT_qR : forall R, 0 <= R -> 3 * R + 1 <= len -> R + 1 <= (len + 2) / 3.
Proof.
intros R HR HR3. apply (Z.le_trans _ ((3 * R + 3) / 3)).
- rewrite (Z.mul_comm 3 R), (Z.div_add_l R 3 3 ltac:(lia)).
  replace (3 / 3) with 1 by reflexivity. lia.
- apply Z.div_le_mono; lia.
Qed.

(* with one or two leftover bytes the quotient is exactly R + 1 *)
Lemma encT_qRe : forall R, 0 <= R -> 3 * R + 1 <= len -> len <= 3 * R + 2 -> (len + 2) / 3 = R + 1.
Proof.
intros R HR H1 H2.
assert (Hc : len = 3 * R + 1 \/ len = 3 * R + 2) by lia. destruct Hc as [He|He]; rewrite He.
- replace (3 * R + 1 + 2) with ((R + 1) * 3 + 0) by lia.
  rewrite (Z.div_add_l (R + 1) 3 0 ltac:(lia)). replace (0 / 3) with 0 by reflexivity. lia.
- replace (3 * R + 2 + 2) with ((R + 1) * 3 + 1) by lia.
  rewrite (Z.div_add_l (R + 1) 3 1 ltac:(lia)). replace (1 / 3) with 0 by reflexivity. lia.
Qed.

(* ---- the three index shapes the engine leaves, as the model's six-bit indices (blocks' enc_t0 / enc_t1_one) ---- *)
Lemma encT_U_addG : forall E (y : sv) v, U E y = v -> 0 <= v < 64 ->
  U E (SAlu ALU_ADD (SLit G_B64) y) = G_B64 + v.
Proof.
intros E y v Hy Hv. rewrite U_SAlu. cbn [zalu_raw].
rewrite Hy, U_SLit, (zcanon_id G_B64) by (unfold M64, G_B64; lia).
apply zcanon_id. unfold M64, G_B64. lia.
Qed.

(* 0x84624..0x8462c  slli a3,a3,0x10; srli a7,a3,0x12 *)
Lemma encT_U_i0 : forall E b0, ew E 36 = w64 b0 -> 0 <= b0 < 256 ->
  U E (SAlu ALU_SRL (SAlu ALU_SLL (SOff 36 0) (SLit 16)) (SLit 18)) = b0 / 4.
Proof.
intros E b0 H36 H0.
rewrite (enc_U_srl E _ 18 _ ltac:(lia)
  (enc_U_sll E (SOff 36 0) 16 b0 ltac:(lia) (U_atom E 36 b0 H36 ltac:(lia)))).
exact (enc_t0 b0 H0).
Qed.

(* 0x8465c..0x84668, one leftover byte: a5 = 0, so  or a3,a5,a3; slli a3,a3,0x2e; srli a2,a3,0x3a *)
Lemma encT_U_i1a : forall E b0, ew E 36 = w64 b0 -> 0 <= b0 < 256 ->
  U E (SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_OR (SLit 0) (SAlu ALU_SLL (SOff 36 0) (SLit 16))) (SLit 46))
       (SLit 58))
  = (b0 mod 4) * 16.
Proof.
intros E b0 H36 H0.
assert (AZ : U E (SLit 0) = 0) by (rewrite U_SLit; reflexivity).
assert (A0 : U E (SAlu ALU_SLL (SOff 36 0) (SLit 16)) = Z.shiftl b0 16 mod 2 ^ 64)
  by (apply (enc_U_sll E (SOff 36 0) 16 b0); [lia | apply (U_atom E 36 b0 H36); lia]).
assert (AO : U E (SAlu ALU_OR (SLit 0) (SAlu ALU_SLL (SOff 36 0) (SLit 16))) = b0 * 65536).
{ rewrite (enc_U_or E _ _ _ _ AZ A0). brute1 b0. }
rewrite (enc_U_srl E _ 58 _ ltac:(lia) (enc_U_sll E _ 46 _ ltac:(lia) AO)).
exact (enc_t1_one b0 H0).
Qed.

(* 0x846a0..0x846a4, two leftover bytes: the engine folds  slli a5,a5,8; srli a5,a5,6  into  slli 2 *)
Lemma encT_U_i2 : forall E b1, ew E 37 = w64 b1 -> 0 <= b1 < 256 ->
  U E (SAlu ALU_AND (SAlu ALU_SLL (SOff 37 0) (SLit 2)) (SLit 60)) = (b1 mod 16) * 4.
Proof.
intros E b1 H37 H1.
rewrite (U_and_lit E _ 60 ltac:(lia)),
        (enc_U_sll E (SOff 37 0) 2 b1 ltac:(lia) (U_atom E 37 b1 H37 ltac:(lia))).
brute1 b1.
Qed.

(* ---- the tail's symbolic states (atom 38 = data + 3R, 36 / 37 its bytes, 11 the output pointer q + 4R,
   18 the shadow base, 8 len, 14 the index 3R; 100/200/300 the table seats, 101/201/301 their bytes) ---- *)
Definition encT_rin1 : YP09.region :=
  YP09.mkRegion (Some 38%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 36 0))].
Definition encT_rin2 : YP09.region :=
  YP09.mkRegion (Some 38%nat) 0 2 0 0
    [YP09.mkChunk 0 (CVal 1 (SOff 36 0)); YP09.mkChunk 1 (CVal 1 (SOff 37 0))].
Definition encT_rout : YP09.region := YP09.mkRegion (Some 11%nat) 0 4 0 4 [].
Definition encT_gf : list (nat * afact) :=
  [(18%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (38%nat, mkAF 4096 PTOP 0); (11%nat, mkAF 4096 PTOP 0);
   (8%nat, mkAF 0 (2 ^ 27) 0); (14%nat, mkAF 0 (2 ^ 27) 0); (36%nat, mkAF 0 255 0); (37%nat, mkAF 0 255 0)].
Definition encT_al : list (sv * sv) := [(SAlu ALU_ADD (SOff 9 0) (SOff 14 0), SOff 38 0)].
Definition encT_ss1 : sstate :=
  mkSS 0x845e0 sr_atoms [encT_rin1; encT_rout] None
    (mkFacts encT_gf [mkAC BC_GEU (SOff 14 1) (SOff 8 0)] encT_al).
Definition encT_ss2 : sstate :=
  mkSS 0x845e0 sr_atoms [encT_rin2; encT_rout] None
    (mkFacts encT_gf [mkAC BC_LTU (SOff 14 1) (SOff 8 0)] encT_al).
Definition encT_SH1 : list shent := [mkSHE 38 0 1; mkSHE 11 0 4].
Definition encT_SH2 : list shent := [mkSHE 38 0 2; mkSHE 11 0 4].
Definition encT_run (ss : sstate) (SH : list shent) (stop : Z) : shst * trun_status :=
  sym_run_toN_tok tfibsegs fsw_wr_tbl (run_K 0 enc_Bx SH ss) enc_Bx fs_Bspan SH FUEL stop ss.
Definition encT_drop (ss : sstate) : sstate :=
  mkSS (ss_pc ss) (ss_regs ss) (tl (ss_mem ss)) (ss_resv ss) (ss_facts ss).

(* the one-leftover-byte walk: 0x845e0 -> 0x84638 -> 0x84670 -> 0x84700, two seats *)
Definition encT_A1 : shst := Eval vm_compute in fst (encT_run encT_ss1 encT_SH1 0x84638).
Definition encT_A1s : sstate :=
  Eval vm_compute in enc_seat (sh_ss encT_A1) 12%bv 100 G_B64 (G_B64 + 63).
Definition encT_SH1_100 : list shent := encT_SH1 ++ [mkSHE 100 0 1].
Definition encT_B1 : shst := Eval vm_compute in fst (encT_run encT_A1s encT_SH1_100 0x84670).
Definition encT_B1s : sstate :=
  Eval vm_compute in enc_seat (encT_drop (sh_ss encT_B1)) 12%bv 200 G_B64 (G_B64 + 63).
Definition encT_SH1_200 : list shent := encT_SH1 ++ [mkSHE 200 0 1].
Definition encT_C1 : shst := Eval vm_compute in fst (encT_run encT_B1s encT_SH1_200 0x84700).

(* the two-leftover-byte walk: 0x845e0 -> 0x84638 -> 0x84670 -> 0x846ac -> 0x84700, three seats *)
Definition encT_A2 : shst := Eval vm_compute in fst (encT_run encT_ss2 encT_SH2 0x84638).
Definition encT_A2s : sstate :=
  Eval vm_compute in enc_seat (sh_ss encT_A2) 12%bv 100 G_B64 (G_B64 + 63).
Definition encT_SH2_100 : list shent := encT_SH2 ++ [mkSHE 100 0 1].
Definition encT_B2 : shst := Eval vm_compute in fst (encT_run encT_A2s encT_SH2_100 0x84670).
Definition encT_B2s : sstate :=
  Eval vm_compute in enc_seat (encT_drop (sh_ss encT_B2)) 12%bv 200 G_B64 (G_B64 + 63).
Definition encT_SH2_200 : list shent := encT_SH2 ++ [mkSHE 200 0 1].
Definition encT_C2 : shst := Eval vm_compute in fst (encT_run encT_B2s encT_SH2_200 0x846ac).
Definition encT_C2s : sstate :=
  Eval vm_compute in enc_seat (encT_drop (sh_ss encT_C2)) 12%bv 300 G_B64 (G_B64 + 63).
Definition encT_SH2_300 : list shent := encT_SH2 ++ [mkSHE 300 0 1].
Definition encT_D2 : shst := Eval vm_compute in fst (encT_run encT_C2s encT_SH2_300 0x84700).

(* ---- every byte a tail run may write is one of this round's four output bytes: the only region with a write
   window is the output quad, based on atom 11 ---- *)
Definition encT_wshape (rg : YP09.region) : bool :=
  (YP09.r_whi rg <=? YP09.r_wlo rg)
  || (YP09.obase_eqb (YP09.r_base rg) (Some 11%nat) && (YP09.r_wlo rg =? 0) && (YP09.r_whi rg =? 4)).

Lemma encT_wr_win : forall (E : env) (rs : list YP09.region) a R,
  forallb encT_wshape rs = true -> bv_unsigned (ew E 11) = q + 4 * R ->
  in_wrange E rs a -> q + 4 * R <= a < q + 4 * R + 4.
Proof.
intros E rs a R HF H11 (rg & Hin & Hrg).
pose proof (proj1 (forallb_forall _ _) HF rg Hin) as Hw.
unfold encT_wshape in Hw. apply orb_prop in Hw as [Hro | Hb].
- apply Z.leb_le in Hro. lia.
- apply andb_prop in Hb as [Hb Hhi]. apply andb_prop in Hb as [Hbb Hlo].
  apply Z.eqb_eq in Hlo. apply Z.eqb_eq in Hhi.
  destruct (YP09.r_base rg) as [n|] eqn:Eb; [|cbn [YP09.obase_eqb] in Hbb; discriminate].
  cbn [YP09.obase_eqb] in Hbb. apply Nat.eqb_eq in Hbb. subst n.
  try rewrite Eb in Hrg. rewrite Hlo, Hhi in Hrg. cbn [base_val] in Hrg.
  rewrite H11 in Hrg. lia.
Qed.

Lemma encT_wr_bound : forall (E : env) (rs : list YP09.region) a R,
  forallb encT_wshape rs = true -> bv_unsigned (ew E 11) = q + 4 * R -> 0 <= R -> 3 * R + 1 <= len ->
  in_wrange E rs a -> encR_out a.
Proof.
intros E rs a R HF H11 HR HR3 Hin.
pose proof encR_size_pos as HM. pose proof (encT_qR R HR HR3) as HQ.
pose proof (encT_wr_win E rs a R HF H11 Hin) as Hw.
unfold encR_out, enc_size in *. lia.
Qed.

Lemma encT_awr : forall (E : env) (rs : list YP09.region) R,
  forallb encT_wshape rs = true -> bv_unsigned (ew E 11) = q + 4 * R -> 0 <= R -> 3 * R + 1 <= len ->
  awr_ok tfibsegs B E rs STK_preset_base64_encode (spZ regs0) FS_PSTAT_FP
    (ablocks B ly0 St0) (ablocks B lyc Sc) lyc [] (frames St0).
Proof.
intros E rs R HF H11 HR HR3 a Ha.
pose proof encR_size_pos as HM.
pose proof (encT_wr_bound E rs a R HF H11 HR HR3 Ha) as Hout.
unfold encR_out in Hout.
left. right. right. left.
exists (q - HEAD), (enc_size len + HEAD).
split; [exact HQB|]. split; [exact encR_new_block|].
unfold req_size. destruct (enc_size len + HEAD =? 0) eqn:EQ;
  [apply Z.eqb_eq in EQ; unfold HEAD in *; lia | unfold HEAD in *; lia].
Qed.

(* ---- the atoms every stage of the tail reads, as one fact that travels through the runs and the seats ---- *)
Definition encT_base (E : env) (msE : machine_state) (R b0 b1 : Z) : Prop :=
  ew E 2 = getr (ms_regs msE) 2 /\ ew E 8 = w64 len /\ ew E 9 = w64 data /\ ew E 10 = w64 q /\
  ew E 11 = w64 (q + 4 * R) /\ ew E 14 = w64 (3 * R) /\ ew E 18 = w64 SHADOW_OFF /\
  ew E 36 = w64 b0 /\ ew E 37 = w64 b1 /\ ew E 38 = w64 (data + 3 * R).

Lemma encT_base_agree : forall (E E' : env) msE R b0 b1 (k : nat), (39 <= k)%nat ->
  env_agree k E E' -> encT_base E msE R b0 b1 -> encT_base E' msE R b0 b1.
Proof.
intros E E' msE R b0 b1 k Hk (HA & _) HB. unfold encT_base in *.
destruct HB as (H2 & H8 & H9 & H10 & H11 & H14 & H18 & H36 & H37 & H38).
repeat split; rewrite HA by lia; assumption.
Qed.

Lemma encT_U_of_base : forall (E : env) msE R b0 b1,
  encT_base E msE R b0 b1 -> 0 <= R -> 3 * R + 1 <= len ->
  U E enc_Bx = SHADOW_OFF /\ U E (SOff 38 0) = data + 3 * R /\ U E (SOff 11 0) = q + 4 * R /\
  bv_unsigned (ew E 38) = data + 3 * R /\ bv_unsigned (ew E 11) = q + 4 * R.
Proof.
intros E msE R b0 b1 (A2 & A8 & A9 & A10 & A11 & A14 & A18 & A36 & A37 & A38) HR HR3.
pose proof encR_size_pos as HM. pose proof alloc_ceiling_val as (CR & _).
pose proof encR_out_facts as (_ & HQceil & _). pose proof (encT_qR R HR HR3) as HQ.
pose proof HDLO as HD1. pose proof HDHI as HD2.
assert (HQlo : 4112 <= q) by (unfold HEAD in *; lia).
split; [apply (U_atom E 18 SHADOW_OFF A18); unfold SHADOW_OFF; lia|].
split; [apply (U_atom E 38 _ A38); lia|].
split; [apply (U_atom E 11 _ A11); unfold enc_size in *; lia|].
split; [rewrite A38; apply unsigned_lit_small; lia|].
rewrite A11; apply unsigned_lit_small; unfold enc_size in *; lia.
Qed.

(* ---- ONE segment run of the tail: the state, its shadow entries and the invariant go in, the engine's
   token run (fsw_run_to_tok_AJU, no obligation, every write inside the output quad) carries them to the stop
   pc. Each of the seven runs of the two arms is exactly one application of this lemma. ---- *)
Lemma encT_seg : forall (E : env) (ss : sstate) (SH : list shent) (stop : Z) (st' : shst)
    (ms msE : machine_state) (md : Model) (R b0 b1 : Z) (Q : world tfibsegs -> config -> Prop),
  st_ok tfibsegs E ss (restrict (w_H Wc) ms) ->
  sh_ok tfibsegs enc_Bx SH E (mrestrict (w_H Wc) (ms_mem ms)) ->
  encR_inv (ms_mem ms) md ->
  encT_base E msE R b0 b1 ->
  sh_static_ok (run_K 0 enc_Bx SH ss) enc_Bx fs_Bspan SH (ss_facts ss) (ss_mem ss) = true ->
  encT_run ss SH stop = (st', TS_running) ->
  sh_obls st' = [] ->
  forallb encT_wshape (ss_mem ss) = true ->
  (39 <= run_K 0 enc_Bx SH ss)%nat ->
  0 <= R -> 3 * R + 1 <= len ->
  (forall (ws : list word) (ms' : machine_state) (md' : Model),
     length ws = sh_j st' ->
     st_ok tfibsegs (extK E (run_K 0 enc_Bx SH ss) ws) (sh_ss st') (restrict (w_H Wc) ms') ->
     encR_inv (ms_mem ms') md' ->
     encT_base (extK E (run_K 0 enc_Bx SH ss) ws) msE R b0 b1 ->
     env_agree (run_K 0 enc_Bx SH ss) E (extK E (run_K 0 enc_Bx SH ss) ws) ->
     frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
     frame_of E (ss_mem ss) (mrestrict (w_H Wc) (ms_mem ms)) (mrestrict (w_H Wc) (ms_mem ms')) ->
     SRr tfibsegs Wc (mkCfg ms' md') Q) ->
  SRr tfibsegs Wc (mkCfg ms md) Q.
Proof.
intros E ss SH stop st' ms msE md R b0 b1 Q HS SHOK HINV HB HST Hrun Hobl HW HK39 HR HR3 HK.
pose proof HINV as (HJ & HARU & HA). unfold encR_J in HJ.
destruct (encT_U_of_base E msE R b0 b1 HB HR HR3) as (_ & _ & _ & _ & E11).
eapply (@fsw_run_to_tok_AJU _ rc SK _ fsw_wr_tbl fsw_wr_tbl_ok Wc FUEL stop E
  (run_K 0 enc_Bx SH ss) enc_Bx fs_Bspan SH ss st' TS_running ms
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS SHOK HST Hrun I HARU HJ).
- rewrite Hobl. apply Forall_nil.
- exact (encT_awr E (ss_mem ss) R HW E11 HR HR3).
- intros ws ms' mat' Hlen HS' SHOK' HJ' HARU' HF HFr HG.
  pose proof (env_agree_extK E (run_K 0 enc_Bx SH ss) ws) as HAGx.
  apply (HK ws ms' _ Hlen HS').
  + unfold encR_inv. split; [exact HJ'|]. split; [exact HARU'|].
    intros x Hx.
    rewrite (enc_frame_X E (ss_mem ss) (ms_mem ms) (ms_mem ms') encR_out HF
      ltac:(intros z Hz; exact (encT_wr_bound E (ss_mem ss) z R HW E11 HR HR3 Hz)) x Hx).
    exact (HA x Hx).
  + exact (encT_base_agree E _ msE R b0 b1 (run_K 0 enc_Bx SH ss) HK39 HAGx HB).
  + exact HAGx.
  + exact HF.
  + exact HFr.
Qed.

(* ---- the state at 0x845e0, in the two arms ---- *)
Lemma encT_state1 : forall ms md R b0,
  0 <= R -> len = 3 * R + 1 -> encR_inv (ms_mem ms) md -> encR_exit_regs ms R ->
  nth (Z.to_nat (3 * R)) bs 0 = b0 ->
  st_ok tfibsegs (Ereg (ms_regs ms) (encR_extra3 b0 0 (data + 3 * R))) encT_ss1
    (restrict (w_H Wc) (mkst (ms_regs ms) (w64 0x845e0) (ms_mem ms) (seg_rom tfibsegs)))
  /\ 0 <= b0 < 256.
Proof.
intros ms md R b0 HR Hlen (HJ & HARU & HA) HX N0.
pose proof encR_size_pos as HM. pose proof alloc_ceiling_val as (CR & _).
pose proof encR_out_facts as (HAPq & HQceil & HQimg).
pose proof (encT_qR R HR ltac:(lia)) as HQ. pose proof HLN as HLN'.
pose proof HDLO as HD1. pose proof HDHI as HD2.
assert (HQlo : 4112 <= q) by (unfold HEAD in *; lia).
pose proof HX as (X8 & X9 & X10 & X11 & X14 & X18 & Xsp & Xk).
destruct (encR_in_byte (ms_mem ms) (Z.to_nat (3 * R)) HA ltac:(lia)) as (V0 & B0).
rewrite N0 in V0, B0.
replace (data + Z.of_nat (Z.to_nat (3 * R))) with (data + 3 * R) in V0 by lia.
split; [|exact B0].
assert (A8 : ew (Ereg (ms_regs ms) (encR_extra3 b0 0 (data + 3 * R))) 8 = w64 len)
  by (rewrite (ew_Ereg_nat (ms_regs ms) _ 8 8%bv eq_refl); exact X8).
assert (A9 : ew (Ereg (ms_regs ms) (encR_extra3 b0 0 (data + 3 * R))) 9 = w64 data)
  by (rewrite (ew_Ereg_nat (ms_regs ms) _ 9 9%bv eq_refl); exact X9).
assert (A11 : ew (Ereg (ms_regs ms) (encR_extra3 b0 0 (data + 3 * R))) 11 = w64 (q + 4 * R))
  by (rewrite (ew_Ereg_nat (ms_regs ms) _ 11 11%bv eq_refl); exact X11).
assert (A14 : ew (Ereg (ms_regs ms) (encR_extra3 b0 0 (data + 3 * R))) 14 = w64 (3 * R))
  by (rewrite (ew_Ereg_nat (ms_regs ms) _ 14 14%bv eq_refl); exact X14).
assert (A18 : ew (Ereg (ms_regs ms) (encR_extra3 b0 0 (data + 3 * R))) 18 = w64 SHADOW_OFF)
  by (rewrite (ew_Ereg_nat (ms_regs ms) _ 18 18%bv eq_refl); exact X18).
assert (A36 : ew (Ereg (ms_regs ms) (encR_extra3 b0 0 (data + 3 * R))) 36 = w64 b0)
  by (change 36%nat with (32 + 4)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (A37 : ew (Ereg (ms_regs ms) (encR_extra3 b0 0 (data + 3 * R))) 37 = w64 0)
  by (change 37%nat with (32 + 5)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (A38 : ew (Ereg (ms_regs ms) (encR_extra3 b0 0 (data + 3 * R))) 38 = w64 (data + 3 * R))
  by (change 38%nat with (32 + 6)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (U8 : bv_unsigned (ew (Ereg (ms_regs ms) (encR_extra3 b0 0 (data + 3 * R))) 8) = len)
  by (rewrite A8; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew (Ereg (ms_regs ms) (encR_extra3 b0 0 (data + 3 * R))) 11) = q + 4 * R)
  by (rewrite A11; apply unsigned_lit_small; unfold enc_size in *; lia).
assert (U14 : bv_unsigned (ew (Ereg (ms_regs ms) (encR_extra3 b0 0 (data + 3 * R))) 14) = 3 * R)
  by (rewrite A14; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew (Ereg (ms_regs ms) (encR_extra3 b0 0 (data + 3 * R))) 18) = SHADOW_OFF)
  by (rewrite A18; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U36 : bv_unsigned (ew (Ereg (ms_regs ms) (encR_extra3 b0 0 (data + 3 * R))) 36) = b0)
  by (rewrite A36; apply unsigned_lit_small; lia).
assert (U37 : bv_unsigned (ew (Ereg (ms_regs ms) (encR_extra3 b0 0 (data + 3 * R))) 37) = 0)
  by (rewrite A37; apply unsigned_lit_small; lia).
assert (U38 : bv_unsigned (ew (Ereg (ms_regs ms) (encR_extra3 b0 0 (data + 3 * R))) 38) = data + 3 * R)
  by (rewrite A38; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold encT_ss1. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- vm_compute; reflexivity.
- constructor; [|constructor; [|constructor]].
  + unfold encT_rin1, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U38. split; [lia|]. split; [unfold PTOP in *; lia|].
    split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val tfibsegs _ _ (data + 3 * R) 0 1%N (SOff 36 0) b0);
      [rewrite fsw_SOff0, A36; reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
      | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_r; exact V0].
  + unfold encT_rout, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U11. split; [lia|]. split; [unfold PTOP, enc_size in *; lia|].
    split; [|constructor]. intros o Ho. replace (q + 4 * R + o) with (q + (4 * R + o)) by lia.
    apply (encR_wr_out (ms_mem ms) md HARU). unfold enc_size in *. lia.
- apply pairwise_disjoint_of_extents. unfold encT_rin1, encT_rout, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U38, U11.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  destruct (encR_dj ltac:(lia)) as [D|D];
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold enc_size in *; lia.
- unfold encT_gf, encT_al, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split].
  + unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U18, U38, U11, U8, U14, U36, U37. rewrite !Z.pow_0_r.
    unfold PTOP, SHADOW_OFF, enc_size in *.
    repeat split; try lia; try (apply Z.mod_1_r).
  + split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
    rewrite branch_geu_U. apply negb_true_iff. apply Z.ltb_ge.
    rewrite (U_atom_off _ 14 (3 * R) 1 A14 ltac:(lia) ltac:(lia)),
            (U_atom _ 8 len A8 ltac:(lia)). lia.
  + split; [|exact I]. apply U_inj.
    rewrite (enc_U_add2 _ 9 14 0 0 data (3 * R) A9 A14 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
               ltac:(lia)).
    rewrite (U_atom _ 38 (data + 3 * R) A38 ltac:(lia)). lia.
Qed.

Lemma encT_state2 : forall ms md R b0 b1,
  0 <= R -> len = 3 * R + 2 -> encR_inv (ms_mem ms) md -> encR_exit_regs ms R ->
  nth (Z.to_nat (3 * R)) bs 0 = b0 -> nth (Z.to_nat (3 * R + 1)) bs 0 = b1 ->
  st_ok tfibsegs (Ereg (ms_regs ms) (encR_extra3 b0 b1 (data + 3 * R))) encT_ss2
    (restrict (w_H Wc) (mkst (ms_regs ms) (w64 0x845e0) (ms_mem ms) (seg_rom tfibsegs)))
  /\ 0 <= b0 < 256 /\ 0 <= b1 < 256.
Proof.
intros ms md R b0 b1 HR Hlen (HJ & HARU & HA) HX N0 N1.
pose proof encR_size_pos as HM. pose proof alloc_ceiling_val as (CR & _).
pose proof encR_out_facts as (HAPq & HQceil & HQimg).
pose proof (encT_qR R HR ltac:(lia)) as HQ. pose proof HLN as HLN'.
pose proof HDLO as HD1. pose proof HDHI as HD2.
assert (HQlo : 4112 <= q) by (unfold HEAD in *; lia).
pose proof HX as (X8 & X9 & X10 & X11 & X14 & X18 & Xsp & Xk).
destruct (encR_in_byte (ms_mem ms) (Z.to_nat (3 * R)) HA ltac:(lia)) as (V0 & B0).
destruct (encR_in_byte (ms_mem ms) (Z.to_nat (3 * R + 1)) HA ltac:(lia)) as (V1 & B1).
rewrite N0 in V0, B0. rewrite N1 in V1, B1.
replace (data + Z.of_nat (Z.to_nat (3 * R))) with (data + 3 * R) in V0 by lia.
replace (data + Z.of_nat (Z.to_nat (3 * R + 1))) with (data + 3 * R + 1) in V1 by lia.
split; [|split; [exact B0 | exact B1]].
assert (A8 : ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 (data + 3 * R))) 8 = w64 len)
  by (rewrite (ew_Ereg_nat (ms_regs ms) _ 8 8%bv eq_refl); exact X8).
assert (A9 : ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 (data + 3 * R))) 9 = w64 data)
  by (rewrite (ew_Ereg_nat (ms_regs ms) _ 9 9%bv eq_refl); exact X9).
assert (A11 : ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 (data + 3 * R))) 11 = w64 (q + 4 * R))
  by (rewrite (ew_Ereg_nat (ms_regs ms) _ 11 11%bv eq_refl); exact X11).
assert (A14 : ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 (data + 3 * R))) 14 = w64 (3 * R))
  by (rewrite (ew_Ereg_nat (ms_regs ms) _ 14 14%bv eq_refl); exact X14).
assert (A18 : ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 (data + 3 * R))) 18 = w64 SHADOW_OFF)
  by (rewrite (ew_Ereg_nat (ms_regs ms) _ 18 18%bv eq_refl); exact X18).
assert (A36 : ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 (data + 3 * R))) 36 = w64 b0)
  by (change 36%nat with (32 + 4)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (A37 : ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 (data + 3 * R))) 37 = w64 b1)
  by (change 37%nat with (32 + 5)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (A38 : ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 (data + 3 * R))) 38 = w64 (data + 3 * R))
  by (change 38%nat with (32 + 6)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (U8 : bv_unsigned (ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 (data + 3 * R))) 8) = len)
  by (rewrite A8; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 (data + 3 * R))) 11) = q + 4 * R)
  by (rewrite A11; apply unsigned_lit_small; unfold enc_size in *; lia).
assert (U14 : bv_unsigned (ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 (data + 3 * R))) 14) = 3 * R)
  by (rewrite A14; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 (data + 3 * R))) 18) = SHADOW_OFF)
  by (rewrite A18; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U36 : bv_unsigned (ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 (data + 3 * R))) 36) = b0)
  by (rewrite A36; apply unsigned_lit_small; lia).
assert (U37 : bv_unsigned (ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 (data + 3 * R))) 37) = b1)
  by (rewrite A37; apply unsigned_lit_small; lia).
assert (U38 : bv_unsigned (ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 (data + 3 * R))) 38) = data + 3 * R)
  by (rewrite A38; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold encT_ss2. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- vm_compute; reflexivity.
- constructor; [|constructor; [|constructor]].
  + unfold encT_rin2, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U38. split; [lia|]. split; [unfold PTOP in *; lia|].
    split; [intros o Ho; lia|]. constructor; [|constructor; [|constructor]].
    * apply (chunk_ok_val tfibsegs _ _ (data + 3 * R) 0 1%N (SOff 36 0) b0);
        [rewrite fsw_SOff0, A36; reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
        | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_r; exact V0].
    * apply (chunk_ok_val tfibsegs _ _ (data + 3 * R) 1 1%N (SOff 37 0) b1);
        [rewrite fsw_SOff0, A37; reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
        | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; exact V1].
  + unfold encT_rout, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U11. split; [lia|]. split; [unfold PTOP, enc_size in *; lia|].
    split; [|constructor]. intros o Ho. replace (q + 4 * R + o) with (q + (4 * R + o)) by lia.
    apply (encR_wr_out (ms_mem ms) md HARU). unfold enc_size in *. lia.
- apply pairwise_disjoint_of_extents. unfold encT_rin2, encT_rout, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U38, U11.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  destruct (encR_dj ltac:(lia)) as [D|D];
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold enc_size in *; lia.
- unfold encT_gf, encT_al, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split].
  + unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U18, U38, U11, U8, U14, U36, U37. rewrite !Z.pow_0_r.
    unfold PTOP, SHADOW_OFF, enc_size in *.
    repeat split; try lia; try (apply Z.mod_1_r).
  + split; [|exact I]. unfold acond_ok. cbn [ac_c ac_a ac_b].
    rewrite branch_ltu_U. apply Z.ltb_lt.
    rewrite (U_atom_off _ 14 (3 * R) 1 A14 ltac:(lia) ltac:(lia)),
            (U_atom _ 8 len A8 ltac:(lia)). lia.
  + split; [|exact I]. apply U_inj.
    rewrite (enc_U_add2 _ 9 14 0 0 data (3 * R) A9 A14 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
               ltac:(lia)).
    rewrite (U_atom _ 38 (data + 3 * R) A38 ltac:(lia)). lia.
Qed.

(* ---- the tail's shadow entries: the leftover byte(s), the output quad, and one live table seat ---- *)
Lemma encT_sh0 : forall mem (mdx : Model) (E : env) R (c : Z), encR_agree mem ->
  0 <= R -> 3 * R + c <= len -> 1 <= c <= 2 ->
  ARU tfibsegs B lyc Sc (U0 ++ [(q - HEAD, HEAD)]) Wc mem mdx ->
  U E enc_Bx = SHADOW_OFF -> U E (SOff 38 0) = data + 3 * R -> U E (SOff 11 0) = q + 4 * R ->
  sh_ok tfibsegs enc_Bx [mkSHE 38 0 c; mkSHE 11 0 4] E (mrestrict (w_H Wc) mem).
Proof.
intros mem mdx E R c HA HR HRc Hc HARU HB H38 H11.
pose proof encR_size_pos as HM. pose proof (encT_qR R HR ltac:(lia)) as HQ.
unfold sh_ok. constructor; [|constructor; [|constructor]].
- apply (enc_she Wc mem E 38%nat (data + 3 * R) 0 c data len HB H38);
    [exact (encR_ra_in mem mdx HARU ltac:(lia)) | lia | lia | lia|].
  intros x Hx. apply (encR_in_apart ltac:(lia)). lia.
- apply (enc_she Wc mem E 11%nat (q + 4 * R) 0 4 q (enc_size len) HB H11);
    [exact (encR_ra_out mem mdx HARU) | lia | unfold enc_size in *; lia | lia|].
  intros x Hx. apply (proj1 encR_out_facts). unfold enc_size in *. lia.
Qed.

Lemma encT_shs : forall mem (mdx : Model) (E : env) R (c : Z) (n : nat) v, encR_agree mem ->
  0 <= R -> 3 * R + c <= len -> 1 <= c <= 2 -> 0 <= v < 64 ->
  ARU tfibsegs B lyc Sc (U0 ++ [(q - HEAD, HEAD)]) Wc mem mdx ->
  U E enc_Bx = SHADOW_OFF -> U E (SOff 38 0) = data + 3 * R -> U E (SOff 11 0) = q + 4 * R ->
  U E (SOff n 0) = G_B64 + v ->
  sh_ok tfibsegs enc_Bx ([mkSHE 38 0 c; mkSHE 11 0 4] ++ [mkSHE n 0 1]) E (mrestrict (w_H Wc) mem).
Proof.
intros mem mdx E R c n v HA HR HRc Hc Hv HARU HB H38 H11 Hn.
unfold sh_ok. apply (proj2 (Forall_app _ [mkSHE 38 0 c; mkSHE 11 0 4] [mkSHE n 0 1])). split.
- exact (encT_sh0 mem mdx E R c HA HR HRc Hc HARU HB H38 H11).
- apply Forall_cons; [|apply Forall_nil].
  exact (encR_shent_seat mem E n v HA HB Hn Hv).
Qed.

(* ---- one table seat of the tail: g_b64 + a six-bit index, apart from the leftover bytes and the output quad ---- *)
Lemma encT_seat_dj : forall (E : env) (n : nat) (av R c : Z) (cs cs2 : list YP09.chunk),
  bv_unsigned (ew E n) = av -> bv_unsigned (ew E 38) = data + 3 * R ->
  bv_unsigned (ew E 11) = q + 4 * R -> G_B64 <= av < G_B64 + 64 ->
  0 <= R -> 3 * R + c <= len -> 1 <= c <= 2 ->
  all_disjoint E (YP09.mkRegion (Some n) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff (S n) 0))])
    [YP09.mkRegion (Some 38%nat) 0 c 0 0 cs; YP09.mkRegion (Some 11%nat) 0 4 0 4 cs2].
Proof.
intros E n av R c cs cs2 Hn H38 H11 Hav HR HRc Hc.
pose proof encR_size_pos as HM. pose proof (encT_qR R HR ltac:(lia)) as HQ.
apply all_disjoint_of_extents. unfold extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Hn, H38, H11.
cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
destruct (encR_dj_in_tab ltac:(lia)) as [D1|D1]; destruct encR_dj_out_tab as [D2|D2];
  repeat match goal with |- _ /\ _ => split end; try exact I; unfold G_B64, enc_size in *; lia.
Qed.

Lemma encT_seat_ok : forall (msX : machine_state) (E : env) (ss : sstate) (n : nat) (v R c : Z)
    (mdx : Model) (cs cs2 : list YP09.chunk),
  encR_agree (ms_mem msX) -> ARU tfibsegs B lyc Sc (U0 ++ [(q - HEAD, HEAD)]) Wc (ms_mem msX) mdx ->
  0 <= R -> 3 * R + c <= len -> 1 <= c <= 2 -> 0 <= v < 64 ->
  st_ok tfibsegs E ss (restrict (w_H Wc) msX) -> ss_atoms_lt n ss = true -> (38 < n)%nat ->
  getr (ms_regs msX) 12 = w64 (G_B64 + v) ->
  bv_unsigned (ew E 38) = data + 3 * R -> bv_unsigned (ew E 11) = q + 4 * R ->
  ss_mem ss = [YP09.mkRegion (Some 38%nat) 0 c 0 0 cs; YP09.mkRegion (Some 11%nat) 0 4 0 4 cs2] ->
  st_ok tfibsegs (ewset (ewset E n (w64 (G_B64 + v))) (S n) (w64 (WriterSpec.b64c v)))
    (enc_seat ss 12%bv n G_B64 (G_B64 + 63)) (restrict (w_H Wc) msX).
Proof.
intros msX E ss n v R c mdx cs cs2 HA HARU HR HRc Hc Hv HS Hat Hn Hreg H38 H11 Hmem.
pose proof (b64c_range v Hv) as HBr.
apply (enc_seat_ro1 E ss (restrict (w_H Wc) msX) 12%bv n (G_B64 + v) (WriterSpec.b64c v)
  G_B64 (G_B64 + 63) HS Hat ltac:(vm_compute; discriminate)).
- cbn [ms_regs restrict]. exact Hreg.
- unfold G_B64. lia.
- lia.
- unfold G_B64. lia.
- exact HBr.
- cbn [ms_mem restrict]. exact (encR_tab_keep (ms_mem msX) HA HTABc v Hv).
- rewrite Hmem. apply (encT_seat_dj _ n (G_B64 + v) R c cs cs2).
  + rewrite ew_ewset_other by lia. rewrite ew_ewset_same. apply unsigned_lit_small. unfold G_B64. lia.
  + rewrite !ew_ewset_other by lia. exact H38.
  + rewrite !ew_ewset_other by lia. exact H11.
  + unfold G_B64. lia.
  + lia.
  + lia.
  + lia.
Qed.

(* ---- the finish: the registers at 0x84700 and encR_nul ---- *)
Definition encT_kept_z : list Z := [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27].

Lemma encT_kept_in : forall z, acallee_saved z -> z <> 2 -> z <> 8 -> z <> 9 -> z <> 18 ->
  In z encT_kept_z.
Proof.
intros z Hz H2 H8 H9 H18. unfold acallee_saved in Hz. unfold encT_kept_z. cbn [In]. lia.
Qed.

Lemma encT_kept_reg : forall (E : env) (ss : sstate) (ms msE : machine_state) (xs : list word),
  st_ok tfibsegs E ss (restrict (w_H Wc) ms) ->
  env_agree 39 (Ereg (ms_regs msE) xs) E ->
  forallb (fun z => sv_eqb (sr_get (ss_regs ss) (Z_to_bv 5 z)) (SOff (Z.to_nat z) 0)) encT_kept_z = true ->
  forall z, In z encT_kept_z -> getr (ms_regs ms) (Z_to_bv 5 z) = getr (ms_regs msE) (Z_to_bv 5 z).
Proof.
intros E ss ms msE xs HS HAG HC z Hz.
assert (Hzr : 0 <= z <= 27) by (unfold encT_kept_z in Hz; cbn [In] in Hz; lia).
assert (Hbz : bv_unsigned (Z_to_bv 5 z) = z)
  by (rewrite Z_to_bv_unsigned, bv_wrap_small; [reflexivity | change (bv_modulus 5) with 32; lia]).
pose proof (proj1 (forallb_forall _ _) HC z Hz) as Hq. apply sv_eqb_eq in Hq.
rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) E ss ms (Z_to_bv 5 z) HS), Hq, fsw_SOff0.
rewrite (proj1 HAG (Z.to_nat z) ltac:(lia)).
exact (ew_Ereg_nat (ms_regs msE) xs (Z.to_nat z) (Z_to_bv 5 z) ltac:(lia)).
Qed.

Lemma encT_ag39 : forall (E E' : env) (k : nat), (39 <= k)%nat -> env_agree k E E' -> env_agree 39 E E'.
Proof. intros E E' k Hk HA. exact (YP03.env_agree_le 39 k E E' Hk HA). Qed.

Lemma encT_ag39t : forall (E1 E2 E3 : env),
  env_agree 39 E1 E2 -> env_agree 39 E2 E3 -> env_agree 39 E1 E3.
Proof. intros E1 E2 E3 H1 H2. exact (YP03.env_agree_trans 39 E1 E2 E3 H1 H2). Qed.

Lemma encT_fin : forall (E : env) (ss : sstate) (ms msE : machine_state) (md : Model) (R : Z)
    (xs : list word),
  st_ok tfibsegs E ss (restrict (w_H Wc) ms) ->
  env_agree 39 (Ereg (ms_regs msE) xs) E ->
  ss_pc ss = 0x84700 -> ss_resv ss = None ->
  sr_get (ss_regs ss) 2%bv = SOff 2 0 ->
  sr_get (ss_regs ss) 10%bv = SOff 10 0 ->
  sr_get (ss_regs ss) 11%bv = SOff 11 4 ->
  sr_get (ss_regs ss) 18%bv = SOff 18 0 ->
  forallb (fun z => sv_eqb (sr_get (ss_regs ss) (Z_to_bv 5 z)) (SOff (Z.to_nat z) 0)) encT_kept_z = true ->
  encR_inv (ms_mem ms) md ->
  garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) q (WriterSpec.b64_enc bs) ->
  encR_exit_regs msE R -> 0 <= R -> 3 * R + 1 <= len -> len <= 3 * R + 2 ->
  SRr tfibsegs Wc (mkCfg ms md)
    (fpostU tfibsegs B STK_preset_base64_encode (spZ regs0) FS_PSTAT_FP regs0 ly0 St0 U0 W0 mem0 md0
       EV_preset_base64_encode (U0 ++ [(q - HEAD, HEAD)]) encR_Q).
Proof.
intros E ss ms msE md R xs HS HAG Hpc Hrv S2 S10 S11 S18 HC HINV HPRE HX HR HR1 HR2.
pose proof encR_size_pos as HM. pose proof alloc_ceiling_val as (CR & _).
pose proof encR_out_facts as (_ & HQceil & _).
pose proof (encT_qR R HR HR1) as HQ. pose proof (encT_qRe R HR HR1 HR2) as HQe.
assert (HQlo : 4112 <= q) by (unfold HEAD in *; lia).
pose proof HX as (X8 & X9 & X10 & X11 & X14 & X18 & Xsp & Xk).
assert (A11 : ew E 11 = w64 (q + 4 * R))
  by (rewrite (proj1 HAG 11%nat ltac:(lia)), (ew_Ereg_nat (ms_regs msE) xs 11 11%bv eq_refl); exact X11).
apply (encR_nul ms md HINV HPRE).
- rewrite <- Hpc. exact (st_ok_restrict_mkst tfibsegs (w_H Wc) E ss ms HS Hrv).
- rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) E ss ms 10%bv HS), S10, fsw_SOff0,
    (proj1 HAG 10%nat ltac:(lia)), (ew_Ereg_nat (ms_regs msE) xs 10 10%bv eq_refl). exact X10.
- rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) E ss ms 11%bv HS), S11.
  apply (enc_denot_of_U E (SOff 11 4) (q + 4 * ((len + 2) / 3))).
  rewrite (U_atom_off E 11 (q + 4 * R) 4 A11 ltac:(unfold enc_size in *; lia)
             ltac:(unfold enc_size in *; lia)), HQe. lia.
- rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) E ss ms 18%bv HS), S18, fsw_SOff0,
    (proj1 HAG 18%nat ltac:(lia)), (ew_Ereg_nat (ms_regs msE) xs 18 18%bv eq_refl). exact X18.
- unfold spZ.
  rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) E ss ms 2%bv HS), S2, fsw_SOff0,
    (proj1 HAG 2%nat ltac:(lia)), (ew_Ereg_nat (ms_regs msE) xs 2 2%bv eq_refl). exact Xsp.
- intros z Hz H2 H8 H9 H18.
  rewrite (encT_kept_reg E ss ms msE xs HS HAG HC z (encT_kept_in z Hz H2 H8 H9 H18)).
  exact (Xk z Hz H2 H8 H9 H18).
Qed.

(* ---- the tail with ONE leftover byte (len = 3R + 1): three runs, two seats ---- *)
Lemma encR_tail1 : forall ms md R b0,
  encR_inv (ms_mem ms) md -> encR_exit_regs ms R ->
  ms = mkst (ms_regs ms) (w64 0x845e0) (ms_mem ms) (seg_rom tfibsegs) ->
  garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) q
    (WriterSpec.b64_enc (firstn (Z.to_nat (3 * R)) bs)) ->
  0 <= R -> len = 3 * R + 1 -> nth (Z.to_nat (3 * R)) bs 0 = b0 ->
  SRr tfibsegs Wc (mkCfg ms md)
    (fpostU tfibsegs B STK_preset_base64_encode (spZ regs0) FS_PSTAT_FP regs0 ly0 St0 U0 W0 mem0 md0
       EV_preset_base64_encode (U0 ++ [(q - HEAD, HEAD)]) encR_Q).
Proof.
intros ms md R b0 HINV HX Hms HPRE HR Hlen N0.
pose proof encR_size_pos as HM. pose proof alloc_ceiling_val as (CR & _).
pose proof encR_out_facts as (HAPq & HQceil & HQimg).
pose proof (encT_qR R HR ltac:(lia)) as HQ.
pose proof HINV as (HJ0 & HARU0 & HA0).
assert (HQlo : 4112 <= q) by (unfold HEAD in *; lia).
pose proof HX as (X8 & X9 & X10 & X11 & X14 & X18 & Xsp & Xk).
destruct (encT_state1 ms md R b0 HR Hlen HINV HX N0) as (HS0 & B0).
rewrite <- Hms in HS0.
assert (I0 : 0 <= b0 / 4 < 64)
  by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (I1 : 0 <= (b0 mod 4) * 16 < 64) by (pose proof (Z.mod_pos_bound b0 4 ltac:(lia)); lia).
assert (HB0 : encT_base (Ereg (ms_regs ms) (encR_extra3 b0 0 (data + 3 * R))) ms R b0 0).
{ unfold encT_base.
  split; [rewrite (ew_Ereg_nat (ms_regs ms) _ 2 2%bv eq_refl); reflexivity|].
  split; [rewrite (ew_Ereg_nat (ms_regs ms) _ 8 8%bv eq_refl); exact X8|].
  split; [rewrite (ew_Ereg_nat (ms_regs ms) _ 9 9%bv eq_refl); exact X9|].
  split; [rewrite (ew_Ereg_nat (ms_regs ms) _ 10 10%bv eq_refl); exact X10|].
  split; [rewrite (ew_Ereg_nat (ms_regs ms) _ 11 11%bv eq_refl); exact X11|].
  split; [rewrite (ew_Ereg_nat (ms_regs ms) _ 14 14%bv eq_refl); exact X14|].
  split; [rewrite (ew_Ereg_nat (ms_regs ms) _ 18 18%bv eq_refl); exact X18|].
  split; [change 36%nat with (32 + 4)%nat; rewrite ew_Ereg_extra; reflexivity|].
  split; [change 37%nat with (32 + 5)%nat; rewrite ew_Ereg_extra; reflexivity|].
  change 38%nat with (32 + 6)%nat; rewrite ew_Ereg_extra; reflexivity. }
destruct (encT_U_of_base _ ms R b0 0 HB0 HR ltac:(lia)) as (U18a & U38a & U11a & E38a & E11a).
assert (SH0 : sh_ok tfibsegs enc_Bx encT_SH1 (Ereg (ms_regs ms) (encR_extra3 b0 0 (data + 3 * R)))
  (mrestrict (w_H Wc) (ms_mem ms)))
  by exact (encT_sh0 (ms_mem ms) md _ R 1 HA0 HR ltac:(lia) ltac:(lia) HARU0 U18a U38a U11a).
(* segment A: 0x845e0 -> 0x84638, the leftover byte's shadow check, its read, and the first table address *)
apply (encT_seg _ encT_ss1 encT_SH1 0x84638 encT_A1 ms ms md R b0 0 _ HS0 SH0 HINV HB0
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; lia) HR ltac:(lia)).
intros ws1 ms1 md1 Hln1 HS1 HINV1 HB1 HAG1 HF1 HFr1.
pose proof HB1 as (B2a & B8a & B9a & B10a & B11a & B14a & B18a & B36a & B37a & B38a).
destruct (encT_U_of_base _ ms R b0 0 HB1 HR ltac:(lia)) as (U18b & U38b & U11b & E38b & E11b).
pose proof HINV1 as (HJ1 & HARU1 & HA1).
(* seat 100: a2 = g_b64 + bA / 4 *)
assert (RA1 : getr (ms_regs ms1) 12 = w64 (G_B64 + b0 / 4)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) _ _ ms1 12%bv HS1).
  lazymatch goal with |- sv_denot _ ?t = _ => let t' := eval vm_compute in t in change t with t' end.
  apply enc_denot_of_U. apply (encT_U_addG _ _ (b0 / 4)); [|lia].
  exact (encT_U_i0 _ b0 B36a ltac:(lia)). }
pose proof (encT_seat_ok ms1 _ (sh_ss encT_A1) 100 (b0 / 4) R 1 md1 _ _ HA1 HARU1 HR ltac:(lia)
  ltac:(lia) I0 HS1 ltac:(vm_compute; reflexivity) ltac:(lia) RA1 E38b E11b ltac:(reflexivity)) as HS1s.
lazymatch type of HS1 with st_ok _ ?EA _ _ =>
lazymatch type of HS1s with st_ok _ ?EB _ _ =>
  assert (G0s : env_agree 100 EA EB) by apply env_agree_ewset2;
  assert (A101 : ew EB 101 = w64 (WriterSpec.b64c (b0 / 4))) by apply ew_ewset_same;
  assert (HB1s : encT_base EB ms R b0 0)
    by exact (encT_base_agree EA EB ms R b0 0 100%nat ltac:(lia) G0s HB1);
  assert (U100 : U EB (SOff 100 0) = G_B64 + b0 / 4)
    by (apply encR_U_of_bv; [rewrite ew_ewset_other by lia; rewrite ew_ewset_same;
         apply unsigned_lit_small; unfold G_B64; lia | unfold G_B64; lia])
end end.
destruct (encT_U_of_base _ ms R b0 0 HB1s HR ltac:(lia)) as (U18c & U38c & U11c & E38c & E11c).
assert (SH1s : sh_ok tfibsegs enc_Bx encT_SH1_100
  (ewset (ewset (extK (Ereg (ms_regs ms) (encR_extra3 b0 0 (data + 3 * R)))
                   (run_K 0 enc_Bx encT_SH1 encT_ss1) ws1) 100 (w64 (G_B64 + b0 / 4)))
     (S 100) (w64 (WriterSpec.b64c (b0 / 4)))) (mrestrict (w_H Wc) (ms_mem ms1)))
  by (unfold encT_SH1_100, encT_SH1;
      exact (encT_shs (ms_mem ms1) md1 _ R 1 100 (b0 / 4) HA1 HR ltac:(lia) ltac:(lia) I0 HARU1
               U18c U38c U11c U100)).
(* segment B: 0x84638 -> 0x84670, the seat's byte, the first output byte and the second table address *)
apply (encT_seg _ encT_A1s encT_SH1_100 0x84670 encT_B1 ms1 ms md1 R b0 0 _ HS1s SH1s HINV1 HB1s
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; lia) HR ltac:(lia)).
intros ws2 ms2 md2 Hln2 HS2 HINV2 HB2 HAG2 HF2 HFr2.
pose proof HB2 as (C2a & C8a & C9a & C10a & C11a & C14a & C18a & C36a & C37a & C38a).
pose proof HINV2 as (HJ2 & HARU2 & HA2).
assert (A101b : ew (extK _ (run_K 0 enc_Bx encT_SH1_100 encT_A1s) ws2) 101
  = w64 (WriterSpec.b64c (b0 / 4)))
  by (rewrite (proj1 HAG2 101%nat ltac:(vm_compute; lia)); exact A101).
(* the seat the run is done with is dropped and the next one seated *)
pose proof ((fun Hm => enc_drop_head _ _ _ _ _ Hm HS2) ltac:(vm_compute; reflexivity)) as HSd2.
assert (RA2 : getr (ms_regs ms2) 12 = w64 (G_B64 + (b0 mod 4) * 16)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) _ _ ms2 12%bv HS2).
  lazymatch goal with |- sv_denot _ ?t = _ => let t' := eval vm_compute in t in change t with t' end.
  apply enc_denot_of_U. apply (encT_U_addG _ _ ((b0 mod 4) * 16)); [|lia].
  exact (encT_U_i1a _ b0 C36a ltac:(lia)). }
destruct (encT_U_of_base _ ms R b0 0 HB2 HR ltac:(lia)) as (U18d & U38d & U11d & E38d & E11d).
pose proof (encT_seat_ok ms2 _ (encT_drop (sh_ss encT_B1)) 200 ((b0 mod 4) * 16) R 1 md2 _ _
  HA2 HARU2 HR ltac:(lia) ltac:(lia) I1 HSd2 ltac:(vm_compute; reflexivity) ltac:(lia) RA2
  E38d E11d ltac:(reflexivity)) as HS2s.
lazymatch type of HS2 with st_ok _ ?EA _ _ =>
lazymatch type of HS2s with st_ok _ ?EB _ _ =>
  assert (G1s : env_agree 200 EA EB) by apply env_agree_ewset2;
  assert (A201 : ew EB 201 = w64 (WriterSpec.b64c ((b0 mod 4) * 16))) by apply ew_ewset_same;
  assert (A101c : ew EB 101 = w64 (WriterSpec.b64c (b0 / 4)))
    by (rewrite (proj1 G1s 101%nat ltac:(lia)); exact A101b);
  assert (HB2s : encT_base EB ms R b0 0)
    by exact (encT_base_agree EA EB ms R b0 0 200%nat ltac:(lia) G1s HB2);
  assert (U200 : U EB (SOff 200 0) = G_B64 + (b0 mod 4) * 16)
    by (apply encR_U_of_bv; [rewrite ew_ewset_other by lia; rewrite ew_ewset_same;
         apply unsigned_lit_small; unfold G_B64; lia | unfold G_B64; lia])
end end.
destruct (encT_U_of_base _ ms R b0 0 HB2s HR ltac:(lia)) as (U18e & U38e & U11e & E38e & E11e).
assert (SH2s : sh_ok tfibsegs enc_Bx encT_SH1_200
  (ewset (ewset (extK _ (run_K 0 enc_Bx encT_SH1_100 encT_A1s) ws2) 200
            (w64 (G_B64 + (b0 mod 4) * 16))) (S 200) (w64 (WriterSpec.b64c ((b0 mod 4) * 16))))
  (mrestrict (w_H Wc) (ms_mem ms2)))
  by (unfold encT_SH1_200, encT_SH1;
      exact (encT_shs (ms_mem ms2) md2 _ R 1 200 ((b0 mod 4) * 16) HA2 HR ltac:(lia) ltac:(lia) I1
               HARU2 U18e U38e U11e U200)).
(* segment C: 0x84670 -> 0x84700, the second output byte and the two '=' bytes *)
apply (encT_seg _ encT_B1s encT_SH1_200 0x84700 encT_C1 ms2 ms md2 R b0 0 _ HS2s SH2s HINV2 HB2s
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; lia) HR ltac:(lia)).
intros ws3 ms3 md3 Hln3 HS3 HINV3 HB3 HAG3 HF3 HFr3.
assert (A101d : ew (extK _ (run_K 0 enc_Bx encT_SH1_200 encT_B1s) ws3) 101
  = w64 (WriterSpec.b64c (b0 / 4)))
  by (rewrite (proj1 HAG3 101%nat ltac:(vm_compute; lia)); exact A101c).
assert (A201d : ew (extK _ (run_K 0 enc_Bx encT_SH1_200 encT_B1s) ws3) 201
  = w64 (WriterSpec.b64c ((b0 mod 4) * 16)))
  by (rewrite (proj1 HAG3 201%nat ltac:(vm_compute; lia)); exact A201).
destruct (encT_U_of_base _ ms R b0 0 HB3 HR ltac:(lia)) as (U18f & U38f & U11f & E38f & E11f).
(* the three runs wrote only this round's four output bytes *)
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (q + 4 * R <= a < q + 4 * R + 4) ->
  mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms3)) a
  = mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) a).
{ intros a Ha Hx. unfold mbyte.
  rewrite (enc_frame_X _ _ _ _ (fun x => q + 4 * R <= x < q + 4 * R + 4) HFr3
    ltac:(intros z Hz; exact (encT_wr_win _ (ss_mem encT_B1s) z R ltac:(vm_compute; reflexivity)
            E11e Hz)) (Z_to_bv 64 a) ltac:(rewrite (wz a Ha); exact Hx)).
  rewrite (enc_frame_X _ _ _ _ (fun x => q + 4 * R <= x < q + 4 * R + 4) HFr2
    ltac:(intros z Hz; exact (encT_wr_win _ (ss_mem encT_A1s) z R ltac:(vm_compute; reflexivity)
            E11c Hz)) (Z_to_bv 64 a) ltac:(rewrite (wz a Ha); exact Hx)).
  rewrite (enc_frame_X _ _ _ _ (fun x => q + 4 * R <= x < q + 4 * R + 4) HFr1
    ltac:(intros z Hz; exact (encT_wr_win _ (ss_mem encT_ss1) z R ltac:(vm_compute; reflexivity)
            E11a Hz)) (Z_to_bv 64 a) ltac:(rewrite (wz a Ha); exact Hx)).
  reflexivity. }
(* the four bytes of the last quad, read off the output region's chunks *)
pose proof (fsw_region_nth _ _ (restrict (w_H Wc) ms3) 2
  (YP09.mkRegion (Some 11%nat) 0 4 0 4
     [YP09.mkChunk 3 (CVal 1 (SLit 61)); YP09.mkChunk 2 (CVal 1 (SLit 61));
      YP09.mkChunk 1 (CVal 1 (SOff 201 0)); YP09.mkChunk 0 (CVal 1 (SOff 101 0))])
  HS3 ltac:(vm_compute; reflexivity)) as HRout.
cbn [ms_mem restrict] in HRout.
assert (VO0 : val_mem tfibsegs (mrestrict (w_H Wc) (ms_mem ms3)) (q + 4 * R + 0) 1
  (WriterSpec.b64c (b0 / 4)))
  by (apply (fsw_field _ _ 11 (q + 4 * R) _ 0 4 0 4 0 1%N (SOff 101 0) (WriterSpec.b64c (b0 / 4))
        HRout E11f); [cbn; tauto | rewrite fsw_SOff0, A101d; reflexivity
      | cbn [Z.of_N]; pose proof (b64c_range (b0 / 4) I0); lia | cbn [Z.of_N]; lia]).
assert (VO1 : val_mem tfibsegs (mrestrict (w_H Wc) (ms_mem ms3)) (q + 4 * R + 1) 1
  (WriterSpec.b64c ((b0 mod 4) * 16)))
  by (apply (fsw_field _ _ 11 (q + 4 * R) _ 0 4 0 4 1 1%N (SOff 201 0)
        (WriterSpec.b64c ((b0 mod 4) * 16)) HRout E11f);
      [cbn; tauto | rewrite fsw_SOff0, A201d; reflexivity
      | cbn [Z.of_N]; pose proof (b64c_range ((b0 mod 4) * 16) I1); lia | cbn [Z.of_N]; lia]).
assert (VO2 : val_mem tfibsegs (mrestrict (w_H Wc) (ms_mem ms3)) (q + 4 * R + 2) 1 61)
  by (apply (fsw_field _ _ 11 (q + 4 * R) _ 0 4 0 4 2 1%N (SLit 61) 61 HRout E11f);
      [cbn; tauto | rewrite denot_lit_U, U_SLit; reflexivity | cbn [Z.of_N]; lia
      | cbn [Z.of_N]; lia]).
assert (VO3 : val_mem tfibsegs (mrestrict (w_H Wc) (ms_mem ms3)) (q + 4 * R + 3) 1 61)
  by (apply (fsw_field _ _ 11 (q + 4 * R) _ 0 4 0 4 3 1%N (SLit 61) 61 HRout E11f);
      [cbn; tauto | rewrite denot_lit_U, U_SLit; reflexivity | cbn [Z.of_N]; lia
      | cbn [Z.of_N]; lia]).
(* the whole base64 text is now in the output block *)
destruct (encT_model1 R b0 HR Hlen N0) as (HMODEL & HLEN4).
assert (HPRE' : garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms3)) q (WriterSpec.b64_enc bs)).
{ rewrite HMODEL.
  apply (encR_garr8_app4 (mrestrict (w_H Wc) (ms_mem ms3))
    (WriterSpec.b64_enc (firstn (Z.to_nat (3 * R)) bs))
    (WriterSpec.b64c (b0 / 4)) (WriterSpec.b64c ((b0 mod 4) * 16)) 61 61 q (4 * R));
    first [ solve [apply (encR_garr8_keep (mrestrict (w_H Wc) (ms_mem ms)) _ q _
                     (fun x => q + 4 * R <= x < q + 4 * R + 4) KEEP ltac:(lia)
                     ltac:(rewrite HLEN4; unfold enc_size in *; lia)
                     ltac:(intros i Hi; rewrite HLEN4 in Hi; lia) HPRE)]
          | solve [exact HLEN4] | solve [lia] | solve [unfold enc_size in *; lia]
          | solve [exact VO0] | solve [exact VO1] | solve [exact VO2] | solve [exact VO3]
          | solve [pose proof (b64c_range (b0 / 4) I0); lia]
          | solve [pose proof (b64c_range ((b0 mod 4) * 16) I1); lia] ]. }
(* 0x84700: the terminating 0 and the epilogue *)
apply (encT_fin _ (sh_ss encT_C1) ms3 ms md3 R (encR_extra3 b0 0 (data + 3 * R)) HS3).
- exact (encT_ag39t _ _ _
    (encT_ag39t _ _ _
      (encT_ag39 _ _ (run_K 0 enc_Bx encT_SH1 encT_ss1) ltac:(vm_compute; lia) HAG1)
      (encT_ag39 _ _ 100%nat ltac:(lia) G0s))
    (encT_ag39t _ _ _
      (encT_ag39 _ _ (run_K 0 enc_Bx encT_SH1_100 encT_A1s) ltac:(vm_compute; lia) HAG2)
      (encT_ag39t _ _ _ (encT_ag39 _ _ 200%nat ltac:(lia) G1s)
        (encT_ag39 _ _ (run_K 0 enc_Bx encT_SH1_200 encT_B1s) ltac:(vm_compute; lia) HAG3)))).
- vm_compute; reflexivity.
- vm_compute; reflexivity.
- vm_compute; reflexivity.
- vm_compute; reflexivity.
- vm_compute; reflexivity.
- vm_compute; reflexivity.
- vm_compute; reflexivity.
- exact HINV3.
- exact HPRE'.
- exact HX.
- exact HR.
- lia.
- lia.
Qed.

(* ---- the tail with TWO leftover bytes (len = 3R + 2): four runs, three seats ---- *)
Lemma encR_tail2 : forall ms md R b0 b1,
  encR_inv (ms_mem ms) md -> encR_exit_regs ms R ->
  ms = mkst (ms_regs ms) (w64 0x845e0) (ms_mem ms) (seg_rom tfibsegs) ->
  garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) q
    (WriterSpec.b64_enc (firstn (Z.to_nat (3 * R)) bs)) ->
  0 <= R -> len = 3 * R + 2 ->
  nth (Z.to_nat (3 * R)) bs 0 = b0 -> nth (Z.to_nat (3 * R + 1)) bs 0 = b1 ->
  SRr tfibsegs Wc (mkCfg ms md)
    (fpostU tfibsegs B STK_preset_base64_encode (spZ regs0) FS_PSTAT_FP regs0 ly0 St0 U0 W0 mem0 md0
       EV_preset_base64_encode (U0 ++ [(q - HEAD, HEAD)]) encR_Q).
Proof.
intros ms md R b0 b1 HINV HX Hms HPRE HR Hlen N0 N1.
pose proof encR_size_pos as HM. pose proof alloc_ceiling_val as (CR & _).
pose proof encR_out_facts as (HAPq & HQceil & HQimg).
pose proof (encT_qR R HR ltac:(lia)) as HQ.
pose proof HINV as (HJ0 & HARU0 & HA0).
assert (HQlo : 4112 <= q) by (unfold HEAD in *; lia).
pose proof HX as (X8 & X9 & X10 & X11 & X14 & X18 & Xsp & Xk).
destruct (encT_state2 ms md R b0 b1 HR Hlen HINV HX N0 N1) as (HS0 & B0 & B1).
rewrite <- Hms in HS0.
assert (I0 : 0 <= b0 / 4 < 64)
  by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
assert (I1 : 0 <= (b0 mod 4) * 16 + b1 / 16 < 64).
{ pose proof (Z.mod_pos_bound b0 4 ltac:(lia)).
  assert (0 <= b1 / 16 < 16) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  lia. }
assert (I2 : 0 <= (b1 mod 16) * 4 < 64) by (pose proof (Z.mod_pos_bound b1 16 ltac:(lia)); lia).
assert (HB0 : encT_base (Ereg (ms_regs ms) (encR_extra3 b0 b1 (data + 3 * R))) ms R b0 b1).
{ unfold encT_base.
  split; [rewrite (ew_Ereg_nat (ms_regs ms) _ 2 2%bv eq_refl); reflexivity|].
  split; [rewrite (ew_Ereg_nat (ms_regs ms) _ 8 8%bv eq_refl); exact X8|].
  split; [rewrite (ew_Ereg_nat (ms_regs ms) _ 9 9%bv eq_refl); exact X9|].
  split; [rewrite (ew_Ereg_nat (ms_regs ms) _ 10 10%bv eq_refl); exact X10|].
  split; [rewrite (ew_Ereg_nat (ms_regs ms) _ 11 11%bv eq_refl); exact X11|].
  split; [rewrite (ew_Ereg_nat (ms_regs ms) _ 14 14%bv eq_refl); exact X14|].
  split; [rewrite (ew_Ereg_nat (ms_regs ms) _ 18 18%bv eq_refl); exact X18|].
  split; [change 36%nat with (32 + 4)%nat; rewrite ew_Ereg_extra; reflexivity|].
  split; [change 37%nat with (32 + 5)%nat; rewrite ew_Ereg_extra; reflexivity|].
  change 38%nat with (32 + 6)%nat; rewrite ew_Ereg_extra; reflexivity. }
destruct (encT_U_of_base _ ms R b0 b1 HB0 HR ltac:(lia)) as (U18a & U38a & U11a & E38a & E11a).
assert (SH0 : sh_ok tfibsegs enc_Bx encT_SH2 (Ereg (ms_regs ms) (encR_extra3 b0 b1 (data + 3 * R)))
  (mrestrict (w_H Wc) (ms_mem ms)))
  by exact (encT_sh0 (ms_mem ms) md _ R 2 HA0 HR ltac:(lia) ltac:(lia) HARU0 U18a U38a U11a).
(* segment A: 0x845e0 -> 0x84638, both leftover bytes' checks and reads, the first table address *)
apply (encT_seg _ encT_ss2 encT_SH2 0x84638 encT_A2 ms ms md R b0 b1 _ HS0 SH0 HINV HB0
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; lia) HR ltac:(lia)).
intros ws1 ms1 md1 Hln1 HS1 HINV1 HB1 HAG1 HF1 HFr1.
pose proof HB1 as (B2a & B8a & B9a & B10a & B11a & B14a & B18a & B36a & B37a & B38a).
destruct (encT_U_of_base _ ms R b0 b1 HB1 HR ltac:(lia)) as (U18b & U38b & U11b & E38b & E11b).
pose proof HINV1 as (HJ1 & HARU1 & HA1).
assert (RA1 : getr (ms_regs ms1) 12 = w64 (G_B64 + b0 / 4)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) _ _ ms1 12%bv HS1).
  lazymatch goal with |- sv_denot _ ?t = _ => let t' := eval vm_compute in t in change t with t' end.
  apply enc_denot_of_U. apply (encT_U_addG _ _ (b0 / 4)); [|lia].
  exact (encT_U_i0 _ b0 B36a ltac:(lia)). }
pose proof (encT_seat_ok ms1 _ (sh_ss encT_A2) 100 (b0 / 4) R 2 md1 _ _ HA1 HARU1 HR ltac:(lia)
  ltac:(lia) I0 HS1 ltac:(vm_compute; reflexivity) ltac:(lia) RA1 E38b E11b ltac:(reflexivity)) as HS1s.
lazymatch type of HS1 with st_ok _ ?EA _ _ =>
lazymatch type of HS1s with st_ok _ ?EB _ _ =>
  assert (G0s : env_agree 100 EA EB) by apply env_agree_ewset2;
  assert (A101 : ew EB 101 = w64 (WriterSpec.b64c (b0 / 4))) by apply ew_ewset_same;
  assert (HB1s : encT_base EB ms R b0 b1)
    by exact (encT_base_agree EA EB ms R b0 b1 100%nat ltac:(lia) G0s HB1);
  assert (U100 : U EB (SOff 100 0) = G_B64 + b0 / 4)
    by (apply encR_U_of_bv; [rewrite ew_ewset_other by lia; rewrite ew_ewset_same;
         apply unsigned_lit_small; unfold G_B64; lia | unfold G_B64; lia])
end end.
destruct (encT_U_of_base _ ms R b0 b1 HB1s HR ltac:(lia)) as (U18c & U38c & U11c & E38c & E11c).
assert (SH1s : sh_ok tfibsegs enc_Bx encT_SH2_100
  (ewset (ewset (extK (Ereg (ms_regs ms) (encR_extra3 b0 b1 (data + 3 * R)))
                   (run_K 0 enc_Bx encT_SH2 encT_ss2) ws1) 100 (w64 (G_B64 + b0 / 4)))
     (S 100) (w64 (WriterSpec.b64c (b0 / 4)))) (mrestrict (w_H Wc) (ms_mem ms1)))
  by (unfold encT_SH2_100, encT_SH2;
      exact (encT_shs (ms_mem ms1) md1 _ R 2 100 (b0 / 4) HA1 HR ltac:(lia) ltac:(lia) I0 HARU1
               U18c U38c U11c U100)).
(* segment B: 0x84638 -> 0x84670, the seat's byte, the first output byte and the second table address *)
apply (encT_seg _ encT_A2s encT_SH2_100 0x84670 encT_B2 ms1 ms md1 R b0 b1 _ HS1s SH1s HINV1 HB1s
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; lia) HR ltac:(lia)).
intros ws2 ms2 md2 Hln2 HS2 HINV2 HB2 HAG2 HF2 HFr2.
pose proof HB2 as (C2a & C8a & C9a & C10a & C11a & C14a & C18a & C36a & C37a & C38a).
pose proof HINV2 as (HJ2 & HARU2 & HA2).
assert (A101b : ew (extK _ (run_K 0 enc_Bx encT_SH2_100 encT_A2s) ws2) 101
  = w64 (WriterSpec.b64c (b0 / 4)))
  by (rewrite (proj1 HAG2 101%nat ltac:(vm_compute; lia)); exact A101).
pose proof ((fun Hm => enc_drop_head _ _ _ _ _ Hm HS2) ltac:(vm_compute; reflexivity)) as HSd2.
assert (RA2 : getr (ms_regs ms2) 12 = w64 (G_B64 + ((b0 mod 4) * 16 + b1 / 16))).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) _ _ ms2 12%bv HS2).
  lazymatch goal with |- sv_denot _ ?t = _ => let t' := eval vm_compute in t in change t with t' end.
  apply enc_denot_of_U. apply (encT_U_addG _ _ ((b0 mod 4) * 16 + b1 / 16)); [|lia].
  exact (enc_U_t1 _ b0 b1 C36a C37a ltac:(lia) ltac:(lia)). }
destruct (encT_U_of_base _ ms R b0 b1 HB2 HR ltac:(lia)) as (U18d & U38d & U11d & E38d & E11d).
pose proof (encT_seat_ok ms2 _ (encT_drop (sh_ss encT_B2)) 200 ((b0 mod 4) * 16 + b1 / 16) R 2 md2 _ _
  HA2 HARU2 HR ltac:(lia) ltac:(lia) I1 HSd2 ltac:(vm_compute; reflexivity) ltac:(lia) RA2
  E38d E11d ltac:(reflexivity)) as HS2s.
lazymatch type of HS2 with st_ok _ ?EA _ _ =>
lazymatch type of HS2s with st_ok _ ?EB _ _ =>
  assert (G1s : env_agree 200 EA EB) by apply env_agree_ewset2;
  assert (A201 : ew EB 201 = w64 (WriterSpec.b64c ((b0 mod 4) * 16 + b1 / 16)))
    by apply ew_ewset_same;
  assert (A101c : ew EB 101 = w64 (WriterSpec.b64c (b0 / 4)))
    by (rewrite (proj1 G1s 101%nat ltac:(lia)); exact A101b);
  assert (HB2s : encT_base EB ms R b0 b1)
    by exact (encT_base_agree EA EB ms R b0 b1 200%nat ltac:(lia) G1s HB2);
  assert (U200 : U EB (SOff 200 0) = G_B64 + ((b0 mod 4) * 16 + b1 / 16))
    by (apply encR_U_of_bv; [rewrite ew_ewset_other by lia; rewrite ew_ewset_same;
         apply unsigned_lit_small; unfold G_B64; lia | unfold G_B64; lia])
end end.
destruct (encT_U_of_base _ ms R b0 b1 HB2s HR ltac:(lia)) as (U18e & U38e & U11e & E38e & E11e).
assert (SH2s : sh_ok tfibsegs enc_Bx encT_SH2_200
  (ewset (ewset (extK _ (run_K 0 enc_Bx encT_SH2_100 encT_A2s) ws2) 200
            (w64 (G_B64 + ((b0 mod 4) * 16 + b1 / 16)))) (S 200)
     (w64 (WriterSpec.b64c ((b0 mod 4) * 16 + b1 / 16)))) (mrestrict (w_H Wc) (ms_mem ms2)))
  by (unfold encT_SH2_200, encT_SH2;
      exact (encT_shs (ms_mem ms2) md2 _ R 2 200 ((b0 mod 4) * 16 + b1 / 16) HA2 HR ltac:(lia)
               ltac:(lia) I1 HARU2 U18e U38e U11e U200)).
(* segment C: 0x84670 -> 0x846ac, the second output byte and the third table address *)
apply (encT_seg _ encT_B2s encT_SH2_200 0x846ac encT_C2 ms2 ms md2 R b0 b1 _ HS2s SH2s HINV2 HB2s
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; lia) HR ltac:(lia)).
intros ws3 ms3 md3 Hln3 HS3 HINV3 HB3 HAG3 HF3 HFr3.
pose proof HB3 as (D2a & D8a & D9a & D10a & D11a & D14a & D18a & D36a & D37a & D38a).
pose proof HINV3 as (HJ3 & HARU3 & HA3).
assert (A101d : ew (extK _ (run_K 0 enc_Bx encT_SH2_200 encT_B2s) ws3) 101
  = w64 (WriterSpec.b64c (b0 / 4)))
  by (rewrite (proj1 HAG3 101%nat ltac:(vm_compute; lia)); exact A101c).
assert (A201d : ew (extK _ (run_K 0 enc_Bx encT_SH2_200 encT_B2s) ws3) 201
  = w64 (WriterSpec.b64c ((b0 mod 4) * 16 + b1 / 16)))
  by (rewrite (proj1 HAG3 201%nat ltac:(vm_compute; lia)); exact A201).
pose proof ((fun Hm => enc_drop_head _ _ _ _ _ Hm HS3) ltac:(vm_compute; reflexivity)) as HSd3.
assert (RA3 : getr (ms_regs ms3) 12 = w64 (G_B64 + (b1 mod 16) * 4)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) _ _ ms3 12%bv HS3).
  lazymatch goal with |- sv_denot _ ?t = _ => let t' := eval vm_compute in t in change t with t' end.
  apply enc_denot_of_U. apply (encT_U_addG _ _ ((b1 mod 16) * 4)); [|lia].
  exact (encT_U_i2 _ b1 D37a ltac:(lia)). }
destruct (encT_U_of_base _ ms R b0 b1 HB3 HR ltac:(lia)) as (U18f & U38f & U11f & E38f & E11f).
pose proof (encT_seat_ok ms3 _ (encT_drop (sh_ss encT_C2)) 300 ((b1 mod 16) * 4) R 2 md3 _ _
  HA3 HARU3 HR ltac:(lia) ltac:(lia) I2 HSd3 ltac:(vm_compute; reflexivity) ltac:(lia) RA3
  E38f E11f ltac:(reflexivity)) as HS3s.
lazymatch type of HS3 with st_ok _ ?EA _ _ =>
lazymatch type of HS3s with st_ok _ ?EB _ _ =>
  assert (G2s : env_agree 300 EA EB) by apply env_agree_ewset2;
  assert (A301 : ew EB 301 = w64 (WriterSpec.b64c ((b1 mod 16) * 4))) by apply ew_ewset_same;
  assert (A101e : ew EB 101 = w64 (WriterSpec.b64c (b0 / 4)))
    by (rewrite (proj1 G2s 101%nat ltac:(lia)); exact A101d);
  assert (A201e : ew EB 201 = w64 (WriterSpec.b64c ((b0 mod 4) * 16 + b1 / 16)))
    by (rewrite (proj1 G2s 201%nat ltac:(lia)); exact A201d);
  assert (HB3s : encT_base EB ms R b0 b1)
    by exact (encT_base_agree EA EB ms R b0 b1 300%nat ltac:(lia) G2s HB3);
  assert (U300 : U EB (SOff 300 0) = G_B64 + (b1 mod 16) * 4)
    by (apply encR_U_of_bv; [rewrite ew_ewset_other by lia; rewrite ew_ewset_same;
         apply unsigned_lit_small; unfold G_B64; lia | unfold G_B64; lia])
end end.
destruct (encT_U_of_base _ ms R b0 b1 HB3s HR ltac:(lia)) as (U18g & U38g & U11g & E38g & E11g).
assert (SH3s : sh_ok tfibsegs enc_Bx encT_SH2_300
  (ewset (ewset (extK _ (run_K 0 enc_Bx encT_SH2_200 encT_B2s) ws3) 300
            (w64 (G_B64 + (b1 mod 16) * 4))) (S 300) (w64 (WriterSpec.b64c ((b1 mod 16) * 4))))
  (mrestrict (w_H Wc) (ms_mem ms3)))
  by (unfold encT_SH2_300, encT_SH2;
      exact (encT_shs (ms_mem ms3) md3 _ R 2 300 ((b1 mod 16) * 4) HA3 HR ltac:(lia) ltac:(lia) I2
               HARU3 U18g U38g U11g U300)).
(* segment D: 0x846ac -> 0x84700, the third output byte and the one '=' byte *)
apply (encT_seg _ encT_C2s encT_SH2_300 0x84700 encT_D2 ms3 ms md3 R b0 b1 _ HS3s SH3s HINV3 HB3s
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; lia) HR ltac:(lia)).
intros ws4 ms4 md4 Hln4 HS4 HINV4 HB4 HAG4 HF4 HFr4.
assert (A101f : ew (extK _ (run_K 0 enc_Bx encT_SH2_300 encT_C2s) ws4) 101
  = w64 (WriterSpec.b64c (b0 / 4)))
  by (rewrite (proj1 HAG4 101%nat ltac:(vm_compute; lia)); exact A101e).
assert (A201f : ew (extK _ (run_K 0 enc_Bx encT_SH2_300 encT_C2s) ws4) 201
  = w64 (WriterSpec.b64c ((b0 mod 4) * 16 + b1 / 16)))
  by (rewrite (proj1 HAG4 201%nat ltac:(vm_compute; lia)); exact A201e).
assert (A301f : ew (extK _ (run_K 0 enc_Bx encT_SH2_300 encT_C2s) ws4) 301
  = w64 (WriterSpec.b64c ((b1 mod 16) * 4)))
  by (rewrite (proj1 HAG4 301%nat ltac:(vm_compute; lia)); exact A301).
destruct (encT_U_of_base _ ms R b0 b1 HB4 HR ltac:(lia)) as (U18h & U38h & U11h & E38h & E11h).
assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (q + 4 * R <= a < q + 4 * R + 4) ->
  mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms4)) a
  = mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) a).
{ intros a Ha Hx. unfold mbyte.
  rewrite (enc_frame_X _ _ _ _ (fun x => q + 4 * R <= x < q + 4 * R + 4) HFr4
    ltac:(intros z Hz; exact (encT_wr_win _ (ss_mem encT_C2s) z R ltac:(vm_compute; reflexivity)
            E11g Hz)) (Z_to_bv 64 a) ltac:(rewrite (wz a Ha); exact Hx)).
  rewrite (enc_frame_X _ _ _ _ (fun x => q + 4 * R <= x < q + 4 * R + 4) HFr3
    ltac:(intros z Hz; exact (encT_wr_win _ (ss_mem encT_B2s) z R ltac:(vm_compute; reflexivity)
            E11e Hz)) (Z_to_bv 64 a) ltac:(rewrite (wz a Ha); exact Hx)).
  rewrite (enc_frame_X _ _ _ _ (fun x => q + 4 * R <= x < q + 4 * R + 4) HFr2
    ltac:(intros z Hz; exact (encT_wr_win _ (ss_mem encT_A2s) z R ltac:(vm_compute; reflexivity)
            E11c Hz)) (Z_to_bv 64 a) ltac:(rewrite (wz a Ha); exact Hx)).
  rewrite (enc_frame_X _ _ _ _ (fun x => q + 4 * R <= x < q + 4 * R + 4) HFr1
    ltac:(intros z Hz; exact (encT_wr_win _ (ss_mem encT_ss2) z R ltac:(vm_compute; reflexivity)
            E11a Hz)) (Z_to_bv 64 a) ltac:(rewrite (wz a Ha); exact Hx)).
  reflexivity. }
pose proof (fsw_region_nth _ _ (restrict (w_H Wc) ms4) 2
  (YP09.mkRegion (Some 11%nat) 0 4 0 4
     [YP09.mkChunk 3 (CVal 1 (SLit 61)); YP09.mkChunk 2 (CVal 1 (SOff 301 0));
      YP09.mkChunk 1 (CVal 1 (SOff 201 0)); YP09.mkChunk 0 (CVal 1 (SOff 101 0))])
  HS4 ltac:(vm_compute; reflexivity)) as HRout.
cbn [ms_mem restrict] in HRout.
assert (VO0 : val_mem tfibsegs (mrestrict (w_H Wc) (ms_mem ms4)) (q + 4 * R + 0) 1
  (WriterSpec.b64c (b0 / 4)))
  by (apply (fsw_field _ _ 11 (q + 4 * R) _ 0 4 0 4 0 1%N (SOff 101 0) (WriterSpec.b64c (b0 / 4))
        HRout E11h); [cbn; tauto | rewrite fsw_SOff0, A101f; reflexivity
      | cbn [Z.of_N]; pose proof (b64c_range (b0 / 4) I0); lia | cbn [Z.of_N]; lia]).
assert (VO1 : val_mem tfibsegs (mrestrict (w_H Wc) (ms_mem ms4)) (q + 4 * R + 1) 1
  (WriterSpec.b64c ((b0 mod 4) * 16 + b1 / 16)))
  by (apply (fsw_field _ _ 11 (q + 4 * R) _ 0 4 0 4 1 1%N (SOff 201 0)
        (WriterSpec.b64c ((b0 mod 4) * 16 + b1 / 16)) HRout E11h);
      [cbn; tauto | rewrite fsw_SOff0, A201f; reflexivity
      | cbn [Z.of_N]; pose proof (b64c_range ((b0 mod 4) * 16 + b1 / 16) I1); lia
      | cbn [Z.of_N]; lia]).
assert (VO2 : val_mem tfibsegs (mrestrict (w_H Wc) (ms_mem ms4)) (q + 4 * R + 2) 1
  (WriterSpec.b64c ((b1 mod 16) * 4)))
  by (apply (fsw_field _ _ 11 (q + 4 * R) _ 0 4 0 4 2 1%N (SOff 301 0)
        (WriterSpec.b64c ((b1 mod 16) * 4)) HRout E11h);
      [cbn; tauto | rewrite fsw_SOff0, A301f; reflexivity
      | cbn [Z.of_N]; pose proof (b64c_range ((b1 mod 16) * 4) I2); lia | cbn [Z.of_N]; lia]).
assert (VO3 : val_mem tfibsegs (mrestrict (w_H Wc) (ms_mem ms4)) (q + 4 * R + 3) 1 61)
  by (apply (fsw_field _ _ 11 (q + 4 * R) _ 0 4 0 4 3 1%N (SLit 61) 61 HRout E11h);
      [cbn; tauto | rewrite denot_lit_U, U_SLit; reflexivity | cbn [Z.of_N]; lia
      | cbn [Z.of_N]; lia]).
destruct (encT_model2 R b0 b1 HR Hlen N0 N1) as (HMODEL & HLEN4).
assert (HPRE' : garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms4)) q (WriterSpec.b64_enc bs)).
{ rewrite HMODEL.
  apply (encR_garr8_app4 (mrestrict (w_H Wc) (ms_mem ms4))
    (WriterSpec.b64_enc (firstn (Z.to_nat (3 * R)) bs))
    (WriterSpec.b64c (b0 / 4)) (WriterSpec.b64c ((b0 mod 4) * 16 + b1 / 16))
    (WriterSpec.b64c ((b1 mod 16) * 4)) 61 q (4 * R));
    first [ solve [apply (encR_garr8_keep (mrestrict (w_H Wc) (ms_mem ms)) _ q _
                     (fun x => q + 4 * R <= x < q + 4 * R + 4) KEEP ltac:(lia)
                     ltac:(rewrite HLEN4; unfold enc_size in *; lia)
                     ltac:(intros i Hi; rewrite HLEN4 in Hi; lia) HPRE)]
          | solve [exact HLEN4] | solve [lia] | solve [unfold enc_size in *; lia]
          | solve [exact VO0] | solve [exact VO1] | solve [exact VO2] | solve [exact VO3]
          | solve [pose proof (b64c_range (b0 / 4) I0); lia]
          | solve [pose proof (b64c_range ((b0 mod 4) * 16 + b1 / 16) I1); lia]
          | solve [pose proof (b64c_range ((b1 mod 16) * 4) I2); lia] ]. }
apply (encT_fin _ (sh_ss encT_D2) ms4 ms md4 R (encR_extra3 b0 b1 (data + 3 * R)) HS4).
- exact (encT_ag39t _ _ _
    (encT_ag39t _ _ _
      (encT_ag39 _ _ (run_K 0 enc_Bx encT_SH2 encT_ss2) ltac:(vm_compute; lia) HAG1)
      (encT_ag39 _ _ 100%nat ltac:(lia) G0s))
    (encT_ag39t _ _ _
      (encT_ag39t _ _ _
        (encT_ag39 _ _ (run_K 0 enc_Bx encT_SH2_100 encT_A2s) ltac:(vm_compute; lia) HAG2)
        (encT_ag39 _ _ 200%nat ltac:(lia) G1s))
      (encT_ag39t _ _ _
        (encT_ag39 _ _ (run_K 0 enc_Bx encT_SH2_200 encT_B2s) ltac:(vm_compute; lia) HAG3)
        (encT_ag39t _ _ _ (encT_ag39 _ _ 300%nat ltac:(lia) G2s)
          (encT_ag39 _ _ (run_K 0 enc_Bx encT_SH2_300 encT_C2s) ltac:(vm_compute; lia) HAG4))))).
- vm_compute; reflexivity.
- vm_compute; reflexivity.
- vm_compute; reflexivity.
- vm_compute; reflexivity.
- vm_compute; reflexivity.
- vm_compute; reflexivity.
- vm_compute; reflexivity.
- exact HINV4.
- exact HPRE'.
- exact HX.
- exact HR.
- lia.
- lia.
Qed.

(* ---- the tail, 0x845e0 .. 0x846fc then encR_nul: one or two leftover bytes ---- *)
Lemma encR_tail : forall ms md R,
  encR_inv (ms_mem ms) md ->
  encR_exit_regs ms R ->
  ms = mkst (ms_regs ms) (w64 0x845e0) (ms_mem ms) (seg_rom tfibsegs) ->
  garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) q
    (WriterSpec.b64_enc (firstn (Z.to_nat (3 * R)) bs)) ->
  0 <= R -> 3 * R < len < 3 * R + 3 ->
  SRr tfibsegs Wc (mkCfg ms md)
    (fpostU tfibsegs B STK_preset_base64_encode (spZ regs0) FS_PSTAT_FP regs0 ly0 St0 U0 W0 mem0 md0
       EV_preset_base64_encode (U0 ++ [(q - HEAD, HEAD)]) encR_Q).
Proof.
intros ms md R HINV HX Hms HPRE HR Hlen.
assert (Hc : len = 3 * R + 1 \/ len = 3 * R + 2) by lia. destruct Hc as [He|He].
- exact (encR_tail1 ms md R (nth (Z.to_nat (3 * R)) bs 0) HINV HX Hms HPRE HR He eq_refl).
- exact (encR_tail2 ms md R (nth (Z.to_nat (3 * R)) bs 0) (nth (Z.to_nat (3 * R + 1)) bs 0)
    HINV HX Hms HPRE HR He eq_refl eq_refl).
Qed.
(* ==== END the tail block ==== *)
Lemma encR_round_step : forall ms md r b0 b1 b2 (Q : world tfibsegs -> config -> Prop),
  0 <= r -> 3 * r + 3 <= len ->
  encR_inv (ms_mem ms) md -> encR_loop_regs ms r ->
  garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) q
    (WriterSpec.b64_enc (firstn (Z.to_nat (3 * r)) bs)) ->
  nth (Z.to_nat (3 * r)) bs 0 = b0 -> nth (Z.to_nat (3 * r + 1)) bs 0 = b1 ->
  nth (Z.to_nat (3 * r + 2)) bs 0 = b2 ->
  (forall ms' md', 3 * (r + 1) + 3 <= len -> encR_inv (ms_mem ms') md' -> encR_loop_regs ms' (r + 1) ->
     ms' = mkst (ms_regs ms') (w64 0x843fc) (ms_mem ms') (seg_rom tfibsegs) ->
     garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms')) q
       (WriterSpec.b64_enc (firstn (Z.to_nat (3 * (r + 1))) bs)) ->
     SRr tfibsegs Wc (mkCfg ms' md') Q) ->
  (forall ms' md', len <= 3 * (r + 1) + 2 -> encR_inv (ms_mem ms') md' -> encR_exit_regs ms' (r + 1) ->
     ms' = mkst (ms_regs ms') (w64 0x845dc) (ms_mem ms') (seg_rom tfibsegs) ->
     garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms')) q
       (WriterSpec.b64_enc (firstn (Z.to_nat (3 * (r + 1))) bs)) ->
     SRr tfibsegs Wc (mkCfg ms' md') Q) ->
  SRr tfibsegs Wc (mkCfg (mkst (ms_regs ms) (w64 0x843fc) (ms_mem ms) (seg_rom tfibsegs)) md) Q.
Proof.
intros ms md r b0 b1 b2 Q Hr Hr3 HINV HR HPRE N0 N1 N2 KNEXT KEXIT.
pose proof HR as (R8 & R9 & R10 & R11 & R12 & R14 & R15 & R17 & R18 & Rsp & Rk).
pose proof encR_size_pos as HM. pose proof alloc_ceiling_val as (CR & _).
pose proof encR_out_facts as (HAPq & HQceil & HQimg).
assert (HQlo : 4112 <= q) by (unfold HEAD in *; lia).
destruct HINV as (HJ & HARU & HA). unfold encR_J in HJ.
destruct (encR_round_state ms md r b0 b1 b2 Hr Hr3 (conj HJ (conj HARU HA)) HR N0 N1 N2)
  as (HS & B0 & B1 & B2).
destruct (encR_round_env ms r b0 b1 b2 HR) as (A11 & A12 & A15 & A17 & A18).
assert (A36 : ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) 36 = w64 b0)
  by (change 36%nat with (32 + 4)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (A37 : ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) 37 = w64 b1)
  by (change 37%nat with (32 + 5)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (A38 : ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) 38 = w64 b2)
  by (change 38%nat with (32 + 6)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (U18 : U (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) enc_Bx = SHADOW_OFF)
  by (apply (U_atom _ 18 _ A18); unfold SHADOW_OFF; lia).
assert (U12 : U (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) (SOff 12 0) = data + 3 * r + 2)
  by (apply (U_atom _ 12 _ A12); lia).
assert (U17 : U (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) (SOff 17 0) = q + 4 * r)
  by (apply (U_atom _ 17 _ A17); unfold enc_size in *; lia).
assert (U11 : U (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) (SOff 11 0) = q + 4 * r)
  by (apply (U_atom _ 11 _ A11); unfold enc_size in *; lia).
assert (E17u : bv_unsigned (ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) 17) = q + 4 * r)
  by (rewrite A17; apply unsigned_lit_small; unfold enc_size in *; lia).
assert (SHOK : sh_ok tfibsegs enc_Bx enc_SH (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2))
  (mrestrict (w_H Wc) (ms_mem ms)))
  by exact (encR_sh0 (ms_mem ms) md _ r HA Hr Hr3 HARU U18 U12 U17 U11).
(* segment A: 0x843fc -> 0x84448, the three input shadow checks and the first table index *)
fsw_aj_run_to_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan 0x84448.
all: first
  [ solve [ cbn [enc_round_ss ss_mem];
            apply awr_ok_cons_ro; [cbn; lia|];
            eapply awr_ok_cons_gen with (k := 17%nat) (b := q + 4 * r);
            [ reflexivity | exact E17u
            | cbn [enc_rout YP09.r_wlo YP09.r_whi]; intros a Ha; left; right; right; left;
              exists (q - HEAD), (enc_size len + HEAD); split; [exact HQB|];
              split; [exact encR_new_block|];
              unfold req_size; destruct (enc_size len + HEAD =? 0) eqn:EQ;
              [apply Z.eqb_eq in EQ; unfold HEAD in *; lia | unfold HEAD, enc_size in *; lia]
            | apply awr_ok_nil ] ]
  | idtac ].
(* the run wrote only inside the output block, so the invariant's agreement survives it *)
assert (HA0 : encR_agree (ms_mem ms0)).
{ intros x Hx.
  rewrite (enc_frame_X (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) (ss_mem (enc_round_ss 0x843fc))
    (ms_mem ms) (ms_mem ms0) encR_out HF); [exact (HA x Hx) | | exact Hx].
  intros a (rg & Hin & Hrg). cbn [enc_round_ss ss_mem In] in Hin.
  destruct Hin as [<-|[<-|[]]];
    cbn [enc_rin enc_rout YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg;
    [lia | unfold encR_out; rewrite E17u in Hrg; unfold enc_size in *; lia]. }
(* seat 100: a3 = g_b64 + b0 / 4 *)
destruct (enc_ix_range b0 b1 b2 B0 B1 B2) as (X0 & X1 & X2 & X3).
assert (RA3 : getr (ms_regs ms0) 13 = w64 (G_B64 + b0 / 4)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) _ _ ms0 13%bv HS).
  lazymatch goal with |- sv_denot _ ?t = _ => let t' := eval vm_compute in t in change t with t' end.
  apply enc_denot_of_U. apply (enc_U_addG _ _ (b0 / 4)).
  - repeat (rewrite ew_ewset_other by lia). exact A15.
  - apply (enc_U_t0 _ b0); [repeat (rewrite ew_ewset_other by lia); exact A36 | lia].
  - lia. }
lazymatch type of HS with st_ok _ ?EE _ _ =>
  assert (E12u0 : bv_unsigned (ew EE 12) = data + 3 * r + 2)
    by (repeat (rewrite ew_ewset_other by lia); rewrite A12; apply unsigned_lit_small; lia);
  assert (E17u0 : bv_unsigned (ew EE 17) = q + 4 * r)
    by (repeat (rewrite ew_ewset_other by lia); exact E17u)
end.
pose proof (encR_seat_ok ms0 _ _ 13%bv 100 (b0 / 4) r _ [] HA0 HARU Hr Hr3 ltac:(lia) HS
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(lia) RA3 E12u0 E17u0
  ltac:(vm_compute; reflexivity)) as HS1.
lazymatch type of HS1 with st_ok _ ?EE2 _ _ =>
  assert (SHOK1 : sh_ok tfibsegs enc_Bx enc_SH1 EE2 (mrestrict (w_H Wc) (ms_mem ms0)))
  by (unfold enc_SH1; apply Forall_app; split;
      [ apply (encR_sh0 (ms_mem ms0) _ _ r HA0 Hr Hr3 HARU);
        apply encR_U_of_bv;
        first [ solve [repeat (rewrite ew_ewset_other by lia); rewrite A18; apply unsigned_lit_small;
                       unfold SHADOW_OFF; lia]
              | solve [repeat (rewrite ew_ewset_other by lia); rewrite A12; apply unsigned_lit_small; lia]
              | solve [repeat (rewrite ew_ewset_other by lia); rewrite A17; apply unsigned_lit_small;
                       unfold enc_size in *; lia]
              | solve [repeat (rewrite ew_ewset_other by lia); rewrite A11; apply unsigned_lit_small;
                       unfold enc_size in *; lia]
              | solve [unfold SHADOW_OFF; lia] | solve [unfold enc_size in *; lia] | solve [lia] ]
      | constructor; [|constructor];
        apply (encR_shent_seat (ms_mem ms0) _ 100 (b0 / 4) HA0);
        first [ solve [apply encR_U_of_bv; [repeat (rewrite ew_ewset_other by lia); rewrite A18;
                         apply unsigned_lit_small; unfold SHADOW_OFF; lia | unfold SHADOW_OFF; lia]]
              | solve [apply encR_U_of_bv; [rewrite ew_ewset_other by lia; rewrite ew_ewset_same;
                         apply unsigned_lit_small; unfold G_B64; lia | unfold G_B64; lia]]
              | solve [lia] ] ])
end.
clear HS SHOK. rename HS1 into HS. rename SHOK1 into SHOK.
lazymatch type of HS with st_ok _ ?EE _ _ =>
  assert (E17B : bv_unsigned (ew EE 17) = q + 4 * r)
    by (repeat (rewrite ew_ewset_other by lia); exact E17u)
end.
(* segment B: 0x84448 -> 0x8448c, the seat's byte and the first output byte *)
fsw_aj_run_to_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan 0x8448c.
all: first
  [ solve [ cbn [enc_seat enc_round_ss add_atom ss_mem];
            repeat (apply awr_ok_cons_ro; [cbn; lia|]);
            eapply awr_ok_cons_gen with (k := 17%nat) (b := q + 4 * r);
            [ reflexivity | solve [repeat (rewrite ew_ewset_other by lia); exact E17u]
            | cbn [enc_rout YP09.r_wlo YP09.r_whi]; intros a Ha; left; right; right; left;
              exists (q - HEAD), (enc_size len + HEAD); split; [exact HQB|];
              split; [exact encR_new_block|];
              unfold req_size; destruct (enc_size len + HEAD =? 0) eqn:EQ;
              [apply Z.eqb_eq in EQ; unfold HEAD in *; lia | unfold HEAD, enc_size in *; lia]
            | apply awr_ok_nil ] ]
  | idtac ].
(* the seat the run is done with is dropped, the next one is seated, and the agreement is re-read *)
assert (HA1 : encR_agree (ms_mem ms1)).
{ intros x Hx.
  rewrite (enc_frame_X _ _ (ms_mem ms0) (ms_mem ms1) encR_out HF0); [exact (HA0 x Hx) | | exact Hx].
  intros a (rg & Hrin & Hrg). revert Hrg.
  lazymatch type of Hrin with In _ ?L => let L' := eval vm_compute in L in change L with L' in Hrin end.
  cbn [In] in Hrin. destruct Hrin as [<-|[<-|[<-|[]]]]; intros Hrg;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg;
    first [ lia | unfold encR_out; rewrite E17B in Hrg; unfold enc_size in *; lia ]. }
pose proof ((fun Hm => enc_drop_head _ _ _ _ _ Hm HS) ltac:(vm_compute; reflexivity)) as HSd1.
assert (RA2 : getr (ms_regs ms1) 12 = w64 (G_B64 + ((b0 mod 4) * 16 + b1 / 16))).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) _ _ ms1 12%bv HS).
  lazymatch goal with |- sv_denot _ ?t = _ => let t' := eval vm_compute in t in change t with t' end.
  apply enc_denot_of_U. apply (enc_U_addG _ _ ((b0 mod 4) * 16 + b1 / 16)).
  - repeat (rewrite ew_ewset_other by lia). exact A15.
  - apply (enc_U_t1 _ b0 b1);
      [repeat (rewrite ew_ewset_other by lia); exact A36
      | repeat (rewrite ew_ewset_other by lia); exact A37 | lia | lia].
  - lia. }
lazymatch type of HSd1 with st_ok _ ?EE _ _ =>
  assert (E12u1 : bv_unsigned (ew EE 12) = data + 3 * r + 2)
    by (repeat (rewrite ew_ewset_other by lia); rewrite A12; apply unsigned_lit_small; lia);
  assert (E17u1 : bv_unsigned (ew EE 17) = q + 4 * r)
    by (repeat (rewrite ew_ewset_other by lia); exact E17u)
end.
pose proof (encR_seat_ok ms1 _ _ 12%bv 200 ((b0 mod 4) * 16 + b1 / 16) r _
  [YP09.mkChunk 0 (CVal 1 (SOff 101 0))] HA1 HARU Hr Hr3 ltac:(lia) HSd1
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(lia) RA2 E12u1 E17u1
  ltac:(vm_compute; reflexivity)) as HS2.
lazymatch type of HS2 with st_ok _ ?EE2 _ _ =>
  assert (SHOK2 : sh_ok tfibsegs enc_Bx enc_SH2 EE2 (mrestrict (w_H Wc) (ms_mem ms1)))
  by (unfold enc_SH2, enc_SH1; apply Forall_app; split;
      [ apply Forall_app; split;
        [ apply (encR_sh0 (ms_mem ms1) _ _ r HA1 Hr Hr3 HARU);
          apply encR_U_of_bv;
          first [ solve [repeat (rewrite ew_ewset_other by lia); rewrite A18; apply unsigned_lit_small;
                         unfold SHADOW_OFF; lia]
                | solve [repeat (rewrite ew_ewset_other by lia); rewrite A12; apply unsigned_lit_small; lia]
                | solve [repeat (rewrite ew_ewset_other by lia); rewrite A17; apply unsigned_lit_small;
                         unfold enc_size in *; lia]
                | solve [repeat (rewrite ew_ewset_other by lia); rewrite A11; apply unsigned_lit_small;
                         unfold enc_size in *; lia]
                | solve [unfold SHADOW_OFF; lia] | solve [unfold enc_size in *; lia] | solve [lia] ]
        | constructor; [|constructor];
          apply (encR_shent_seat (ms_mem ms1) _ 100 (b0 / 4) HA1);
          first [ solve [apply encR_U_of_bv; [repeat (rewrite ew_ewset_other by lia); rewrite A18;
                           apply unsigned_lit_small; unfold SHADOW_OFF; lia | unfold SHADOW_OFF; lia]]
                | solve [apply encR_U_of_bv; [repeat (rewrite ew_ewset_other by lia);
                           rewrite ew_ewset_same; apply unsigned_lit_small; unfold G_B64; lia
                         | unfold G_B64; lia]]
                | solve [lia] ] ]
      | constructor; [|constructor];
        apply (encR_shent_seat (ms_mem ms1) _ 200 ((b0 mod 4) * 16 + b1 / 16) HA1);
        first [ solve [apply encR_U_of_bv; [repeat (rewrite ew_ewset_other by lia); rewrite A18;
                         apply unsigned_lit_small; unfold SHADOW_OFF; lia | unfold SHADOW_OFF; lia]]
              | solve [apply encR_U_of_bv; [rewrite ew_ewset_other by lia; rewrite ew_ewset_same;
                         apply unsigned_lit_small; unfold G_B64; lia | unfold G_B64; lia]]
              | solve [lia] ] ])
end.
clear HS SHOK HSd1. rename HS2 into HS. rename SHOK2 into SHOK.
lazymatch type of HS with st_ok _ ?EE _ _ =>
  assert (E17C : bv_unsigned (ew EE 17) = q + 4 * r)
    by (repeat (rewrite ew_ewset_other by lia); exact E17u)
end.
(* segment C: 0x8448c -> 0x844c8, the second output byte *)
fsw_aj_run_to_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan 0x844c8.
all: first
  [ solve [ cbn [enc_seat enc_round_ss add_atom ss_mem];
            repeat (apply awr_ok_cons_ro; [cbn; lia|]);
            eapply awr_ok_cons_gen with (k := 17%nat) (b := q + 4 * r);
            [ reflexivity | exact E17C
            | cbn [enc_rout YP09.r_wlo YP09.r_whi]; intros a Ha; left; right; right; left;
              exists (q - HEAD), (enc_size len + HEAD); split; [exact HQB|];
              split; [exact encR_new_block|];
              unfold req_size; destruct (enc_size len + HEAD =? 0) eqn:EQ;
              [apply Z.eqb_eq in EQ; unfold HEAD in *; lia | unfold HEAD, enc_size in *; lia]
            | apply awr_ok_nil ] ]
  | idtac ].
assert (HA2 : encR_agree (ms_mem ms2)).
{ intros x Hx.
  rewrite (enc_frame_X _ _ (ms_mem ms1) (ms_mem ms2) encR_out HF1); [exact (HA1 x Hx) | | exact Hx].
  intros a (rg & Hrin & Hrg). revert Hrg.
  lazymatch type of Hrin with In _ ?L => let L' := eval vm_compute in L in change L with L' in Hrin end.
  cbn [In] in Hrin. destruct Hrin as [<-|[<-|[<-|[]]]]; intros Hrg;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg;
    first [ lia | unfold encR_out; rewrite E17C in Hrg; unfold enc_size in *; lia ]. }
pose proof ((fun Hm => enc_drop_head _ _ _ _ _ Hm HS) ltac:(vm_compute; reflexivity)) as HSd2.
assert (RA3' : getr (ms_regs ms2) 12 = w64 (G_B64 + ((b1 mod 16) * 4 + b2 / 64))).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) _ _ ms2 12%bv HS).
  lazymatch goal with |- sv_denot _ ?t = _ => let t' := eval vm_compute in t in change t with t' end.
  apply enc_denot_of_U. apply (enc_U_addG _ _ ((b1 mod 16) * 4 + b2 / 64)).
  - repeat (rewrite ew_ewset_other by lia). exact A15.
  - apply (enc_U_t2 _ b1 b2);
      [repeat (rewrite ew_ewset_other by lia); exact A37
      | repeat (rewrite ew_ewset_other by lia); exact A38 | lia | lia].
  - lia. }
lazymatch type of HSd2 with st_ok _ ?EE _ _ =>
  assert (E12u2 : bv_unsigned (ew EE 12) = data + 3 * r + 2)
    by (repeat (rewrite ew_ewset_other by lia); rewrite A12; apply unsigned_lit_small; lia);
  assert (E17u2 : bv_unsigned (ew EE 17) = q + 4 * r)
    by (repeat (rewrite ew_ewset_other by lia); exact E17u)
end.
pose proof (encR_seat_ok ms2 _ _ 12%bv 300 ((b1 mod 16) * 4 + b2 / 64) r _
  [YP09.mkChunk 1 (CVal 1 (SOff 201 0)); YP09.mkChunk 0 (CVal 1 (SOff 101 0))]
  HA2 HARU Hr Hr3 ltac:(lia) HSd2
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(lia) RA3' E12u2 E17u2
  ltac:(vm_compute; reflexivity)) as HS3.
lazymatch type of HS3 with st_ok _ ?EE2 _ _ =>
  assert (SHOK3 : sh_ok tfibsegs enc_Bx enc_SH3 EE2 (mrestrict (w_H Wc) (ms_mem ms2)))
  by (unfold enc_SH3; apply (proj2 (Forall_app _ enc_SH2 [mkSHE 300 0 1])); split;
      [ unfold enc_SH2; apply (proj2 (Forall_app _ enc_SH1 [mkSHE 200 0 1])); split;
        [ unfold enc_SH1; apply (proj2 (Forall_app _ enc_SH [mkSHE 100 0 1])); split;
          [ enc_shbase (ms_mem ms2) HA2 r Hr Hr3 HARU A11 A12 A17 A18
          | apply Forall_cons; [enc_shseat (ms_mem ms2) HA2 100%nat (b0 / 4) A18 | apply Forall_nil] ]
        | apply Forall_cons;
          [enc_shseat (ms_mem ms2) HA2 200%nat ((b0 mod 4) * 16 + b1 / 16) A18 | apply Forall_nil] ]
      | apply Forall_cons;
        [enc_shseat (ms_mem ms2) HA2 300%nat ((b1 mod 16) * 4 + b2 / 64) A18 | apply Forall_nil] ])
end.
clear HS SHOK HSd2. rename HS3 into HS. rename SHOK3 into SHOK.
lazymatch type of HS with st_ok _ ?EE _ _ =>
  assert (E17D : bv_unsigned (ew EE 17) = q + 4 * r)
    by (repeat (rewrite ew_ewset_other by lia); exact E17u)
end.
(* segment D: 0x844c8 -> 0x844fc, the third output byte *)
fsw_aj_run_to_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan 0x844fc.
all: first
  [ solve [ cbn [enc_seat enc_round_ss add_atom ss_mem];
            repeat (apply awr_ok_cons_ro; [cbn; lia|]);
            eapply awr_ok_cons_gen with (k := 17%nat) (b := q + 4 * r);
            [ reflexivity | exact E17D
            | cbn [enc_rout YP09.r_wlo YP09.r_whi]; intros a Ha; left; right; right; left;
              exists (q - HEAD), (enc_size len + HEAD); split; [exact HQB|];
              split; [exact encR_new_block|];
              unfold req_size; destruct (enc_size len + HEAD =? 0) eqn:EQ;
              [apply Z.eqb_eq in EQ; unfold HEAD in *; lia | unfold HEAD, enc_size in *; lia]
            | apply awr_ok_nil ] ]
  | idtac ].
assert (HA3 : encR_agree (ms_mem ms3)).
{ intros x Hx.
  rewrite (enc_frame_X _ _ (ms_mem ms2) (ms_mem ms3) encR_out HF2); [exact (HA2 x Hx) | | exact Hx].
  intros a (rg & Hrin & Hrg). revert Hrg.
  lazymatch type of Hrin with In _ ?L => let L' := eval vm_compute in L in change L with L' in Hrin end.
  cbn [In] in Hrin. destruct Hrin as [<-|[<-|[<-|[]]]]; intros Hrg;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg;
    first [ lia | unfold encR_out; rewrite E17D in Hrg; unfold enc_size in *; lia ]. }
pose proof ((fun Hm => enc_drop_head _ _ _ _ _ Hm HS) ltac:(vm_compute; reflexivity)) as HSd3.
assert (RA4 : getr (ms_regs ms3) 12 = w64 (G_B64 + b2 mod 64)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) _ _ ms3 12%bv HS).
  lazymatch goal with |- sv_denot _ ?t = _ => let t' := eval vm_compute in t in change t with t' end.
  apply enc_denot_of_U. apply (enc_U_addG _ _ (b2 mod 64)).
  - repeat (rewrite ew_ewset_other by lia). exact A15.
  - apply (enc_U_t3 _ b2); [repeat (rewrite ew_ewset_other by lia); exact A38 | lia].
  - lia. }
lazymatch type of HSd3 with st_ok _ ?EE _ _ =>
  assert (E12u3 : bv_unsigned (ew EE 12) = data + 3 * r + 2)
    by (repeat (rewrite ew_ewset_other by lia); rewrite A12; apply unsigned_lit_small; lia);
  assert (E17u3 : bv_unsigned (ew EE 17) = q + 4 * r)
    by (repeat (rewrite ew_ewset_other by lia); exact E17u)
end.
pose proof (encR_seat_ok ms3 _ _ 12%bv 400 (b2 mod 64) r _
  [YP09.mkChunk 2 (CVal 1 (SOff 301 0)); YP09.mkChunk 1 (CVal 1 (SOff 201 0));
   YP09.mkChunk 0 (CVal 1 (SOff 101 0))]
  HA3 HARU Hr Hr3 ltac:(lia) HSd3
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(lia) RA4 E12u3 E17u3
  ltac:(vm_compute; reflexivity)) as HS4.
lazymatch type of HS4 with st_ok _ ?EE2 _ _ =>
  assert (SHOK4 : sh_ok tfibsegs enc_Bx enc_SH4 EE2 (mrestrict (w_H Wc) (ms_mem ms3)))
  by (unfold enc_SH4; apply (proj2 (Forall_app _ enc_SH3 [mkSHE 400 0 1])); split;
      [ unfold enc_SH3; apply (proj2 (Forall_app _ enc_SH2 [mkSHE 300 0 1])); split;
        [ unfold enc_SH2; apply (proj2 (Forall_app _ enc_SH1 [mkSHE 200 0 1])); split;
          [ unfold enc_SH1; apply (proj2 (Forall_app _ enc_SH [mkSHE 100 0 1])); split;
            [ enc_shbase (ms_mem ms3) HA3 r Hr Hr3 HARU A11 A12 A17 A18
            | apply Forall_cons; [enc_shseat (ms_mem ms3) HA3 100%nat (b0 / 4) A18 | apply Forall_nil] ]
          | apply Forall_cons;
            [enc_shseat (ms_mem ms3) HA3 200%nat ((b0 mod 4) * 16 + b1 / 16) A18 | apply Forall_nil] ]
        | apply Forall_cons;
          [enc_shseat (ms_mem ms3) HA3 300%nat ((b1 mod 16) * 4 + b2 / 64) A18 | apply Forall_nil] ]
      | apply Forall_cons; [enc_shseat (ms_mem ms3) HA3 400%nat (b2 mod 64) A18 | apply Forall_nil] ])
end.
clear HS SHOK HSd3. rename HS4 into HS. rename SHOK4 into SHOK.
lazymatch type of HS with st_ok _ ?EE _ _ =>
  assert (E17E : bv_unsigned (ew EE 17) = q + 4 * r)
    by (repeat (rewrite ew_ewset_other by lia); exact E17u)
end.
(* segment E: 0x844fc -> 0x84534, the fourth output byte and the loop's branch *)
fsw_aj_run_to_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan 0x84534.
all: first
  [ solve [ cbn [enc_seat enc_round_ss add_atom ss_mem];
            repeat (apply awr_ok_cons_ro; [cbn; lia|]);
            eapply awr_ok_cons_gen with (k := 17%nat) (b := q + 4 * r);
            [ reflexivity | exact E17E
            | cbn [enc_rout YP09.r_wlo YP09.r_whi]; intros a Ha; left; right; right; left;
              exists (q - HEAD), (enc_size len + HEAD); split; [exact HQB|];
              split; [exact encR_new_block|];
              unfold req_size; destruct (enc_size len + HEAD =? 0) eqn:EQ;
              [apply Z.eqb_eq in EQ; unfold HEAD in *; lia | unfold HEAD, enc_size in *; lia]
            | apply awr_ok_nil ] ]
  | idtac ].
assert (HA4 : encR_agree (ms_mem ms4)).
{ intros x Hx.
  rewrite (enc_frame_X _ _ (ms_mem ms3) (ms_mem ms4) encR_out HF3); [exact (HA3 x Hx) | | exact Hx].
  intros a (rg & Hrin & Hrg). revert Hrg.
  lazymatch type of Hrin with In _ ?L => let L' := eval vm_compute in L in change L with L' in Hrin end.
  cbn [In] in Hrin. destruct Hrin as [<-|[<-|[<-|[]]]]; intros Hrg;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg;
    first [ lia | unfold encR_out; rewrite E17E in Hrg; unfold enc_size in *; lia ]. }
(* the five runs of the round wrote only this round's four output bytes *)
assert (KEEPR : forall a, 0 <= a < 2 ^ 64 -> ~ (q + 4 * r <= a < q + 4 * r + 4) ->
  mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms4)) a = mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) a).
{ intros a Ha Hx. unfold mbyte.
  rewrite (enc_frame_X _ _ _ _ (fun x => q + 4 * r <= x < q + 4 * r + 4) HFr3
    ltac:(intros z (rg & Hrin & Hrg); revert Hrg;
          lazymatch type of Hrin with In _ ?L => let L' := eval vm_compute in L in
            change L with L' in Hrin end;
          cbn [In] in Hrin; destruct Hrin as [<-|[<-|[<-|[]]]]; intros Hrg;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg;
          first [ lia | rewrite E17E in Hrg; lia ])
    (Z_to_bv 64 a) ltac:(rewrite (wz a Ha); exact Hx)).
  rewrite (enc_frame_X _ _ _ _ (fun x => q + 4 * r <= x < q + 4 * r + 4) HFr2
    ltac:(intros z (rg & Hrin & Hrg); revert Hrg;
          lazymatch type of Hrin with In _ ?L => let L' := eval vm_compute in L in
            change L with L' in Hrin end;
          cbn [In] in Hrin; destruct Hrin as [<-|[<-|[<-|[]]]]; intros Hrg;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg;
          first [ lia | rewrite E17D in Hrg; lia ])
    (Z_to_bv 64 a) ltac:(rewrite (wz a Ha); exact Hx)).
  rewrite (enc_frame_X _ _ _ _ (fun x => q + 4 * r <= x < q + 4 * r + 4) HFr1
    ltac:(intros z (rg & Hrin & Hrg); revert Hrg;
          lazymatch type of Hrin with In _ ?L => let L' := eval vm_compute in L in
            change L with L' in Hrin end;
          cbn [In] in Hrin; destruct Hrin as [<-|[<-|[<-|[]]]]; intros Hrg;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg;
          first [ lia | rewrite E17C in Hrg; lia ])
    (Z_to_bv 64 a) ltac:(rewrite (wz a Ha); exact Hx)).
  rewrite (enc_frame_X _ _ _ _ (fun x => q + 4 * r <= x < q + 4 * r + 4) HFr0
    ltac:(intros z (rg & Hrin & Hrg); revert Hrg;
          lazymatch type of Hrin with In _ ?L => let L' := eval vm_compute in L in
            change L with L' in Hrin end;
          cbn [In] in Hrin; destruct Hrin as [<-|[<-|[<-|[]]]]; intros Hrg;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg;
          first [ lia | rewrite E17B in Hrg; lia ])
    (Z_to_bv 64 a) ltac:(rewrite (wz a Ha); exact Hx)).
  rewrite (enc_frame_X _ _ _ _ (fun x => q + 4 * r <= x < q + 4 * r + 4) HFr
    ltac:(intros z (rg & Hrin & Hrg); revert Hrg;
          lazymatch type of Hrin with In _ ?L => let L' := eval vm_compute in L in
            change L with L' in Hrin end;
          cbn [In] in Hrin; destruct Hrin as [<-|[<-|[]]]; intros Hrg;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg;
          first [ lia | rewrite E17u in Hrg; lia ])
    (Z_to_bv 64 a) ltac:(rewrite (wz a Ha); exact Hx)).
  reflexivity. }
(* the four output bytes of the round, read off the output region's chunks *)
lazymatch type of HS with st_ok _ ?EE _ _ =>
  assert (E17F : bv_unsigned (ew EE 17) = q + 4 * r)
    by (repeat (rewrite ew_ewset_other by lia); exact E17u)
end.
pose proof (fsw_region_nth _ _ (restrict (w_H Wc) ms4) 2
  (YP09.mkRegion (Some 17%nat) 0 4 0 4
     [YP09.mkChunk 3 (CVal 1 (SOff 401 0)); YP09.mkChunk 2 (CVal 1 (SOff 301 0));
      YP09.mkChunk 1 (CVal 1 (SOff 201 0)); YP09.mkChunk 0 (CVal 1 (SOff 101 0))])
  HS ltac:(vm_compute; reflexivity)) as HRout.
cbn [ms_mem restrict] in HRout.
lazymatch type of HS with st_ok _ ?EE _ _ =>
  assert (VQ : forall (od : Z) (n : nat) v,
    In (YP09.mkChunk od (CVal 1 (SOff n 0)))
       [YP09.mkChunk 3 (CVal 1 (SOff 401 0)); YP09.mkChunk 2 (CVal 1 (SOff 301 0));
        YP09.mkChunk 1 (CVal 1 (SOff 201 0)); YP09.mkChunk 0 (CVal 1 (SOff 101 0))] ->
    sv_denot EE (SOff n 0) = Z_to_bv 64 v -> 0 <= v < 256 ->
    val_mem tfibsegs (mrestrict (w_H Wc) (ms_mem ms4)) (q + 4 * r + od) 1 v)
  by (intros od n v Hin Hd Hv;
      exact (fsw_field _ _ 17 (q + 4 * r) _ 0 4 0 4 od 1%N (SOff n 0) v HRout E17F Hin Hd
        ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia)))
end.
assert (VO0 : val_mem tfibsegs (mrestrict (w_H Wc) (ms_mem ms4)) (q + 4 * r + 0) 1
  (WriterSpec.b64c (b0 / 4)))
  by (apply (VQ 0 101%nat); [cbn; tauto
      | rewrite fsw_SOff0; repeat (rewrite ew_ewset_other by lia); rewrite ew_ewset_same; reflexivity
      | pose proof (b64c_range (b0 / 4) ltac:(lia)); lia]).
assert (VO1 : val_mem tfibsegs (mrestrict (w_H Wc) (ms_mem ms4)) (q + 4 * r + 1) 1
  (WriterSpec.b64c ((b0 mod 4) * 16 + b1 / 16)))
  by (apply (VQ 1 201%nat); [cbn; tauto
      | rewrite fsw_SOff0; repeat (rewrite ew_ewset_other by lia); rewrite ew_ewset_same; reflexivity
      | pose proof (b64c_range ((b0 mod 4) * 16 + b1 / 16) ltac:(lia)); lia]).
assert (VO2 : val_mem tfibsegs (mrestrict (w_H Wc) (ms_mem ms4)) (q + 4 * r + 2) 1
  (WriterSpec.b64c ((b1 mod 16) * 4 + b2 / 64)))
  by (apply (VQ 2 301%nat); [cbn; tauto
      | rewrite fsw_SOff0; repeat (rewrite ew_ewset_other by lia); rewrite ew_ewset_same; reflexivity
      | pose proof (b64c_range ((b1 mod 16) * 4 + b2 / 64) ltac:(lia)); lia]).
assert (VO3 : val_mem tfibsegs (mrestrict (w_H Wc) (ms_mem ms4)) (q + 4 * r + 3) 1
  (WriterSpec.b64c (b2 mod 64)))
  by (apply (VQ 3 401%nat); [cbn; tauto
      | rewrite fsw_SOff0; repeat (rewrite ew_ewset_other by lia); rewrite ew_ewset_same; reflexivity
      | pose proof (b64c_range (b2 mod 64) ltac:(lia)); lia]).
(* the base64 text written so far gains this round's four letters *)
destruct (encR_prefix_step r b0 b1 b2 Hr Hr3 N0 N1 N2) as (HMODEL & HLEN4).
assert (HPRE' : garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms4)) q
  (WriterSpec.b64_enc (firstn (Z.to_nat (3 * (r + 1))) bs))).
{ rewrite HMODEL.
  apply (encR_garr8_app4 _ _ _ _ _ _ q (4 * r));
    first [ solve [apply (encR_garr8_keep (mrestrict (w_H Wc) (ms_mem ms)) _ q _
                     (fun x => q + 4 * r <= x < q + 4 * r + 4) KEEPR ltac:(lia)
                     ltac:(rewrite HLEN4; unfold enc_size in *; lia)
                     ltac:(intros i Hi; rewrite HLEN4 in Hi; lia) HPRE)]
          | solve [exact HLEN4] | solve [lia] | solve [unfold enc_size in *; lia]
          | solve [exact VO0] | solve [exact VO1] | solve [exact VO2] | solve [exact VO3]
          | solve [pose proof (b64c_range (b0 / 4) ltac:(lia)); lia]
          | solve [pose proof (b64c_range ((b0 mod 4) * 16 + b1 / 16) ltac:(lia)); lia]
          | solve [pose proof (b64c_range ((b1 mod 16) * 4 + b2 / 64) ltac:(lia)); lia]
          | solve [pose proof (b64c_range (b2 mod 64) ltac:(lia)); lia] ]. }
(* the loop's branch: `bltu a4, s0` at 0x84534 *)
assert (A8 : ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) 8 = w64 len)
  by (rewrite (ew_Ereg_nat (ms_regs ms) _ 8 8%bv eq_refl); exact R8).
assert (A9 : ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) 9 = w64 data)
  by (rewrite (ew_Ereg_nat (ms_regs ms) _ 9 9%bv eq_refl); exact R9).
assert (A10 : ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) 10 = w64 q)
  by (rewrite (ew_Ereg_nat (ms_regs ms) _ 10 10%bv eq_refl); exact R10).
assert (A14 : ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) 14 = w64 (3 * r + 2))
  by (rewrite (ew_Ereg_nat (ms_regs ms) _ 14 14%bv eq_refl); exact R14).
assert (A2 : ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) 2 = getr (ms_regs ms) 2)
  by (rewrite (ew_Ereg_nat (ms_regs ms) _ 2 2%bv eq_refl); reflexivity).
lazymatch type of HS with st_ok _ ?EE _ _ =>
  assert (U14F : U EE (SOff 14 3) = 3 * r + 5)
    by (replace (3 * r + 5) with (3 * r + 2 + 3) by lia;
        apply (U_atom_off _ 14 (3 * r + 2) 3);
        [repeat (rewrite ew_ewset_other by lia); exact A14 | lia | lia]);
  assert (U8F : U EE (SOff 8 0) = len)
    by (apply (U_atom _ 8 len); [repeat (rewrite ew_ewset_other by lia); exact A8 | lia])
end.
eapply SRr_sym_branch with (c := BC_LTU) (a := SOff 14 3) (b := SOff 8 0);
  [exact HS | intros Hbr HSb | intros Hbr HSb];
  rewrite branch_ltu_U, U14F, U8F in Hbr.
- (* the loop goes round again *)
  apply Z.ltb_lt in Hbr.
  clear HS. rename HSb into HS.
  (* the last instructions of the round store nothing: drop the three regions, so the run keeps every byte *)
  do 3 (let H' := fresh "HSd" in
        pose proof ((fun Hm => enc_drop_head _ _ _ _ _ Hm HS) ltac:(vm_compute; reflexivity)) as H';
        clear HS; rename H' into HS).
  fsw_aj_run_toU fsw_wr_tbl_ok HS HJ HARU 0x843fc.
  all: first
    [ solve [apply awr_ok_nil]
    | solve [ cbn [add_cond enc_seat enc_round_ss add_atom ss_mem];
              repeat (apply awr_ok_cons_ro; [cbn; lia|]);
              eapply awr_ok_cons_gen with (k := 17%nat) (b := q + 4 * r);
              [ reflexivity | exact E17F
              | cbn [enc_rout YP09.r_wlo YP09.r_whi]; intros a Ha; left; right; right; left;
                exists (q - HEAD), (enc_size len + HEAD); split; [exact HQB|];
                split; [exact encR_new_block|];
                unfold req_size; destruct (enc_size len + HEAD =? 0) eqn:EQ;
                [apply Z.eqb_eq in EQ; unfold HEAD in *; lia | unfold HEAD, enc_size in *; lia]
              | apply awr_ok_nil ] ]
    | idtac ].
  apply (KNEXT ms5 _ ltac:(lia)).
  + split; [|split].
    * unfold encR_J. exact HJ.
    * exact HARU.
    * intros x Hx.
      rewrite (enc_frame_X _ _ (ms_mem ms4) (ms_mem ms5) encR_out HF4); [exact (HA4 x Hx) | | exact Hx].
      intros a (rg & Hrin & _).
      lazymatch type of Hrin with In _ ?L => let L' := eval vm_compute in L in
        change L with L' in Hrin end.
      destruct Hrin.
  + split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
    * exact (enc_reg_val0 _ _ _ _ 8%bv 8 len HS ltac:(vm_compute; reflexivity)
               ltac:(repeat (rewrite ew_ewset_other by lia); rewrite A8; apply unsigned_lit_small; lia)
               ltac:(lia)).
    * exact (enc_reg_val0 _ _ _ _ 9%bv 9 data HS ltac:(vm_compute; reflexivity)
               ltac:(repeat (rewrite ew_ewset_other by lia); rewrite A9; apply unsigned_lit_small; lia)
               ltac:(lia)).
    * exact (enc_reg_val0 _ _ _ _ 10%bv 10 q HS ltac:(vm_compute; reflexivity)
               ltac:(repeat (rewrite ew_ewset_other by lia); rewrite A10; apply unsigned_lit_small;
                     unfold enc_size in *; lia) ltac:(unfold enc_size in *; lia)).
    * replace (q + 4 * (r + 1)) with (q + 4 * r + 4) by lia.
      exact (enc_reg_val _ _ _ _ 11%bv 11 4 (q + 4 * r) HS ltac:(vm_compute; reflexivity)
               ltac:(repeat (rewrite ew_ewset_other by lia); rewrite A11; apply unsigned_lit_small;
                     unfold enc_size in *; lia) ltac:(unfold enc_size in *; lia)).
    * rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) _ _ ms5 12%bv HS).
      lazymatch goal with |- sv_denot _ ?t = _ => let t' := eval vm_compute in t in change t with t' end.
      apply enc_denot_of_U.
      rewrite (enc_U_add2 _ 9 14 3 0 data (3 * r + 2));
        first [ solve [repeat (rewrite ew_ewset_other by lia); exact A9]
              | solve [repeat (rewrite ew_ewset_other by lia); exact A14]
              | solve [lia] ].
    * replace (3 * (r + 1) + 2) with (3 * r + 2 + 3) by lia.
      exact (enc_reg_val _ _ _ _ 14%bv 14 3 (3 * r + 2) HS ltac:(vm_compute; reflexivity)
               ltac:(repeat (rewrite ew_ewset_other by lia); rewrite A14; apply unsigned_lit_small; lia)
               ltac:(lia)).
    * exact (enc_reg_val0 _ _ _ _ 15%bv 15 G_B64 HS ltac:(vm_compute; reflexivity)
               ltac:(repeat (rewrite ew_ewset_other by lia); rewrite A15; apply unsigned_lit_small;
                     unfold G_B64; lia) ltac:(unfold G_B64; lia)).
    * replace (q + 4 * (r + 1)) with (q + 4 * r + 4) by lia.
      exact (enc_reg_val _ _ _ _ 17%bv 17 4 (q + 4 * r) HS ltac:(vm_compute; reflexivity)
               ltac:(repeat (rewrite ew_ewset_other by lia); exact E17u) ltac:(unfold enc_size in *; lia)).
    * exact (enc_reg_val0 _ _ _ _ 18%bv 18 SHADOW_OFF HS ltac:(vm_compute; reflexivity)
               ltac:(repeat (rewrite ew_ewset_other by lia); rewrite A18; apply unsigned_lit_small;
                     unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia)).
    * unfold spZ. rewrite (enc_reg_val0 _ _ _ _ 2%bv 2 (spZ (ms_regs ms)) HS
        ltac:(vm_compute; reflexivity)
        ltac:(repeat (rewrite ew_ewset_other by lia); rewrite A2; reflexivity)
        ltac:(unfold spZ; pose proof (u64_range (getr (ms_regs ms) 2)); lia)).
      unfold w64. rewrite Z_to_bv_unsigned, bv_wrap_small;
        [exact Rsp | change (bv_modulus 64) with (2 ^ 64); unfold spZ;
         pose proof (u64_range (getr (ms_regs ms) 2)); lia].
    * assert (KEPT11 : forall rr : bv 5, In rr [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
        getr (ms_regs ms5) rr = getr (ms_regs ms) rr).
      { intros rr Hin. cbn [In] in Hin.
        repeat (destruct Hin as [<-|Hin]); [..|destruct Hin];
          (apply (encR_kept_reg _ _ ms5 (ms_regs ms) _ HS);
           [ vm_compute; reflexivity
           | lazymatch goal with |- ew _ (Z.to_nat (bv_unsigned ?R)) = _ =>
               let k := eval vm_compute in (Z.to_nat (bv_unsigned R)) in
               change (Z.to_nat (bv_unsigned R)) with k end;
             repeat (rewrite ew_ewset_other by lia);
             apply (ew_Ereg_nat (ms_regs ms) (encR_extra3 b0 b1 b2)); reflexivity ]). }
      intros z Hz H2 H8 H9 H18.
      pose proof (Rk z Hz H2 H8 H9 H18) as RkZ. rewrite <- RkZ. apply KEPT11.
      assert (Hc : z = 3 \/ z = 4 \/ z = 19 \/ z = 20 \/ z = 21 \/ z = 22 \/ z = 23 \/ z = 24 \/
                   z = 25 \/ z = 26 \/ z = 27) by (unfold acallee_saved in Hz; lia).
      repeat (destruct Hc as [Hc|Hc]); rewrite Hc; cbn [In];
        repeat first [ solve [left; apply bv_eq; vm_compute; reflexivity] | right ].
  + exact (st_ok_restrict_mkst tfibsegs (w_H Wc) _ _ ms5 HS ltac:(vm_compute; reflexivity)).
  + assert (KEEP5 : forall a, 0 <= a < 2 ^ 64 -> ~ False ->
      mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms5)) a = mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms4)) a).
    { intros a Ha _. unfold mbyte. rewrite (HFr4 (Z_to_bv 64 a)); [reflexivity|].
      intros (rg & Hrin & _).
      lazymatch type of Hrin with In _ ?L => let L' := eval vm_compute in L in
        change L with L' in Hrin end.
      destruct Hrin. }
    assert (HL5 : Z.of_nat (length (WriterSpec.b64_enc (firstn (Z.to_nat (3 * (r + 1))) bs))) = 4 * r + 4)
      by (rewrite HMODEL, length_app; cbn [length]; rewrite Nat2Z.inj_add, HLEN4; lia).
    apply (encR_garr8_keep _ _ q _ (fun _ => False) KEEP5);
      [ lia | rewrite HL5; unfold enc_size in *; lia | intros i _ F; exact F | exact HPRE' ].
- (* the loop is done *)
  apply Z.ltb_ge in Hbr.
  clear HS. rename HSb into HS.
  (* the last instructions of the round store nothing: drop the three regions, so the run keeps every byte *)
  do 3 (let H' := fresh "HSd" in
        pose proof ((fun Hm => enc_drop_head _ _ _ _ _ Hm HS) ltac:(vm_compute; reflexivity)) as H';
        clear HS; rename H' into HS).
  fsw_aj_run_toU fsw_wr_tbl_ok HS HJ HARU 0x845dc.
  all: first
    [ solve [apply awr_ok_nil]
    | solve [ cbn [add_cond enc_seat enc_round_ss add_atom ss_mem];
              repeat (apply awr_ok_cons_ro; [cbn; lia|]);
              eapply awr_ok_cons_gen with (k := 17%nat) (b := q + 4 * r);
              [ reflexivity | exact E17F
              | cbn [enc_rout YP09.r_wlo YP09.r_whi]; intros a Ha; left; right; right; left;
                exists (q - HEAD), (enc_size len + HEAD); split; [exact HQB|];
                split; [exact encR_new_block|];
                unfold req_size; destruct (enc_size len + HEAD =? 0) eqn:EQ;
                [apply Z.eqb_eq in EQ; unfold HEAD in *; lia | unfold HEAD, enc_size in *; lia]
              | apply awr_ok_nil ] ]
    | idtac ].
  apply (KEXIT ms5 _ ltac:(lia)).
  + split; [|split].
    * unfold encR_J. exact HJ.
    * exact HARU.
    * intros x Hx.
      rewrite (enc_frame_X _ _ (ms_mem ms4) (ms_mem ms5) encR_out HF4); [exact (HA4 x Hx) | | exact Hx].
      intros a (rg & Hrin & _).
      lazymatch type of Hrin with In _ ?L => let L' := eval vm_compute in L in
        change L with L' in Hrin end.
      destruct Hrin.
  + split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
    * exact (enc_reg_val0 _ _ _ _ 8%bv 8 len HS ltac:(vm_compute; reflexivity)
               ltac:(repeat (rewrite ew_ewset_other by lia); rewrite A8; apply unsigned_lit_small; lia)
               ltac:(lia)).
    * exact (enc_reg_val0 _ _ _ _ 9%bv 9 data HS ltac:(vm_compute; reflexivity)
               ltac:(repeat (rewrite ew_ewset_other by lia); rewrite A9; apply unsigned_lit_small; lia)
               ltac:(lia)).
    * exact (enc_reg_val0 _ _ _ _ 10%bv 10 q HS ltac:(vm_compute; reflexivity)
               ltac:(repeat (rewrite ew_ewset_other by lia); rewrite A10; apply unsigned_lit_small;
                     unfold enc_size in *; lia) ltac:(unfold enc_size in *; lia)).
    * replace (q + 4 * (r + 1)) with (q + 4 * r + 4) by lia.
      exact (enc_reg_val _ _ _ _ 11%bv 17 4 (q + 4 * r) HS ltac:(vm_compute; reflexivity)
               ltac:(repeat (rewrite ew_ewset_other by lia); exact E17u) ltac:(unfold enc_size in *; lia)).
    * replace (3 * (r + 1)) with (3 * r + 2 + 1) by lia.
      exact (enc_reg_val _ _ _ _ 14%bv 14 1 (3 * r + 2) HS ltac:(vm_compute; reflexivity)
               ltac:(repeat (rewrite ew_ewset_other by lia); rewrite A14; apply unsigned_lit_small; lia)
               ltac:(lia)).
    * exact (enc_reg_val0 _ _ _ _ 18%bv 18 SHADOW_OFF HS ltac:(vm_compute; reflexivity)
               ltac:(repeat (rewrite ew_ewset_other by lia); rewrite A18; apply unsigned_lit_small;
                     unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia)).
    * unfold spZ. rewrite (enc_reg_val0 _ _ _ _ 2%bv 2 (spZ (ms_regs ms)) HS
        ltac:(vm_compute; reflexivity)
        ltac:(repeat (rewrite ew_ewset_other by lia); rewrite A2; reflexivity)
        ltac:(unfold spZ; pose proof (u64_range (getr (ms_regs ms) 2)); lia)).
      unfold w64. rewrite Z_to_bv_unsigned, bv_wrap_small;
        [exact Rsp | change (bv_modulus 64) with (2 ^ 64); unfold spZ;
         pose proof (u64_range (getr (ms_regs ms) 2)); lia].
    * assert (KEPT11 : forall rr : bv 5, In rr [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
        getr (ms_regs ms5) rr = getr (ms_regs ms) rr).
      { intros rr Hin. cbn [In] in Hin.
        repeat (destruct Hin as [<-|Hin]); [..|destruct Hin];
          (apply (encR_kept_reg _ _ ms5 (ms_regs ms) _ HS);
           [ vm_compute; reflexivity
           | lazymatch goal with |- ew _ (Z.to_nat (bv_unsigned ?R)) = _ =>
               let k := eval vm_compute in (Z.to_nat (bv_unsigned R)) in
               change (Z.to_nat (bv_unsigned R)) with k end;
             repeat (rewrite ew_ewset_other by lia);
             apply (ew_Ereg_nat (ms_regs ms) (encR_extra3 b0 b1 b2)); reflexivity ]). }
      intros z Hz H2 H8 H9 H18.
      pose proof (Rk z Hz H2 H8 H9 H18) as RkZ. rewrite <- RkZ. apply KEPT11.
      assert (Hc : z = 3 \/ z = 4 \/ z = 19 \/ z = 20 \/ z = 21 \/ z = 22 \/ z = 23 \/ z = 24 \/
                   z = 25 \/ z = 26 \/ z = 27) by (unfold acallee_saved in Hz; lia).
      repeat (destruct Hc as [Hc|Hc]); rewrite Hc; cbn [In];
        repeat first [ solve [left; apply bv_eq; vm_compute; reflexivity] | right ].
  + exact (st_ok_restrict_mkst tfibsegs (w_H Wc) _ _ ms5 HS ltac:(vm_compute; reflexivity)).
  + assert (KEEP5 : forall a, 0 <= a < 2 ^ 64 -> ~ False ->
      mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms5)) a = mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms4)) a).
    { intros a Ha _. unfold mbyte. rewrite (HFr4 (Z_to_bv 64 a)); [reflexivity|].
      intros (rg & Hrin & _).
      lazymatch type of Hrin with In _ ?L => let L' := eval vm_compute in L in
        change L with L' in Hrin end.
      destruct Hrin. }
    assert (HL5 : Z.of_nat (length (WriterSpec.b64_enc (firstn (Z.to_nat (3 * (r + 1))) bs))) = 4 * r + 4)
      by (rewrite HMODEL, length_app; cbn [length]; rewrite Nat2Z.inj_add, HLEN4; lia).
    apply (encR_garr8_keep _ _ q _ (fun _ => False) KEEP5);
      [ lia | rewrite HL5; unfold enc_size in *; lia | intros i _ F; exact F | exact HPRE' ].
Qed.

(* ==== BEGIN EncLoop (a Theorem Labs lane) ==== *)
(* ---- the 3-byte loop, all its rounds: from the head of round r (0x843fc), with the first r output quads
   written, each round is one encR_round_step (KNEXT is the head of round r + 1, KEXIT the loop's exit at
   0x845dc after R = r + 1 rounds, where 3R <= len <= 3R + 2), by induction on len - 3r. RS is
   encR_round_step's statement, held as a hypothesis until the round step closes. ---- *)
Section EncLoop.
Hypothesis RS : forall ms md r b0 b1 b2 (Q : world tfibsegs -> config -> Prop),
  0 <= r -> 3 * r + 3 <= len ->
  encR_inv (ms_mem ms) md -> encR_loop_regs ms r ->
  garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) q
    (WriterSpec.b64_enc (firstn (Z.to_nat (3 * r)) bs)) ->
  nth (Z.to_nat (3 * r)) bs 0 = b0 -> nth (Z.to_nat (3 * r + 1)) bs 0 = b1 ->
  nth (Z.to_nat (3 * r + 2)) bs 0 = b2 ->
  (forall ms' md', 3 * (r + 1) + 3 <= len -> encR_inv (ms_mem ms') md' -> encR_loop_regs ms' (r + 1) ->
     ms' = mkst (ms_regs ms') (w64 0x843fc) (ms_mem ms') (seg_rom tfibsegs) ->
     garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms')) q
       (WriterSpec.b64_enc (firstn (Z.to_nat (3 * (r + 1))) bs)) ->
     SRr tfibsegs Wc (mkCfg ms' md') Q) ->
  (forall ms' md', len <= 3 * (r + 1) + 2 -> encR_inv (ms_mem ms') md' -> encR_exit_regs ms' (r + 1) ->
     ms' = mkst (ms_regs ms') (w64 0x845dc) (ms_mem ms') (seg_rom tfibsegs) ->
     garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms')) q
       (WriterSpec.b64_enc (firstn (Z.to_nat (3 * (r + 1))) bs)) ->
     SRr tfibsegs Wc (mkCfg ms' md') Q) ->
  SRr tfibsegs Wc (mkCfg (mkst (ms_regs ms) (w64 0x843fc) (ms_mem ms) (seg_rom tfibsegs)) md) Q.

Lemma encR_loop : forall ms md r (Q : world tfibsegs -> config -> Prop),
  0 <= r -> 3 * r + 3 <= len ->
  encR_inv (ms_mem ms) md -> encR_loop_regs ms r ->
  garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) q
    (WriterSpec.b64_enc (firstn (Z.to_nat (3 * r)) bs)) ->
  (forall ms' md' R, len <= 3 * R + 2 -> 3 * R <= len ->
     encR_inv (ms_mem ms') md' -> encR_exit_regs ms' R ->
     ms' = mkst (ms_regs ms') (w64 0x845dc) (ms_mem ms') (seg_rom tfibsegs) ->
     garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms')) q
       (WriterSpec.b64_enc (firstn (Z.to_nat (3 * R)) bs)) ->
     SRr tfibsegs Wc (mkCfg ms' md') Q) ->
  SRr tfibsegs Wc (mkCfg (mkst (ms_regs ms) (w64 0x843fc) (ms_mem ms) (seg_rom tfibsegs)) md) Q.
Proof.
intros ms md r Q Hr Hr3.
assert (Hn : exists n, (Z.to_nat (len - 3 * r) <= n)%nat) by (exists (Z.to_nat (len - 3 * r)); lia).
destruct Hn as (n & Hn). revert ms md r Hr Hr3 Hn.
induction n as [|n IH]; intros ms md r Hr Hr3 Hn HINV HR HPRE KEXIT; [lia|].
apply (RS ms md r (nth (Z.to_nat (3 * r)) bs 0) (nth (Z.to_nat (3 * r + 1)) bs 0)
  (nth (Z.to_nat (3 * r + 2)) bs 0) Q Hr Hr3 HINV HR HPRE eq_refl eq_refl eq_refl).
- intros ms' md' Hr3' HINV' HR' HPC HPRE'. rewrite HPC.
  exact (IH ms' md' (r + 1) ltac:(lia) Hr3' ltac:(lia) HINV' HR' HPRE' KEXIT).
- intros ms' md' Hx HINV' HX HPC HPRE'.
  exact (KEXIT ms' md' (r + 1) Hx ltac:(lia) HINV' HX HPC HPRE').
Qed.
End EncLoop.
(* ==== END EncLoop (a Theorem Labs lane) ==== *)

(* the loop with its round step discharged *)
Definition encR_loop_closed := encR_loop encR_round_step.

(* ==== BEGIN the exit block (a Theorem Labs lane) ==== *)
(* ---- the loop's exit branch, 0x845dc  bgeu a4, s0, +0x124  (a4 = 3R, s0 = len; (internal path):149).
   encR_loop's KEXIT hands over here with 3R <= len <= 3R + 2, so the branch is TAKEN exactly when len = 3R
   (no leftover byte: straight to 0x84700, encR_nul, where firstn (3R) bs = bs and q + 4R = q + 4 * ((len + 2) / 3))
   and FALLS THROUGH to 0x845e0 (encR_tail) when 3R < len. The branch is a condition of the symbolic state, so the
   engine decides it in one step; that step reads and writes nothing, so the invariant, the output bytes and every
   register cross it unchanged.
   encR_loop_exit IS encR_loop's KEXIT at Q := encR_nul's / encR_tail's fpostU: the same binders in the same order
   (ms md R, len <= 3 * R + 2, 3 * R <= len, encR_inv, encR_exit_regs, the pc, garr8), so it is passed as KEXIT
   with no glue. 0 <= R is not a hypothesis: it follows from len <= 3 * R + 2 and HLN's 0 <= len. ---- *)
Definition encX_ssE : sstate :=
  mkSS 0x845dc sr_atoms [] None (mkFacts [] [mkAC BC_GEU (SOff 14 0) (SOff 8 0)] []).
Definition encX_ssT : sstate :=
  mkSS 0x845dc sr_atoms [] None (mkFacts [] [mkAC BC_LTU (SOff 14 0) (SOff 8 0)] []).
(* taken: 0x845dc -> 0x84700; not taken: 0x845dc -> 0x845e0 *)
Definition encX_runE : sstate * run_status :=
  Eval vm_compute in sym_run_toN tfibsegs fsw_wr_tbl FUEL 0x84700 encX_ssE.
Definition encX_runT : sstate * run_status :=
  Eval vm_compute in sym_run_toN tfibsegs fsw_wr_tbl FUEL 0x845e0 encX_ssT.

(* the state at 0x845dc: every register its own atom, no region, and the branch's outcome as the one condition *)
Lemma encX_state : forall (c : branch_cond) ms R,
  encR_exit_regs ms R -> branch_taken c (w64 (3 * R)) (w64 len) = true ->
  st_ok tfibsegs (Ereg (ms_regs ms) [])
    (mkSS 0x845dc sr_atoms [] None (mkFacts [] [mkAC c (SOff 14 0) (SOff 8 0)] []))
    (restrict (w_H Wc) (mkst (ms_regs ms) (w64 0x845dc) (ms_mem ms) (seg_rom tfibsegs))).
Proof.
intros c ms R HX Hbr.
pose proof HX as (X8 & X9 & X10 & X11 & X14 & X18 & Xsp & Xk).
rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs).
- apply regs_ok_Ereg.
- reflexivity.
- constructor.
- exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [exact I|]. split; [|exact I]. split; [|exact I].
  unfold acond_ok. cbn [ac_c ac_a ac_b].
  rewrite !fsw_SOff0, (ew_Ereg_nat (ms_regs ms) [] 14 14%bv eq_refl),
    (ew_Ereg_nat (ms_regs ms) [] 8 8%bv eq_refl), X14, X8.
  exact Hbr.
Qed.

(* ONE plain run of the exit (no region, so no write and no shadow check): the invariant and the memory cross it *)
Lemma encX_step : forall (E : env) (ss ss' : sstate) (stop : Z) (ms : machine_state) (md : Model)
    (Q : world tfibsegs -> config -> Prop),
  st_ok tfibsegs E ss (restrict (w_H Wc) ms) ->
  encR_inv (ms_mem ms) md ->
  ss_mem ss = [] ->
  sym_run_toN tfibsegs fsw_wr_tbl FUEL stop ss = (ss', RS_running) ->
  (forall (ms' : machine_state) (md' : Model),
     st_ok tfibsegs E ss' (restrict (w_H Wc) ms') ->
     encR_inv (ms_mem ms') md' ->
     (forall x : word, ms_mem ms' x = ms_mem ms x) ->
     SRr tfibsegs Wc (mkCfg ms' md') Q) ->
  SRr tfibsegs Wc (mkCfg ms md) Q.
Proof.
intros E ss ss' stop ms md Q HS HINV Hmem Hrun HK.
pose proof HINV as (HJ & HARU & HA). unfold encR_J in HJ.
eapply (@fsw_run_to_AJU _ rc SK _ fsw_wr_tbl fsw_wr_tbl_ok Wc FUEL stop E ss ss' RS_running ms
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS Hrun I HARU HJ).
- rewrite Hmem. apply awr_ok_nil.
- intros ms' mat' HS' HJ' HARU' HF HFr HG.
  assert (MEQ : forall x : word, ms_mem ms' x = ms_mem ms x).
  { intros x. apply HF. rewrite Hmem. intros (rg & Hin & _). destruct Hin. }
  apply (HK ms' _ HS').
  + unfold encR_inv. split; [exact HJ'|]. split; [exact HARU'|].
    intros x Hx. rewrite MEQ. exact (HA x Hx).
  + exact MEQ.
Qed.

(* the output bytes cross a step that leaves the memory as it was *)
Lemma encX_garr8 : forall (m m' : word -> option byte) (l : list Z),
  (forall x : word, m' x = m x) -> q + Z.of_nat (length l) <= 2 ^ 64 ->
  garr8 tfibsegs (mrestrict (w_H Wc) m) q l -> garr8 tfibsegs (mrestrict (w_H Wc) m') q l.
Proof.
intros m m' l MEQ Hl HP.
assert (HQlo : 4112 <= q) by (unfold HEAD in *; lia).
apply (encR_garr8_keep (mrestrict (w_H Wc) m) (mrestrict (w_H Wc) m') q l (fun _ => False));
  [ intros a _ _; unfold mbyte, mrestrict; rewrite MEQ; reflexivity | lia | exact Hl
  | intros i _ Hf; exact Hf | exact HP ].
Qed.

Lemma encR_loop_exit : forall ms md R,
  len <= 3 * R + 2 -> 3 * R <= len ->
  encR_inv (ms_mem ms) md -> encR_exit_regs ms R ->
  ms = mkst (ms_regs ms) (w64 0x845dc) (ms_mem ms) (seg_rom tfibsegs) ->
  garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) q
    (WriterSpec.b64_enc (firstn (Z.to_nat (3 * R)) bs)) ->
  SRr tfibsegs Wc (mkCfg ms md)
    (fpostU tfibsegs B STK_preset_base64_encode (spZ regs0) FS_PSTAT_FP regs0 ly0 St0 U0 W0 mem0 md0
       EV_preset_base64_encode (U0 ++ [(q - HEAD, HEAD)]) encR_Q).
Proof.
intros ms md R H2 H1 HINV HX Hms HPRE.
pose proof HLN as HLN'. pose proof HBSL as HBSL'.
assert (HR : 0 <= R) by lia.
pose proof encR_size_pos as HM. pose proof alloc_ceiling_val as (CR & _).
pose proof encR_out_facts as (_ & HQceil & _).
pose proof HX as (X8 & X9 & X10 & X11 & X14 & X18 & Xsp & Xk).
assert (Hc : len = 3 * R \/ 3 * R + 1 <= len) by lia. destruct Hc as [He|He].
- (* no leftover byte: the branch is taken, 0x84700 *)
  assert (HBR : branch_taken BC_GEU (w64 (3 * R)) (w64 len) = true).
  { cbn [branch_taken]. unfold bv_ltu, w64.
    rewrite !unsigned_lit_small by lia. apply negb_true_iff. apply Z.ltb_ge. lia. }
  pose proof (encX_state BC_GEU ms R HX HBR) as HS0. rewrite <- Hms in HS0.
  apply (encX_step _ encX_ssE (fst encX_runE) 0x84700 ms md _ HS0 HINV eq_refl
    ltac:(vm_compute; reflexivity)).
  intros ms' md' HS' HINV' MEQ.
  assert (RG : forall (rr : bv 5) (n : nat), sr_get (ss_regs (fst encX_runE)) rr = SOff n 0 ->
    Z.of_nat n = bv_unsigned rr -> getr (ms_regs ms') rr = getr (ms_regs ms) rr)
    by (intros rr n Hsr Hn; exact (fsw_reg_atom (w_H Wc) (ms_regs ms) [] _ ms' rr rr n HS' Hsr Hn)).
  assert (HQe : (len + 2) / 3 = R).
  { rewrite He. replace (3 * R + 2) with (R * 3 + 2) by lia.
    rewrite (Z.div_add_l R 3 2 ltac:(lia)). replace (2 / 3) with 0 by reflexivity. lia. }
  assert (HFB : firstn (Z.to_nat (3 * R)) bs = bs) by (apply firstn_all2; lia).
  rewrite HFB in HPRE.
  pose proof (b64_enc_len bs) as HBL. rewrite HBSL in HBL.
  apply (encR_nul ms' md' HINV'
    (encX_garr8 (ms_mem ms) (ms_mem ms') _ MEQ ltac:(rewrite HBL; unfold enc_size in *; lia) HPRE)).
  + exact (st_ok_restrict_mkst tfibsegs (w_H Wc) _ _ ms' HS' ltac:(vm_compute; reflexivity)).
  + rewrite (RG 10%bv 10%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)). exact X10.
  + rewrite (RG 11%bv 11%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)), HQe. exact X11.
  + rewrite (RG 18%bv 18%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)). exact X18.
  + unfold spZ. rewrite (RG 2%bv 2%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)).
    exact Xsp.
  + intros z Hz Hz2 Hz8 Hz9 Hz18.
    rewrite (encT_kept_reg (Ereg (ms_regs ms) []) (fst encX_runE) ms' ms [] HS'
      (YP06.env_agree_refl 39 _) ltac:(vm_compute; reflexivity) z (encT_kept_in z Hz Hz2 Hz8 Hz9 Hz18)).
    exact (Xk z Hz Hz2 Hz8 Hz9 Hz18).
- (* one or two leftover bytes: the branch falls through, 0x845e0 *)
  assert (HBR : branch_taken BC_LTU (w64 (3 * R)) (w64 len) = true).
  { cbn [branch_taken]. unfold bv_ltu, w64.
    rewrite !unsigned_lit_small by lia. apply Z.ltb_lt. lia. }
  pose proof (encX_state BC_LTU ms R HX HBR) as HS0. rewrite <- Hms in HS0.
  apply (encX_step _ encX_ssT (fst encX_runT) 0x845e0 ms md _ HS0 HINV eq_refl
    ltac:(vm_compute; reflexivity)).
  intros ms' md' HS' HINV' MEQ.
  assert (RG : forall (rr : bv 5) (n : nat), sr_get (ss_regs (fst encX_runT)) rr = SOff n 0 ->
    Z.of_nat n = bv_unsigned rr -> getr (ms_regs ms') rr = getr (ms_regs ms) rr)
    by (intros rr n Hsr Hn; exact (fsw_reg_atom (w_H Wc) (ms_regs ms) [] _ ms' rr rr n HS' Hsr Hn)).
  pose proof (encT_qR R HR ltac:(lia)) as HQ.
  destruct (encT_model R HR ltac:(lia)) as (_ & HL4).
  apply (encR_tail ms' md' R HINV').
  + split; [rewrite (RG 8%bv 8%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)); exact X8|].
    split; [rewrite (RG 9%bv 9%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)); exact X9|].
    split; [rewrite (RG 10%bv 10%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)); exact X10|].
    split; [rewrite (RG 11%bv 11%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)); exact X11|].
    split; [rewrite (RG 14%bv 14%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)); exact X14|].
    split; [rewrite (RG 18%bv 18%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)); exact X18|].
    split; [unfold spZ; rewrite (RG 2%bv 2%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity));
            exact Xsp|].
    intros z Hz Hz2 Hz8 Hz9 Hz18.
    rewrite (encT_kept_reg (Ereg (ms_regs ms) []) (fst encX_runT) ms' ms [] HS'
      (YP06.env_agree_refl 39 _) ltac:(vm_compute; reflexivity) z (encT_kept_in z Hz Hz2 Hz8 Hz9 Hz18)).
    exact (Xk z Hz Hz2 Hz8 Hz9 Hz18).
  + exact (st_ok_restrict_mkst tfibsegs (w_H Wc) _ _ ms' HS' ltac:(vm_compute; reflexivity)).
  + exact (encX_garr8 (ms_mem ms) (ms_mem ms') _ MEQ ltac:(rewrite HL4; unfold enc_size in *; lia) HPRE).
  + exact HR.
  + lia.
Qed.
(* ==== END the exit block ==== *)
End R.

(* ==== BEGIN the entry block (a Theorem Labs lane) ==== *)
(* preset_base64_encode's ENTRY: 0x84390 .. 0x843d4 (the 32-byte frame, the four saved registers, the size
   arithmetic through the .rodata word 0x10320 = ENC_MAGIC_A), the `jal fuzz_malloc` (0x828ac) discharged by
   fuzz_malloc_spec, the refused arm (0x843d8 beqz a0 -> 0x84714 .. ret) and the three exits of the dispatch:
   0x84700 (len = 0, through encR_nul), 0x845e0 (0 < len < 3, the TAIL's boundary form at R = 0) and 0x843fc
   (3 <= len, the loop head at r = 0).  Every Section R hypothesis is discharged here at the call's post
   (lyc Sc Wc memc mdc q live peak cnt fail = fuzz_malloc_spec's success post, ly0 St0 U0 W0 mem0 md0 regs0 =
   the entry), and handed on as encR_hyps.
   A Theorem Labs lane, split off another Theorem Labs lane by agreement 2026-10-29T09:06Z: the other lane keeps
   encR_round_step, the LOOP induction, the TAIL (encR_tail) and encode_proof, and applies encR_entry.
   The callee contract (lib/A/FSH_Fn_alloc.v fuzz_malloc_spec, FROZEN) is a Section hypothesis, as
   lib/A/FSW_dec_E.v:1081 takes it for preset_base64_decode's entry - the TEMPLATE for an entry + fuzz_malloc
   call in this kit. *)
Hypothesis HMALLOC : fuzz_malloc_spec tfibsegs B.

(* ---------------------------------------------------------------------------------------------------------- *)
(* 9. the allocator statics and the read-only view across the call                                              *)
(* ---------------------------------------------------------------------------------------------------------- *)

(* fs's four alloc.c statics (FS_PSTAT_FP) are image bytes *)
Lemma encE_pstat_img : forall a, inFP FS_PSTAT_FP a -> in_img tfibsegs a.
Proof.
intros a (r & Hr & Ha).
assert (Hb : forallb (fun r : Z * Z => existsb (fun s => (Z.of_N (seg_base s) <=? fst r) &&
  (snd r <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs) FS_PSTAT_FP = true)
  by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) Hb r Hr) as H. apply existsb_exists in H as (s & Hs & Hss).
apply andb_prop in Hss as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists s. split; [exact Hs | lia].
Qed.

(* fs's read-only bytes are image bytes (the port of FSW_rd.v fsw_roP_img, which this file does not import) *)
Lemma encE_roP_img : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> in_img tfibsegs a.
Proof.
intros a [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr]|].
assert (Hb : existsb (fun s => (Z.of_N (seg_base s) <=? FS_RLO) &&
  (FS_RHI <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs = true) by (vm_compute; reflexivity).
apply existsb_exists in Hb as (s & Hs & Hss). apply andb_prop in Hss as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. exists s. split; [exact Hs | lia].
Qed.

(* the four statics are writable and outside [FS_RLO, FS_RHI): no read-only byte is one of them *)
Lemma encE_ro_not_pstat : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> ~ inFP FS_PSTAT_FP a.
Proof.
intros a Hro (r & Hr & Ha).
assert (Hb : forallb (fun r : Z * Z => forallb (fun s => seg_writable s ||
  (snd r <=? Z.of_N (seg_base s)) || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? fst r)) tfibsegs)
  FS_PSTAT_FP = true) by (vm_compute; reflexivity).
assert (Hlo : forallb (fun r : Z * Z => (FS_RHI <=? fst r) || (snd r <=? FS_RLO)) FS_PSTAT_FP = true)
  by (vm_compute; reflexivity).
destruct Hro as [(s & Hs & Hw & Hseg) | Hr2].
- pose proof (proj1 (forallb_forall _ _) Hb r Hr) as H1. cbn beta in H1.
  pose proof (proj1 (forallb_forall _ _) H1 s Hs) as H2. cbn beta in H2.
  rewrite Hw in H2. cbn [orb] in H2.
  apply orb_prop in H2 as [H | H]; apply Z.leb_le in H; lia.
- pose proof (proj1 (forallb_forall _ _) Hlo r Hr) as H1. cbn beta in H1.
  apply orb_prop in H1 as [H | H]; apply Z.leb_le in H; lia.
Qed.

Lemma encE_pstat_closed : ~ YI16.sink_open_fp FS_PSTAT_FP.
Proof.
apply sink_closed_pos. unfold FS_PSTAT_FP. repeat (apply Forall_cons; [cbn [fst]; lia|]). apply Forall_nil.
Qed.

(* the read-only view carries from the raw memory to the allocator's (an image byte is below the shadow band) *)
Lemma encE_aro_unp : forall ly S U (W : world tfibsegs) mem md,
  ARU tfibsegs B ly S U W mem md ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) mem) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) (unpoison U mem)).
Proof.
intros ly S U W mem md HARU HR a Hro Hno Her.
pose proof (fs_segs_img a (encE_roP_img a Hro)) as Hb.
rewrite (aview_at tfibsegs (w_H W) (unpoison U mem) mem a
  (enc_unp_apart ly S U W mem md a HARU ltac:(unfold FS_IMG_END in Hb; lia)
     ltac:(unfold FS_IMG_END, SHADOW_OFF, kHighMemBeg in *; lia))).
exact (HR a Hro Hno Her).
Qed.

(* the read-only view across a program call, at the two RAW memories (the port of FSW_rd.v arodata_kept_own) *)
Lemma encE_aro_call : forall STK1 sp1 lyc Sc Uc (W : world tfibsegs) memc mdc ly' S' U' W' mem' md' kc,
  ajournal tfibsegs B STK1 sp1 FS_PSTAT_FP lyc Sc W (unpoison Uc memc) mdc []
    ly' S' W' (unpoison U' mem') md' kc ->
  ARU tfibsegs B lyc Sc Uc W memc mdc ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) memc) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W') mem').
Proof.
intros STK1 sp1 lyc Sc Uc W memc mdc ly' S' U' W' mem' md' kc HJ HU HO' HP' HR a Ha Ho He.
pose proof HJ as (HAR' & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
assert (HU' : ARU tfibsegs B ly' S' U' W' mem' md')
  by (split; [exact HAR' | split; [exact HO' | exact HP']]).
pose proof (fs_segs_img a (encE_roP_img a Ha)) as Hl.
assert (NS : ~ (SHADOW_OFF <= a < kHighMemBeg)) by (unfold FS_IMG_END, SHADOW_OFF, kHighMemBeg in *; lia).
assert (A64 : 0 <= a < 2 ^ 64) by (unfold FS_IMG_END in Hl; lia).
rewrite <- (aview_at tfibsegs (w_H W') (unpoison U' mem') mem' a
  (enc_unp_apart ly' S' U' W' mem' md' a HU' A64 NS)).
rewrite (F3 a (encE_roP_img a Ha) Ho He (encE_ro_not_pstat a Ha)
  (fp_spares_closed FS_PSTAT_FP a encE_pstat_closed)).
rewrite (aview_at tfibsegs (w_H W) (unpoison Uc memc) memc a
  (enc_unp_apart lyc Sc Uc W memc mdc a HU A64 NS)).
exact (HR a Ha Ho He).
Qed.

(* a byte of a block the call keeps, on the two RAW memories (the journal's block clause, read through ARU) *)
Lemma encE_blk_keep : forall STK1 sp1 ly S U (W : world tfibsegs) memc mdc ly' S' U'
  (W' : world tfibsegs) mem' md' kc p n a,
  ajournal tfibsegs B STK1 sp1 FS_PSTAT_FP ly S W (unpoison U memc) mdc []
    ly' S' W' (unpoison U' mem') md' kc ->
  ARU tfibsegs B ly S U W memc mdc ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  In (p, n) (ablocks B ly S) -> In (p, n) (ablocks B ly' S') -> p <= a < p + req_size n ->
  mbyte tfibsegs (mrestrict (w_H W') mem') a = mbyte tfibsegs (mrestrict (w_H W) memc) a.
Proof.
intros STK1 sp1 ly S U W memc mdc ly' S' U' W' mem' md' kc p n a HJ HU OK' PO' Hin Hin' Ha.
pose proof HJ as (HAR' & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
assert (HU' : ARU tfibsegs B ly' S' U' W' mem' md')
  by (split; [exact HAR' | split; [exact OK' | exact PO']]).
pose proof (ARU_AR tfibsegs B ly S U W memc mdc HU) as HAR.
destruct (enc_blk_bounds ly S W (unpoison U memc) mdc p n a HAR Hin Ha) as (Hb1 & Hb2 & Hb3).
assert (A64 : 0 <= a < 2 ^ 64) by lia.
assert (NS : ~ (SHADOW_OFF <= a < kHighMemBeg)) by (unfold kHighMemBeg, SHADOW_OFF in *; lia).
apply (mbyte_of_aview tfibsegs).
rewrite <- (aview_at tfibsegs (w_H W') (unpoison U' mem') mem' a
  (enc_unp_apart ly' S' U' W' mem' md' a HU' A64 NS)).
rewrite <- (aview_at tfibsegs (w_H W) (unpoison U memc) memc a
  (enc_unp_apart ly S U W memc mdc a HU A64 NS)).
replace a with (p + (a - p)) by lia.
apply (F2 p n (a - p) Hin Hin'); [lia|].
replace (p + (a - p)) with a by lia.
intros Hf. exact (enc_blk_not_img ly S W (unpoison U memc) mdc p n a HAR Hin Ha (encE_pstat_img a Hf)).
Qed.

(* the callee's footprint is the caller's: FS_PSTAT_FP, whose bytes are image bytes *)
Lemma encE_fp_sub : forall ly S lyc Sc, fsw_fp_sub B ly S lyc Sc [] FS_PSTAT_FP FS_PSTAT_FP.
Proof.
intros ly S lyc Sc a Ha. right; right; left. split; [exact Ha | exact (encE_pstat_img a Ha)].
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* 10. the size the five instructions leave in a0, and the four saved words of the frame                        *)
(* ---------------------------------------------------------------------------------------------------------- *)

(* 0x843bc .. 0x843d0: addi a2,s0,2; mulhu a0,a2,a1; slli a0,a0,1; andi a0,a0,-4; addi a0,a0,1 (a1 = ENC_MAGIC) *)
Definition encE_size_sv : sv :=
  SAlu ALU_ADD (SAlu ALU_AND (SAlu ALU_SLL (SMd M_MULHU (SOff 11 2) (SLit ENC_MAGIC)) (SLit 1)) (SLit (-4)))
    (SLit 1).

Lemma encE_size_den : forall (E : env) (len : Z),
  ew E 11 = w64 len -> 0 <= len <= 2 ^ 27 -> sv_denot E encE_size_sv = w64 (enc_size len).
Proof.
intros E len H11 Hlen. unfold encE_size_sv, w64.
assert (HQ : 0 <= (len + 2) / 3 <= 2 ^ 27)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HQ2 : 0 <= 2 * (len + 2) / 3 <= 2 ^ 28)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HA2 : U E (SOff 11 2) = len + 2) by (apply (U_atom_off E 11 len 2 H11); lia).
assert (HMH : U E (SMd M_MULHU (SOff 11 2) (SLit ENC_MAGIC)) = 2 * (len + 2) / 3).
{ rewrite U_SMd. cbn [zmd_raw Z.of_N]. rewrite HA2, U_SLit.
  rewrite (zcanon_id ENC_MAGIC) by (unfold M64, ENC_MAGIC; lia).
  rewrite (enc_mulhu (len + 2) ltac:(lia)). apply zcanon_id. unfold M64. lia. }
assert (HSL : U E (SAlu ALU_SLL (SMd M_MULHU (SOff 11 2) (SLit ENC_MAGIC)) (SLit 1))
  = Z.shiftl (2 * (len + 2) / 3) 1 mod 2 ^ 64)
  by exact (enc_U_sll E _ 1 (2 * (len + 2) / 3) ltac:(lia) HMH).
assert (HB : 0 <= Z.shiftl (2 * (len + 2) / 3) 1 mod 2 ^ 64 < 2 ^ 64)
  by (apply Z.mod_pos_bound; lia).
assert (HAN : U E (SAlu ALU_AND (SAlu ALU_SLL (SMd M_MULHU (SOff 11 2) (SLit ENC_MAGIC)) (SLit 1))
    (SLit (-4)))
  = Z.land (Z.shiftl (2 * (len + 2) / 3) 1 mod 2 ^ 64) (2 ^ 64 - 4)).
{ rewrite U_SAlu. cbn [zalu_raw]. rewrite HSL, U_SLit.
  replace (zcanon (-4)) with (2 ^ 64 - 4) by reflexivity.
  rewrite (land_m4 _ HB). apply zcanon_id. unfold M64.
  pose proof (Z.mul_div_le (Z.shiftl (2 * (len + 2) / 3) 1 mod 2 ^ 64) 4 ltac:(lia)) as HL.
  pose proof (Z.div_pos (Z.shiftl (2 * (len + 2) / 3) 1 mod 2 ^ 64) 4 ltac:(lia) ltac:(lia)) as HP.
  lia. }
assert (HEQ : Z.land (Z.shiftl (2 * (len + 2) / 3) 1 mod 2 ^ 64) (2 ^ 64 - 4) + 1 = enc_size len).
{ unfold enc_size. rewrite <- (enc_mulhu (len + 2) ltac:(lia)). exact (enc_machine len Hlen). }
apply bv_eq. change (bv_unsigned (sv_denot E ?x)) with (U E x).
rewrite unsigned_lit_small by (unfold enc_size; lia).
rewrite U_SAlu. cbn [zalu_raw]. rewrite HAN, U_SLit, (zcanon_id 1) by (unfold M64; lia).
rewrite HEQ. apply zcanon_id. unfold M64, enc_size. lia.
Qed.

(* the four words the prologue saved, as the chunks of encR_cs under any register map *)
Lemma encE_cs_of_vals : forall (W1 : world tfibsegs) (m : word -> option byte) (sp0 : Z)
  (regs0 regsX : bvmap 5 word),
  val_mem tfibsegs (mrestrict (w_H W1) m) (sp0 - 8) 8 (bv_unsigned (getr regs0 1)) ->
  val_mem tfibsegs (mrestrict (w_H W1) m) (sp0 - 16) 8 (bv_unsigned (getr regs0 8)) ->
  val_mem tfibsegs (mrestrict (w_H W1) m) (sp0 - 24) 8 (bv_unsigned (getr regs0 9)) ->
  val_mem tfibsegs (mrestrict (w_H W1) m) (sp0 - 32) 8 (bv_unsigned (getr regs0 18)) ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regsX (encR_extra regs0)) (mrestrict (w_H W1) m) (sp0 - 32)) encR_cs.
Proof.
intros W1 m sp0 regs0 regsX V1 V8 V9 V18.
assert (F : forall (j : nat) (r : bv 5) od, nth j (encR_extra regs0) (Z_to_bv 64 0) = getr regs0 r ->
  val_mem tfibsegs (mrestrict (w_H W1) m) (sp0 - 32 + od) 8 (bv_unsigned (getr regs0 r)) ->
  YP09.chunk_ok tfibsegs (Ereg regsX (encR_extra regs0)) (mrestrict (w_H W1) m) (sp0 - 32)
    (YP09.mkChunk od (CVal 8 (SOff (32 + j) 0)))).
{ intros j r od Hj Hv.
  apply (chunk_ok_val tfibsegs _ _ _ od 8%N (SOff (32 + j) 0) (bv_unsigned (getr regs0 r)));
    first [ solve [apply u64_range]
          | lazymatch goal with |- sv_denot _ _ = _ =>
              rewrite fsw_SOff0, ew_Ereg_extra, Hj; symmetry; apply Z_to_bv_bv_unsigned end
          | solve [cbn; lia]
          | idtac ].
  cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. exact Hv. }
unfold encR_cs. repeat constructor.
- apply (F 0%nat 1%bv 24 eq_refl). replace (sp0 - 32 + 24) with (sp0 - 8) by lia. exact V1.
- apply (F 1%nat 8%bv 16 eq_refl). replace (sp0 - 32 + 16) with (sp0 - 16) by lia. exact V8.
- apply (F 2%nat 9%bv 8 eq_refl). replace (sp0 - 32 + 8) with (sp0 - 24) by lia. exact V9.
- apply (F 3%nat 18%bv 0 eq_refl). replace (sp0 - 32 + 0) with (sp0 - 32) by lia. exact V18.
Qed.

(* and back: the resumed frame region reads the four words at the resumed memory *)
Lemma encE_vals_of_cs : forall (W1 : world tfibsegs) (m : word -> option byte) (sp0 : Z)
  (regs0 regsX : bvmap 5 word),
  region_ok tfibsegs (Ereg regsX (encR_extra regs0)) (mrestrict (w_H W1) m) (fstk_ret 32 encR_cs) ->
  bv_unsigned (ew (Ereg regsX (encR_extra regs0)) 2) = sp0 - 32 ->
  val_mem tfibsegs (mrestrict (w_H W1) m) (sp0 - 8) 8 (bv_unsigned (getr regs0 1)) /\
  val_mem tfibsegs (mrestrict (w_H W1) m) (sp0 - 16) 8 (bv_unsigned (getr regs0 8)) /\
  val_mem tfibsegs (mrestrict (w_H W1) m) (sp0 - 24) 8 (bv_unsigned (getr regs0 9)) /\
  val_mem tfibsegs (mrestrict (w_H W1) m) (sp0 - 32) 8 (bv_unsigned (getr regs0 18)).
Proof.
intros W1 m sp0 regs0 regsX HR E2.
assert (F : forall (j : nat) (r : bv 5) od, nth j (encR_extra regs0) (Z_to_bv 64 0) = getr regs0 r ->
  In (YP09.mkChunk od (CVal 8 (SOff (32 + j) 0))) encR_cs ->
  val_mem tfibsegs (mrestrict (w_H W1) m) (sp0 - 32 + od) 8 (bv_unsigned (getr regs0 r))).
{ intros j r od Hj Hin.
  apply (fsw_field (Ereg regsX (encR_extra regs0)) _ 2 (sp0 - 32) encR_cs 0 32 0 32 od 8%N
    (SOff (32 + j) 0) (bv_unsigned (getr regs0 r)) HR E2 Hin);
    first [ solve [rewrite fsw_SOff0, ew_Ereg_extra, Hj; symmetry; apply Z_to_bv_bv_unsigned]
          | solve [cbn [Z.of_N]; apply u64_range]
          | solve [cbn [Z.of_N]; lia] ]. }
split; [|split; [|split]].
- replace (sp0 - 8) with (sp0 - 32 + 24) by lia.
  apply (F 0%nat 1%bv 24 eq_refl). unfold encR_cs. cbn [In]. tauto.
- replace (sp0 - 16) with (sp0 - 32 + 16) by lia.
  apply (F 1%nat 8%bv 16 eq_refl). unfold encR_cs. cbn [In]. tauto.
- replace (sp0 - 24) with (sp0 - 32 + 8) by lia.
  apply (F 2%nat 9%bv 8 eq_refl). unfold encR_cs. cbn [In]. tauto.
- replace (sp0 - 32) with (sp0 - 32 + 0) by lia.
  apply (F 3%nat 18%bv 0 eq_refl). unfold encR_cs. cbn [In]. tauto.
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* 11. the Section R hypotheses as one conjunction, at the call's post                                          *)
(* ---------------------------------------------------------------------------------------------------------- *)

(* HLN HBS HBSL HDLO HDHI HARUc HHEADS HQB HAB HQ16 HDB HRBc HGLOBc HTABc HRATc HDATc HKEEPc HFRAMEc HSP0 HRA0,
   in the order Section R declares them *)
Definition encR_hyps (ly0 : alayout) (St0 : astate) (U0 : list (Z * Z)) (W0 : world tfibsegs)
    (mem0 : word -> option byte) (regs0 : bvmap 5 word)
    (lyc : alayout) (Sc : astate) (Wc : world tfibsegs) (memc : word -> option byte) (mdc : Model)
    (data len q live peak cnt fail kd : Z) (bs : list Z) : Prop :=
  0 <= len <= 2 ^ 27 /\ WriterSpec.bytes_ok bs /\ Z.of_nat (length bs) = len /\
  4096 <= data /\ data + len <= alloc_ceiling /\
  ARU tfibsegs B lyc Sc (U0 ++ [(q - HEAD, HEAD)]) Wc memc mdc /\
  fs_heads B lyc Sc (U0 ++ [(q - HEAD, HEAD)]) /\
  In (q - HEAD, enc_size len + HEAD) (ablocks B lyc Sc) /\
  ablocks B lyc Sc = ablocks B ly0 St0 ++ [(q - HEAD, enc_size len + HEAD)] /\
  4096 + HEAD <= q /\
  (0 < len -> In (data - HEAD, kd + HEAD) (ablocks B ly0 St0) /\ len <= kd /\ 0 < kd) /\
  fs_rblock tfibsegs B lyc Sc Wc memc q (enc_size len) /\
  fs_glob tfibsegs Wc memc (live + enc_size len) (Z.max peak (live + enc_size len))
    ((cnt + 1) mod 2 ^ 64) fail /\
  (forall v, 0 <= v < 64 -> val_mem tfibsegs (mrestrict (w_H Wc) memc) (G_B64 + v) 1 (WriterSpec.b64c v)) /\
  range_addressable (aview tfibsegs (w_H Wc) memc) SHADOW_OFF G_B64 65 /\
  garr8 tfibsegs (mrestrict (w_H Wc) memc) data bs /\
  (forall i, 0 <= i < len -> mbyte tfibsegs (mrestrict (w_H Wc) memc) (data + i)
                           = mbyte tfibsegs (mrestrict (w_H W0) mem0) (data + i)) /\
  (val_mem tfibsegs (mrestrict (w_H Wc) memc) (spZ regs0 - 8) 8 (bv_unsigned (getr regs0 1)) /\
   val_mem tfibsegs (mrestrict (w_H Wc) memc) (spZ regs0 - 16) 8 (bv_unsigned (getr regs0 8)) /\
   val_mem tfibsegs (mrestrict (w_H Wc) memc) (spZ regs0 - 24) 8 (bv_unsigned (getr regs0 9)) /\
   val_mem tfibsegs (mrestrict (w_H Wc) memc) (spZ regs0 - 32) 8 (bv_unsigned (getr regs0 18))) /\
  (spZ regs0 mod 16 = 0 /\ alloc_ceiling + STK_preset_base64_encode <= spZ regs0 /\ spZ regs0 <= 2 ^ 47) /\
  YK0s.ret_ok (getr regs0 1).

(* encode_spec's refused arm, as its post states it *)
Definition encR_Qnull (ly0 : alayout) (St0 : astate) (live peak cnt : Z) :
    alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' W' regs' mem' md' =>
    getr regs' 10 = w64 0 /\ ablocks B ly' S' = ablocks B ly0 St0 /\
    fs_glob tfibsegs W' mem' live peak ((cnt + 1) mod 2 ^ 64) SIZE_MAXZ.

(* `acallee_saved (bv_unsigned r)` at a concrete register (the donor's decE_cs_side) *)
Ltac encE_cs_side := unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?qq] =>
    let zz := eval vm_compute in (bv_unsigned qq) in change (bv_unsigned qq) with zz end; lia.

(* ---------------------------------------------------------------------------------------------------------- *)
(* 12. the refused arm: 0x843d8 beqz a0 -> 0x84714, the epilogue, the `ret`                                     *)
(* ---------------------------------------------------------------------------------------------------------- *)

Lemma encR_null_arm : forall ly0 St0 U0 (W0 : world tfibsegs) mem0 md0 regs0
  ly' S' (W' : world tfibsegs) regs' mem' md' live peak cnt,
  (spZ regs0 mod 16 = 0 /\ alloc_ceiling + STK_preset_base64_encode <= spZ regs0 /\ spZ regs0 <= 2 ^ 47) ->
  YK0s.ret_ok (getr regs0 1) -> 0 <= cnt -> cnt + 1 < 2 ^ 64 ->
  ajournal tfibsegs B STK_preset_base64_encode (spZ regs0) FS_PSTAT_FP ly0 St0 W0 (unpoison U0 mem0) md0 []
    ly' S' W' (unpoison U0 mem') md' 0 ->
  ARU tfibsegs B ly' S' U0 W' mem' md' ->
  st_ok tfibsegs (Ereg regs' (encR_extra regs0)) (fss_ret 0x843d8 32 encR_cs)
    (restrict (w_H W') (mkst regs' (w64 0x843d8) mem' (seg_rom tfibsegs))) ->
  getr regs' 10 = w64 0 -> spZ regs' = spZ regs0 - 32 ->
  ablocks B ly' S' = ablocks B ly0 St0 ->
  fs_glob tfibsegs W' mem' live peak (cnt + 1) SIZE_MAXZ ->
  (forall z, acallee_saved z -> z <> 2 -> z <> 8 -> z <> 9 -> z <> 18 ->
     getr regs' (Z_to_bv 5 z) = getr regs0 (Z_to_bv 5 z)) ->
  SRr tfibsegs W' (mkCfg (mkst regs' (w64 0x843d8) mem' (seg_rom tfibsegs)) md')
    (fpostU tfibsegs B STK_preset_base64_encode (spZ regs0) FS_PSTAT_FP regs0 ly0 St0 U0 W0 mem0 md0 0 U0
       (encR_Qnull ly0 St0 live peak cnt)).
Proof.
intros ly0 St0 U0 W0 mem0 md0 regs0 ly' S' W' regs' mem' md' live peak cnt
  HSP0 HRA0 Hcnt0 HCNT HJ HARU HS0 H10 Hsp Hbl HG Rk.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof alloc_ceiling_val as (CR & _).
destruct HSP0 as (Hal16 & Hceil & H47).
assert (HSTK : STK_preset_base64_encode
  = ltac:(let v := eval vm_compute in STK_preset_base64_encode in exact v)) by reflexivity.
assert (E2 : bv_unsigned (ew (Ereg regs' (encR_extra regs0)) 2) = spZ regs0 - 32)
  by (rewrite (ew_Ereg_nat regs' (encR_extra regs0) 2 2%bv eq_refl); exact Hsp).
(* a0 = 0: the `beqz a0` is taken *)
assert (HS : st_ok tfibsegs (Ereg regs' (encR_extra regs0))
  (add_cond (fss_ret 0x843d8 32 encR_cs) (mkAC BC_EQ (SOff 10 0) (SLit 0)))
  (restrict (w_H W') (mkst regs' (w64 0x843d8) mem' (seg_rom tfibsegs)))).
{ apply YP06.st_ok_add_cond; [exact HS0|].
  rewrite fsw_SOff0, (ew_Ereg_nat regs' (encR_extra regs0) 10 10%bv eq_refl), H10.
  vm_compute. reflexivity. }
clear HS0.
fsw_aj_runU fsw_wr_tbl_ok HS HJ HARU.
- unfold add_cond, fss_ret. cbn [ss_mem].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -32);
    [reflexivity | rewrite E2; lia | cbv [fstk_ret YP09.r_wlo]; rewrite HSTK; lia
    | cbv [fstk_ret YP09.r_whi]; lia |].
  apply awr_ok_nil.
- (* at the `ret` 0x84728 *)
  assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs0 - 32 <= a < spZ regs0) ->
    ms_mem ms (Z_to_bv 64 a) = mem' (Z_to_bv 64 a)).
  { intros a Ha Hna. apply HF. rewrite (wz a Ha). intros (r & Hin & Hr).
    unfold add_cond, fss_ret in Hin. cbn [ss_mem In] in Hin.
    destruct Hin as [<-|[]];
      cbv [fstk_ret YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite E2 in Hr; lia. }
  assert (SB : same_below mem' (ms_mem ms) alloc_ceiling) by (intros x Hx; apply MEQ; lia).
  assert (R1F : getr (ms_regs ms) 1 = getr regs0 1).
  { lazymatch type of HS with st_ok _ _ ?ssf _ =>
      pose proof (fsw_reg_extra (w_H W') regs' (encR_extra regs0) ssf ms 1%bv 0 HS
        ltac:(vm_compute; reflexivity)) as R1E end.
    cbn [nth encR_extra] in R1E. exact R1E. }
  assert (Ra0 : getr (ms_regs ms) 10 = w64 0).
  { lazymatch type of HS with st_ok _ _ ?ssf _ =>
      rewrite (st_ok_restrict_reg tfibsegs (w_H W') _ ssf ms 10%bv HS) end.
    lazymatch goal with |- sv_denot _ ?t = _ => let t' := eval vm_compute in t in change t with t' end.
    rewrite fsw_SOff0, (ew_Ereg_nat regs' (encR_extra regs0) 10 10%bv eq_refl). exact H10. }
  apply (fsw_retU B fsw_wr_tbl fsw_wr_tbl_ok W' _ _ ms _ STK_preset_base64_encode (spZ regs0) FS_PSTAT_FP
    regs0 ly0 St0 U0 W0 mem0 md0 ly' S' U0 0 (encR_Qnull ly0 St0 live peak cnt) HS).
  + reflexivity.
  + vm_compute. reflexivity.
  + rewrite R1F. exact HRA0.
  + exact HJ.
  + exact HARU.
  + apply (fsw_preserved _ _ _ ms regs0 encR_expect HS ltac:(vm_compute; reflexivity)).
    intros r Hr. cbv [CALLEE_SAVED In] in Hr.
    repeat (destruct Hr as [<-|Hr]); [..|destruct Hr];
    lazymatch goal with |- sv_denot _ (encR_expect ?z) = _ =>
      let e := eval vm_compute in (encR_expect z) in change (encR_expect z) with e end;
    first
    [ solve [apply bv_eq; rewrite denot_SOff; rewrite E2; unfold spZ;
             replace (bv_unsigned (getr regs0 2) - 32 + 32) with (bv_unsigned (getr regs0 2)) by lia;
             apply zcanon_id; unfold M64; apply u64_range]
    | solve [rewrite fsw_SOff0; change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity]
    | solve [rewrite fsw_SOff0; change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity]
    | solve [rewrite fsw_SOff0; change 35%nat with (32 + 3)%nat; rewrite ew_Ereg_extra; reflexivity]
    | solve [rewrite fsw_SOff0;
             lazymatch goal with |- ew _ ?n = getr _ ?r =>
               rewrite (ew_Ereg_nat regs' (encR_extra regs0) n r eq_refl);
               let z := eval vm_compute in (bv_unsigned r) in
               exact (Rk z ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) end] ].
  + intros mat2. unfold encR_Qnull.
    split; [exact Ra0|]. split; [exact Hbl|].
    rewrite Z.mod_small by lia.
    exact (fs_glob_below W' mem' (ms_mem ms) live peak (cnt + 1) SIZE_MAXZ SB HG).
Qed.

(* a callee-saved register the dispatch leaves as its entry atom (one concrete index per case) *)
Ltac encE_kept HSx :=
  lazymatch goal with
  | |- getr _ (Z_to_bv 5 ?zz) = _ =>
      let nn := eval vm_compute in (Z.to_nat zz) in
      exact (fsw_reg_atom _ _ _ _ _ (Z_to_bv 5 zz) (Z_to_bv 5 zz) nn HSx
               ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
  end.

(* ---------------------------------------------------------------------------------------------------------- *)
(* 13. the dispatch after a granted allocation: 0x843d8 .. one of 0x843fc / 0x845e0 / 0x84700                    *)
(* ---------------------------------------------------------------------------------------------------------- *)

Lemma encR_dispatch : forall ly0 St0 U0 (W0 : world tfibsegs) mem0 md0 regs0
  lyc Sc (Wc : world tfibsegs) memc mdc data len q live peak cnt fail kd bs regsC,
  encR_hyps ly0 St0 U0 W0 mem0 regs0 lyc Sc Wc memc mdc data len q live peak cnt fail kd bs ->
  encR_J ly0 St0 U0 W0 mem0 md0 regs0 lyc Sc Wc q memc mdc ->
  st_ok tfibsegs (Ereg regsC (encR_extra regs0)) (fss_ret 0x843d8 32 encR_cs)
    (restrict (w_H Wc) (mkst regsC (w64 0x843d8) memc (seg_rom tfibsegs))) ->
  getr regsC 8 = w64 len -> getr regsC 9 = w64 data -> getr regsC 10 = w64 q ->
  getr regsC 18 = w64 SHADOW_OFF -> spZ regsC = spZ regs0 - 32 ->
  (forall z, acallee_saved z -> z <> 2 -> z <> 8 -> z <> 9 -> z <> 18 ->
     getr regsC (Z_to_bv 5 z) = getr regs0 (Z_to_bv 5 z)) ->
  (* the loop head at round 0 (a Theorem Labs lane's encR_round_step with r = 0) *)
  (forall ms md, 3 <= len ->
     encR_inv ly0 St0 U0 W0 mem0 md0 regs0 lyc Sc Wc memc len q (ms_mem ms) md ->
     encR_loop_regs regs0 data len q ms 0 ->
     ms = mkst (ms_regs ms) (w64 0x843fc) (ms_mem ms) (seg_rom tfibsegs) ->
     garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) q
       (WriterSpec.b64_enc (firstn (Z.to_nat (3 * 0)) bs)) ->
     SRr tfibsegs Wc (mkCfg ms md)
       (fpostU tfibsegs B STK_preset_base64_encode (spZ regs0) FS_PSTAT_FP regs0 ly0 St0 U0 W0 mem0 md0
          EV_preset_base64_encode (U0 ++ [(q - HEAD, HEAD)])
          (encR_Q ly0 St0 W0 mem0 data len q live peak cnt fail bs))) ->
  (* the tail at R = 0 (encR_tail) *)
  (forall ms md, 0 < len < 3 ->
     encR_inv ly0 St0 U0 W0 mem0 md0 regs0 lyc Sc Wc memc len q (ms_mem ms) md ->
     encR_exit_regs regs0 data len q ms 0 ->
     ms = mkst (ms_regs ms) (w64 0x845e0) (ms_mem ms) (seg_rom tfibsegs) ->
     garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) q
       (WriterSpec.b64_enc (firstn (Z.to_nat (3 * 0)) bs)) ->
     SRr tfibsegs Wc (mkCfg ms md)
       (fpostU tfibsegs B STK_preset_base64_encode (spZ regs0) FS_PSTAT_FP regs0 ly0 St0 U0 W0 mem0 md0
          EV_preset_base64_encode (U0 ++ [(q - HEAD, HEAD)])
          (encR_Q ly0 St0 W0 mem0 data len q live peak cnt fail bs))) ->
  SRr tfibsegs Wc (mkCfg (mkst regsC (w64 0x843d8) memc (seg_rom tfibsegs)) mdc)
    (fpostU tfibsegs B STK_preset_base64_encode (spZ regs0) FS_PSTAT_FP regs0 ly0 St0 U0 W0 mem0 md0
       EV_preset_base64_encode (U0 ++ [(q - HEAD, HEAD)])
       (encR_Q ly0 St0 W0 mem0 data len q live peak cnt fail bs)).
Proof.
intros ly0 St0 U0 W0 mem0 md0 regs0 lyc Sc Wc memc mdc data len q live peak cnt fail kd bs regsC
  HY HJ HS0 R8 R9 R10 R18 Rsp Rk KLOOP KTAIL.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof alloc_ceiling_val as (CR & _).
pose proof HY as (HLN & HBS & HBSL & HDLO & HDHI & HARUc & HHEADS & HQB & HAB & HQ16 & HDB & HRBc & HGLOBc
  & HTABc & HRATc & HDATc & HKEEPc & HFRAMEc & HSP0 & HRA0).
pose proof HSP0 as (Hal16 & Hceil & H47).
pose proof (encR_size_pos len bs HLN HBSL) as HM.
assert (HSTK : STK_preset_base64_encode
  = ltac:(let v := eval vm_compute in STK_preset_base64_encode in exact v)) by reflexivity.
(* q is a heap pointer: inside the band's complement, below PTOP *)
pose proof (ARU_AR tfibsegs B lyc Sc _ Wc memc mdc HARUc) as HARc.
assert (Hrq : req_size (enc_size len + HEAD) = enc_size len + HEAD)
  by (unfold req_size; destruct (Z.eqb_spec (enc_size len + HEAD) 0); unfold HEAD in *; lia).
destruct (enc_blk_bounds lyc Sc Wc (unpoison (U0 ++ [(q - HEAD, HEAD)]) memc) mdc
  (q - HEAD) (enc_size len + HEAD) q HARc HQB
  ltac:(rewrite Hrq; unfold HEAD in *; lia)) as (Hq1 & Hq2 & _).
(* the env of the resumed state *)
assert (E2 : bv_unsigned (ew (Ereg regsC (encR_extra regs0)) 2) = spZ regs0 - 32)
  by (rewrite (ew_Ereg_nat regsC (encR_extra regs0) 2 2%bv eq_refl); exact Rsp).
assert (A8 : ew (Ereg regsC (encR_extra regs0)) 8 = w64 len)
  by (rewrite (ew_Ereg_nat regsC (encR_extra regs0) 8 8%bv eq_refl); exact R8).
assert (A9 : ew (Ereg regsC (encR_extra regs0)) 9 = w64 data)
  by (rewrite (ew_Ereg_nat regsC (encR_extra regs0) 9 9%bv eq_refl); exact R9).
assert (A10 : ew (Ereg regsC (encR_extra regs0)) 10 = w64 q)
  by (rewrite (ew_Ereg_nat regsC (encR_extra regs0) 10 10%bv eq_refl); exact R10).
assert (A18 : ew (Ereg regsC (encR_extra regs0)) 18 = w64 SHADOW_OFF)
  by (rewrite (ew_Ereg_nat regsC (encR_extra regs0) 18 18%bv eq_refl); exact R18).
assert (U8 : bv_unsigned (ew (Ereg regsC (encR_extra regs0)) 8) = len)
  by (rewrite A8; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew (Ereg regsC (encR_extra regs0)) 9) = data)
  by (rewrite A9; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew (Ereg regsC (encR_extra regs0)) 10) = q)
  by (rewrite A10; apply unsigned_lit_small; unfold PTOP in *; lia).
assert (U18 : bv_unsigned (ew (Ereg regsC (encR_extra regs0)) 18) = SHADOW_OFF)
  by (rewrite A18; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
(* the dispatch reads no memory: drop the frame region, so the run keeps every byte *)
assert (HSd : st_ok tfibsegs (Ereg regsC (encR_extra regs0))
  (mkSS (ss_pc (fss_ret 0x843d8 32 encR_cs)) (ss_regs (fss_ret 0x843d8 32 encR_cs)) []
     (ss_resv (fss_ret 0x843d8 32 encR_cs)) (ss_facts (fss_ret 0x843d8 32 encR_cs)))
  (restrict (w_H Wc) (mkst regsC (w64 0x843d8) memc (seg_rom tfibsegs))))
  by exact ((fun Hm => enc_drop_head _ _ _ _ _ Hm HS0) ltac:(vm_compute; reflexivity)).
clear HS0.
(* the two atom facts the branches need: a0 = q in the heap, s0 = len in its arm's range *)
assert (HSq : st_ok tfibsegs (Ereg regsC (encR_extra regs0))
  (add_atom (mkSS (ss_pc (fss_ret 0x843d8 32 encR_cs)) (ss_regs (fss_ret 0x843d8 32 encR_cs)) []
     (ss_resv (fss_ret 0x843d8 32 encR_cs)) (ss_facts (fss_ret 0x843d8 32 encR_cs))) 10%nat
     (mkAF 4112 PTOP 0))
  (restrict (w_H Wc) (mkst regsC (w64 0x843d8) memc (seg_rom tfibsegs)))).
{ apply (st_ok_add_fact tfibsegs _ _ _ 10%nat (mkAF 4112 PTOP 0) HSd).
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U10, Z.pow_0_r.
  split; [unfold HEAD, PTOP in *; lia | split; [apply Z.mod_1_r | lia]]. }
clear HSd.
destruct (Z_le_gt_dec 3 len) as [Hlen3 | Hlen3].
- (* ---- 3 <= len: the loop head 0x843fc ---- *)
  assert (HS : st_ok tfibsegs (Ereg regsC (encR_extra regs0))
    (add_atom (add_atom (mkSS (ss_pc (fss_ret 0x843d8 32 encR_cs)) (ss_regs (fss_ret 0x843d8 32 encR_cs)) []
       (ss_resv (fss_ret 0x843d8 32 encR_cs)) (ss_facts (fss_ret 0x843d8 32 encR_cs))) 10%nat
       (mkAF 4112 PTOP 0)) 8%nat (mkAF 3 (2 ^ 27) 0))
    (restrict (w_H Wc) (mkst regsC (w64 0x843d8) memc (seg_rom tfibsegs)))).
  { apply (st_ok_add_fact tfibsegs _ _ _ 8%nat (mkAF 3 (2 ^ 27) 0) HSq).
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U8, Z.pow_0_r.
    split; [lia | split; [apply Z.mod_1_r | lia]]. }
  clear HSq.
  pose proof HARUc as HARUr.
    fsw_aj_run_toU fsw_wr_tbl_ok HS HJ HARUr 0x843fc.
  + cbn [add_atom ss_mem]. apply awr_ok_nil.
  + assert (MEQ : forall x : word, ms_mem ms x = memc x) by (intros x; exact (frame_of_nil _ _ _ x HF)).
    apply (KLOOP ms _ Hlen3).
    * split; [exact HJ | split; [exact HARUr | intros x Hx; exact (MEQ x)]].
    * split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]]].
      -- exact (enc_reg_val0 _ _ _ _ 8%bv 8 len HS ltac:(vm_compute; reflexivity) U8 ltac:(lia)).
      -- exact (enc_reg_val0 _ _ _ _ 9%bv 9 data HS ltac:(vm_compute; reflexivity) U9 ltac:(lia)).
      -- exact (enc_reg_val0 _ _ _ _ 10%bv 10 q HS ltac:(vm_compute; reflexivity) U10
                  ltac:(unfold PTOP in *; lia)).
      -- replace (q + 4 * 0) with q by lia.
         exact (enc_reg_val0 _ _ _ _ 11%bv 10 q HS ltac:(vm_compute; reflexivity) U10
                  ltac:(unfold PTOP in *; lia)).
      -- replace (data + 3 * 0 + 2) with (data + 2) by lia.
         exact (enc_reg_val _ _ _ _ 12%bv 9 2 data HS ltac:(vm_compute; reflexivity) U9 ltac:(lia)).
      -- replace (3 * 0 + 2) with 2 by lia.
         exact (fsw_reg_lit _ _ _ ms 14%bv 2 HS ltac:(vm_compute; reflexivity) ltac:(lia)).
      -- exact (fsw_reg_lit _ _ _ ms 15%bv G_B64 HS ltac:(vm_compute; reflexivity)
                  ltac:(unfold G_B64; lia)).
      -- replace (q + 4 * 0) with q by lia.
         exact (enc_reg_val0 _ _ _ _ 17%bv 10 q HS ltac:(vm_compute; reflexivity) U10
                  ltac:(unfold PTOP in *; lia)).
      -- exact (enc_reg_val0 _ _ _ _ 18%bv 18 SHADOW_OFF HS ltac:(vm_compute; reflexivity) U18
                  ltac:(unfold SHADOW_OFF; lia)).
      -- unfold spZ at 1.
         rewrite (enc_reg_val0 _ _ _ _ 2%bv 2 (spZ regs0 - 32) HS ltac:(vm_compute; reflexivity) E2
           ltac:(unfold spZ in *; pose proof (u64_range (getr regs0 2)); lia)).
         unfold w64. rewrite unsigned_lit_small
           by (unfold spZ in *; pose proof (u64_range (getr regs0 2)); lia).
         reflexivity.
      -- intros z Hz H2 H8 H9 H18. rewrite <- (Rk z Hz H2 H8 H9 H18).
         assert (Hc : z = 3 \/ z = 4 \/ z = 19 \/ z = 20 \/ z = 21 \/ z = 22 \/ z = 23 \/
           z = 24 \/ z = 25 \/ z = 26 \/ z = 27) by (unfold acallee_saved in Hz; lia).
         repeat (destruct Hc as [->|Hc]); try subst z; encE_kept HS.
    * exact (st_ok_restrict_mkst tfibsegs (w_H Wc) _ _ ms HS eq_refl).
    * cbn [Z.mul Z.to_nat firstn WriterSpec.b64_enc]. apply garr8_nil.
- destruct (Z.eq_dec len 0) as [Hlen0 | Hlen0].
  + (* ---- len = 0: the terminating 0 at 0x84700, then encR_nul ---- *)
    assert (HS : st_ok tfibsegs (Ereg regsC (encR_extra regs0))
      (add_atom (add_atom (mkSS (ss_pc (fss_ret 0x843d8 32 encR_cs)) (ss_regs (fss_ret 0x843d8 32 encR_cs)) []
         (ss_resv (fss_ret 0x843d8 32 encR_cs)) (ss_facts (fss_ret 0x843d8 32 encR_cs))) 10%nat
         (mkAF 4112 PTOP 0)) 8%nat (mkAF 0 0 0))
      (restrict (w_H Wc) (mkst regsC (w64 0x843d8) memc (seg_rom tfibsegs)))).
    { apply (st_ok_add_fact tfibsegs _ _ _ 8%nat (mkAF 0 0 0) HSq).
      unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U8, Z.pow_0_r.
      split; [lia | split; [apply Z.mod_1_r | lia]]. }
    clear HSq.
    pose proof HARUc as HARUr.
    fsw_aj_run_toU fsw_wr_tbl_ok HS HJ HARUr 0x84700.
    * cbn [add_atom ss_mem]. apply awr_ok_nil.
    * assert (MEQ : forall x : word, ms_mem ms x = memc x) by (intros x; exact (frame_of_nil _ _ _ x HF)).
      assert (HINV : encR_inv ly0 St0 U0 W0 mem0 md0 regs0 lyc Sc Wc memc len q (ms_mem ms) _)
        by (split; [exact HJ | split; [exact HARUr | intros x Hx; exact (MEQ x)]]).
      assert (HBSnil : bs = []) by (destruct bs as [|b bs']; [reflexivity | cbn [length] in HBSL; lia]).
      apply (encR_nul ly0 St0 U0 W0 mem0 md0 regs0 lyc Sc Wc memc mdc data len q live peak cnt fail kd bs
        HLN HBSL HDLO HDHI HARUc HHEADS HQB HAB HQ16 HDB HRBc HGLOBc HKEEPc HFRAMEc HSP0 HRA0 ms _ HINV).
      -- rewrite HBSnil. cbn [WriterSpec.b64_enc]. apply garr8_nil.
      -- exact (st_ok_restrict_mkst tfibsegs (w_H Wc) _ _ ms HS eq_refl).
      -- exact (enc_reg_val0 _ _ _ _ 10%bv 10 q HS ltac:(vm_compute; reflexivity) U10
                  ltac:(unfold PTOP in *; lia)).
      -- replace (q + 4 * ((len + 2) / 3)) with q by (rewrite Hlen0; cbn; lia).
         exact (enc_reg_val0 _ _ _ _ 11%bv 10 q HS ltac:(vm_compute; reflexivity) U10
                  ltac:(unfold PTOP in *; lia)).
      -- exact (enc_reg_val0 _ _ _ _ 18%bv 18 SHADOW_OFF HS ltac:(vm_compute; reflexivity) U18
                  ltac:(unfold SHADOW_OFF; lia)).
      -- unfold spZ at 1.
         rewrite (enc_reg_val0 _ _ _ _ 2%bv 2 (spZ regs0 - 32) HS ltac:(vm_compute; reflexivity) E2
           ltac:(unfold spZ in *; pose proof (u64_range (getr regs0 2)); lia)).
         unfold w64. rewrite unsigned_lit_small
           by (unfold spZ in *; pose proof (u64_range (getr regs0 2)); lia).
         reflexivity.
      -- intros z Hz H2 H8 H9 H18. rewrite <- (Rk z Hz H2 H8 H9 H18).
         assert (Hc : z = 3 \/ z = 4 \/ z = 19 \/ z = 20 \/ z = 21 \/ z = 22 \/ z = 23 \/
           z = 24 \/ z = 25 \/ z = 26 \/ z = 27) by (unfold acallee_saved in Hz; lia).
         repeat (destruct Hc as [->|Hc]); try subst z; encE_kept HS.
  + (* ---- 0 < len < 3: the tail's boundary 0x845e0 at R = 0 ---- *)
    assert (HS : st_ok tfibsegs (Ereg regsC (encR_extra regs0))
      (add_atom (add_atom (mkSS (ss_pc (fss_ret 0x843d8 32 encR_cs)) (ss_regs (fss_ret 0x843d8 32 encR_cs)) []
         (ss_resv (fss_ret 0x843d8 32 encR_cs)) (ss_facts (fss_ret 0x843d8 32 encR_cs))) 10%nat
         (mkAF 4112 PTOP 0)) 8%nat (mkAF 1 2 0))
      (restrict (w_H Wc) (mkst regsC (w64 0x843d8) memc (seg_rom tfibsegs)))).
    { apply (st_ok_add_fact tfibsegs _ _ _ 8%nat (mkAF 1 2 0) HSq).
      unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U8, Z.pow_0_r.
      split; [lia | split; [apply Z.mod_1_r | lia]]. }
    clear HSq.
    pose proof HARUc as HARUr.
    fsw_aj_run_toU fsw_wr_tbl_ok HS HJ HARUr 0x845e0.
    * cbn [add_atom ss_mem]. apply awr_ok_nil.
    * assert (MEQ : forall x : word, ms_mem ms x = memc x) by (intros x; exact (frame_of_nil _ _ _ x HF)).
      apply (KTAIL ms _ ltac:(lia)).
      -- split; [exact HJ | split; [exact HARUr | intros x Hx; exact (MEQ x)]].
      -- split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
         ++ exact (enc_reg_val0 _ _ _ _ 8%bv 8 len HS ltac:(vm_compute; reflexivity) U8 ltac:(lia)).
         ++ exact (enc_reg_val0 _ _ _ _ 9%bv 9 data HS ltac:(vm_compute; reflexivity) U9 ltac:(lia)).
         ++ exact (enc_reg_val0 _ _ _ _ 10%bv 10 q HS ltac:(vm_compute; reflexivity) U10
                     ltac:(unfold PTOP in *; lia)).
         ++ replace (q + 4 * 0) with q by lia.
            exact (enc_reg_val0 _ _ _ _ 11%bv 10 q HS ltac:(vm_compute; reflexivity) U10
                     ltac:(unfold PTOP in *; lia)).
         ++ replace (3 * 0) with 0 by lia.
            exact (fsw_reg_lit _ _ _ ms 14%bv 0 HS ltac:(vm_compute; reflexivity) ltac:(lia)).
         ++ exact (enc_reg_val0 _ _ _ _ 18%bv 18 SHADOW_OFF HS ltac:(vm_compute; reflexivity) U18
                     ltac:(unfold SHADOW_OFF; lia)).
         ++ unfold spZ at 1.
            rewrite (enc_reg_val0 _ _ _ _ 2%bv 2 (spZ regs0 - 32) HS ltac:(vm_compute; reflexivity) E2
              ltac:(unfold spZ in *; pose proof (u64_range (getr regs0 2)); lia)).
            unfold w64. rewrite unsigned_lit_small
              by (unfold spZ in *; pose proof (u64_range (getr regs0 2)); lia).
            reflexivity.
         ++ intros z Hz H2 H8 H9 H18. rewrite <- (Rk z Hz H2 H8 H9 H18).
            assert (Hc : z = 3 \/ z = 4 \/ z = 19 \/ z = 20 \/ z = 21 \/ z = 22 \/ z = 23 \/
              z = 24 \/ z = 25 \/ z = 26 \/ z = 27) by (unfold acallee_saved in Hz; lia).
            repeat (destruct Hc as [->|Hc]); try subst z; encE_kept HS.
      -- exact (st_ok_restrict_mkst tfibsegs (w_H Wc) _ _ ms HS eq_refl).
      -- cbn [Z.mul Z.to_nat firstn WriterSpec.b64_enc]. apply garr8_nil.
Qed.

(* ---------------------------------------------------------------------------------------------------------- *)
(* 14. the entry 0x84390 .. 0x843d4, the fuzz_malloc call, and its two arms                                      *)
(* ---------------------------------------------------------------------------------------------------------- *)

(* the entry state: the 32-byte frame, the two shadow-base cells, and the .rodata word the size arithmetic reads *)
Definition encE_ss0 : sstate := fss0T_args A_preset_base64_encode 32 [enc_magic_region] [].

Lemma encR_entry : forall ly S U (W : world tfibsegs) regs mem md ch data len (bs : list Z) live peak cnt fail,
  fpreU tfibsegs B STK_preset_base64_encode ly S U W regs mem md ch -> fs_heads B ly S U ->
  getr regs 10 = w64 data -> getr regs 11 = w64 len ->
  WriterSpec.bytes_ok bs -> Z.of_nat (length bs) = len -> 0 <= len <= 2 ^ 27 ->
  zbytes_at tfibsegs W mem data bs -> 4096 <= data -> data + len <= alloc_ceiling ->
  (0 < len -> exists kd, fs_rblock tfibsegs B ly S W mem data kd /\ len <= kd) ->
  fs_glob tfibsegs W mem live peak cnt fail ->
  st_nev S + EV_preset_base64_encode <= EV_MAX -> blocks_bytes S + (enc_size len + HEAD) <= LIVE_MAX ->
  live + enc_size len < 2 ^ 64 -> cnt + 1 < 2 ^ 64 ->
  (* the head of the 3-byte loop, round 0 *)
  (forall lyc Sc (Wc : world tfibsegs) memc mdc q kd ms md', 3 <= len ->
     encR_hyps ly S U W mem regs lyc Sc Wc memc mdc data len q live peak cnt fail kd bs ->
     encR_inv ly S U W mem md regs lyc Sc Wc memc len q (ms_mem ms) md' ->
     encR_loop_regs regs data len q ms 0 ->
     ms = mkst (ms_regs ms) (w64 0x843fc) (ms_mem ms) (seg_rom tfibsegs) ->
     garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) q
       (WriterSpec.b64_enc (firstn (Z.to_nat (3 * 0)) bs)) ->
     SRr tfibsegs Wc (mkCfg ms md')
       (fpostU tfibsegs B STK_preset_base64_encode (spZ regs) FS_PSTAT_FP regs ly S U W mem md
          EV_preset_base64_encode (U ++ [(q - HEAD, HEAD)])
          (encR_Q ly S W mem data len q live peak cnt fail bs))) ->
  (* the tail at R = 0 *)
  (forall lyc Sc (Wc : world tfibsegs) memc mdc q kd ms md', 0 < len < 3 ->
     encR_hyps ly S U W mem regs lyc Sc Wc memc mdc data len q live peak cnt fail kd bs ->
     encR_inv ly S U W mem md regs lyc Sc Wc memc len q (ms_mem ms) md' ->
     encR_exit_regs regs data len q ms 0 ->
     ms = mkst (ms_regs ms) (w64 0x845e0) (ms_mem ms) (seg_rom tfibsegs) ->
     garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) q
       (WriterSpec.b64_enc (firstn (Z.to_nat (3 * 0)) bs)) ->
     SRr tfibsegs Wc (mkCfg ms md')
       (fpostU tfibsegs B STK_preset_base64_encode (spZ regs) FS_PSTAT_FP regs ly S U W mem md
          EV_preset_base64_encode (U ++ [(q - HEAD, HEAD)])
          (encR_Q ly S W mem data len q live peak cnt fail bs))) ->
  SRr tfibsegs W (cfg_at tfibsegs A_preset_base64_encode regs mem md)
    (fun W' c' =>
       (cnt = fail /\
        fpostU tfibsegs B STK_preset_base64_encode (spZ regs) FS_PSTAT_FP regs ly S U W mem md 0 U
          (encR_Qnull ly S live peak cnt) W' c')
       \/
       (exists q, cnt <> fail /\ q <> 0 /\
        fpostU tfibsegs B STK_preset_base64_encode (spZ regs) FS_PSTAT_FP regs ly S U W mem md
          EV_preset_base64_encode (U ++ [(q - HEAD, HEAD)])
          (encR_Q ly S W mem data len q live peak cnt fail bs) W' c')).
Proof.
intros ly S U W regs mem md ch data len bs live peak cnt fail
  HPRE HH H10 H11 HBS HBSL HLN HZB HDLO HDHI HDB0 HGL HEV HLV HLIVE HCNT KLOOP KTAIL.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof alloc_ceiling_val as (CR & _).
assert (HSTK : STK_preset_base64_encode
  = ltac:(let v := eval vm_compute in STK_preset_base64_encode in exact v)) by reflexivity.
assert (HFM : STK_fuzz_malloc = ltac:(let v := eval vm_compute in STK_fuzz_malloc in exact v)) by reflexivity.
pose proof (encR_size_pos len bs HLN HBSL) as HM.
assert (HQD : (len + 2) / 3 <= 44739244) by (apply Z.div_le_upper_bound; lia).
assert (HSZ : enc_size len + HEAD < MALLOC_MAX) by (unfold enc_size, MALLOC_MAX, HEAD; lia).
pose proof HPRE as (HPREU & HRO).
pose proof (fsw_ARU B STK_preset_base64_encode ly S U W regs mem md ch HPREU) as HARU0.
pose proof HPREU as (HAP & HUOK & HUPO).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof (fsw_sp B STK_preset_base64_encode ly S U W regs mem md ch HPREU) as (Hal16 & Hceil & H47 & HSTK0).
assert (Hcnt0 : 0 <= cnt) by (pose proof HGL as (_ & _ & _ & _ & _ & _ & Hc & _); lia).
assert (Hlive0 : 0 <= live) by (pose proof HGL as (_ & _ & _ & _ & Hl & _); lia).
(* ---- the entry state at 0x84390 ---- *)
assert (HROu : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) (unpoison U mem)))
  by exact (encE_aro_unp ly S U W mem md HARU0 HRO).
pose proof IMG as (_ & IMG2).
pose proof (IMG2 ly S W (unpoison U mem) md HAR HROu) as (HROM & _).
assert (E2 : bv_unsigned (ew (Ereg regs fs_extraT) 2) = spZ regs)
  by (rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl); reflexivity).
assert (HS : st_ok tfibsegs (Ereg regs fs_extraT) encE_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 A_preset_base64_encode) mem (seg_rom tfibsegs)))).
{ apply (fsw_entryT_args B STK_preset_base64_encode 32 ly S U W regs mem md ch A_preset_base64_encode
    [enc_magic_region] [] (proj1 HSS) (proj2 HSS) HPREU ltac:(rewrite HSTK; lia)).
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    unfold enc_magic_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    split; [unfold ENC_MAGIC_A; lia|]. split; [unfold ENC_MAGIC_A; lia|].
    split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs _ _ 0 ENC_MAGIC_A 8%N (SLit ENC_MAGIC) ENC_MAGIC);
      [reflexivity | unfold ENC_MAGIC; cbn [Z.of_N]; lia | cbn [Z.of_N]; lia |].
    cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. rewrite Z.add_0_l.
    exact (enc_magic_val ly S U W mem md HARU0 HROM).
  - apply pairwise_disjoint_of_extents.
    unfold fsT_regions_args, fsT_regions, fstk, fs_got_region, fs_bcell_region, enc_magic_region,
      extent_of_region.
    cbn [map app YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2.
    unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address,
      ENC_MAGIC_A.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia].
  - exact I. }
assert (HJ : ajournal tfibsegs B STK_preset_base64_encode (spZ regs) FS_PSTAT_FP ly S W (unpoison U mem) md []
               ly S W (unpoison U mem) md 0)
  by exact (ajournal_init tfibsegs B STK_preset_base64_encode FS_PSTAT_FP ly S W regs (unpoison U mem) md ch HAP).
(* ---- the run 0x84390 -> the jal of fuzz_malloc ---- *)
unfold cfg_at.
fsw_aj_run_toU fsw_wr_tbl_ok HS HJ HARU0 A_fuzz_malloc.
{ unfold encE_ss0, fss0T_args, fsT_regions_args, fsT_regions. cbn [ss_mem app].
  eapply awr_ok_cons_stack with (n := 2%nat);
    [reflexivity | exact E2 | cbv [fstk YP09.r_wlo]; rewrite HSTK; lia | cbv [fstk YP09.r_whi]; lia |].
  apply awr_ok_cons_ro; [cbv [fs_got_region YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_cons_ro; [cbv [fs_bcell_region YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_cons_ro; [cbv [enc_magic_region YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (mdT := m) in * end.
(* the run wrote only the frame, so every byte below the ceiling is the entry byte *)
assert (SB : same_below mem (ms_mem ms) alloc_ceiling).
{ intros x Hx.
  apply (enc_frame_X (Ereg regs fs_extraT) (ss_mem encE_ss0) mem (ms_mem ms)
    (fun a => spZ regs - 32 <= a < spZ regs) HF).
  - intros a (r & Hin & Hr).
    unfold encE_ss0, fss0T_args, fsT_regions_args, fsT_regions in Hin. cbn [ss_mem app In] in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
      cbv [fstk fs_got_region fs_bcell_region enc_magic_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      try rewrite E2 in Hr; lia.
  - rewrite (wz x ltac:(lia)). lia. }
assert (HROc : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) (ms_mem ms)))
  by exact (arodata_below B W mem (ms_mem ms) SB HRO).
assert (HGLc : fs_glob tfibsegs W (ms_mem ms) live peak cnt fail)
  by exact (fs_glob_below W mem (ms_mem ms) live peak cnt fail SB HGL).
(* ---- the registers at the call ---- *)
pose proof (fsw_reg_lit _ _ _ ms 1%bv 0x843d8 HS ltac:(vm_compute; reflexivity) ltac:(lia)) as R1c.
pose proof (fsw_reg_off _ _ _ ms 2%bv 2 (-32) (spZ regs) HS ltac:(vm_compute; reflexivity) E2 ltac:(lia)) as R2c.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms 3%bv 3%bv 3 HS ltac:(vm_compute; reflexivity) eq_refl) as R3c.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms 4%bv 4%bv 4 HS ltac:(vm_compute; reflexivity) eq_refl) as R4c.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms 8%bv 11%bv 11 HS ltac:(vm_compute; reflexivity) eq_refl) as R8c.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms 9%bv 10%bv 10 HS ltac:(vm_compute; reflexivity) eq_refl) as R9c.
pose proof (fsw_reg_extra _ regs fs_extraT _ ms 18%bv 0 HS ltac:(vm_compute; reflexivity)) as R18c.
cbn [nth fs_extraT] in R18c.
assert (Hspc : spZ (ms_regs ms) = spZ regs - 32) by (unfold spZ at 1; exact R2c).
assert (R10c : getr (ms_regs ms) 10 = w64 (enc_size len)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W) _ _ ms 10%bv HS).
  lazymatch goal with |- sv_denot _ ?t = _ => let t' := eval vm_compute in t in change t with t' end.
  apply (encE_size_den _ len);
    [rewrite (ew_Ereg_nat regs fs_extraT 11 11%bv eq_refl); exact H11 | lia]. }
(* ---- the four saved words, read at the call ---- *)
pose proof (fsw_region_nth (Ereg regs fs_extraT) _ (restrict (w_H W) ms) 0%nat _ HS eq_refl) as HR0.
cbn [ms_mem restrict] in HR0.
assert (VSAVE :
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) /\
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) /\
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) /\
  val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (spZ regs - 32) 8 (bv_unsigned (getr regs 18))).
{ assert (F : forall (n : nat) (r : bv 5) od, Z.of_nat n = bv_unsigned r ->
    In (YP09.mkChunk od (CVal 8 (SOff n 0)))
      [YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
       YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))] ->
    val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) (spZ regs + od) 8 (bv_unsigned (getr regs r))).
  { intros n r od Hn Hin.
    apply (fsw_field (Ereg regs fs_extraT) _ 2%nat (spZ regs) _ _ _ _ _ od 8%N (SOff n 0)
      (bv_unsigned (getr regs r)) HR0 E2 Hin);
      first [ solve [rewrite fsw_SOff0, (ew_Ereg_nat regs fs_extraT n r Hn); symmetry;
                     apply Z_to_bv_bv_unsigned]
            | solve [cbn [Z.of_N]; apply u64_range]
            | solve [cbn [Z.of_N]; lia] ]. }
  split; [|split; [|split]].
  - replace (spZ regs - 8) with (spZ regs + (-8)) by lia.
    apply (F 1%nat 1%bv (-8) eq_refl). cbn [In]. tauto.
  - replace (spZ regs - 16) with (spZ regs + (-16)) by lia.
    apply (F 8%nat 8%bv (-16) eq_refl). cbn [In]. tauto.
  - replace (spZ regs - 24) with (spZ regs + (-24)) by lia.
    apply (F 9%nat 9%bv (-24) eq_refl). cbn [In]. tauto.
  - replace (spZ regs - 32) with (spZ regs + (-32)) by lia.
    apply (F 18%nat 18%bv (-32) eq_refl). cbn [In]. tauto. }
pose proof VSAVE as (VS1 & VS8 & VS9 & VS18).
(* ---- the callee's precondition ---- *)
assert (HPREc : fpreU tfibsegs B STK_fuzz_malloc ly S U W (ms_regs ms) (ms_mem ms) mdT []).
{ apply (fsw_fpreU_atFP B STK_preset_base64_encode (spZ regs) FS_PSTAT_FP ly S U W (unpoison U mem) md []
    ly S W (ms_mem ms) mdT 0 (ms_regs ms) STK_fuzz_malloc (-32) [] HJ HARU0 HROc).
  - lia.
  - reflexivity.
  - lia.
  - rewrite HFM. lia.
  - rewrite HSTK, HFM. lia.
  - rewrite R1c. apply ret_ok_even. rewrite unsigned_lit_small by lia. reflexivity.
  - unfold raZ. rewrite R1c, unsigned_lit_small by lia. lia.
  - rewrite R3c. exact Hgp.
  - rewrite R4c. exact Htp.
  - apply achain_low. unfold s0Z. rewrite R8c, H11, unsigned_lit_small by lia. lia. }
assert (HEV1 : st_nev S + 1 <= EV_MAX) by exact HEV.
(* ---- the call ---- *)
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms HS eq_refl). cbn [ss_pc].
eapply SRr_bind;
  [exact (HMALLOC ly S U W (ms_regs ms) (ms_mem ms) mdT [] (enc_size len) live peak cnt fail
     HPREc HH R10c ltac:(lia) HSZ HGLc (fun _ => ltac:(lia)) HCNT HEV1
     (fun _ => HLV))|].
intros W' c' Hwle [(Hcf & HQ1) | (Hcf & res & HQ2)].
- (* ---- the refused arm ---- *)
  destruct HQ1 as (ly' & S' & regs' & mem' & md' & -> & HJc & OK' & PO' & HP' & H10' & Hbl' & HH' & HG').
  rewrite R1c.
  assert (HARU' : ARU tfibsegs B ly' S' U W' mem' md')
    by (split; [exact (proj1 HJc) | split; [exact OK' | exact PO']]).
  destruct (fsw_after_callFPU B STK_preset_base64_encode (spZ regs) FS_PSTAT_FP [] ly S U W mem md W
    ly S U (ms_mem ms) mdT 0 STK_fuzz_malloc FS_PSTAT_FP 32 (ms_regs ms) ly' S' U W' regs' mem' md' 0
    (encR_extra regs) encR_cs 0x843d8 HJ HARU0 HJc (encE_fp_sub ly S ly S) OK' PO' HP' Hspc
    ltac:(lia) ltac:(rewrite HFM; lia) ltac:(rewrite HSTK, HFM; lia) ltac:(reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(unfold encR_cs; repeat constructor; cbn; lia)
    (encE_cs_of_vals W (ms_mem ms) (spZ regs) regs regs' VS1 VS8 VS9 VS18)) as (HJ2 & HARU2 & HS2).
  assert (Rsp' : spZ regs' = spZ regs - 32)
    by (unfold spZ at 1; rewrite (fsw_pres _ _ 2%bv HP' ltac:(encE_cs_side)); exact R2c).
  eapply SRr_mono;
    [ apply (encR_null_arm ly S U W mem md regs ly' S' W' regs' mem' md' live peak cnt
        (conj Hal16 (conj Hceil H47)) Hra Hcnt0 HCNT HJ2 HARU2 HS2 H10' Rsp' Hbl' HG')
    | intros W2 c2 _ HP; left; split; [exact Hcf | exact HP] ].
  intros z Hz H2 H8 H9 H18.
  rewrite (fsw_pres (ms_regs ms) regs' (Z_to_bv 5 z) HP'
    ltac:(rewrite Z_to_bv_unsigned, bv_wrap_small;
          [exact Hz | change (bv_modulus 5) with 32; unfold acallee_saved in Hz; lia])).
  assert (Hc : z = 3 \/ z = 4 \/ z = 19 \/ z = 20 \/ z = 21 \/ z = 22 \/ z = 23 \/
    z = 24 \/ z = 25 \/ z = 26 \/ z = 27) by (unfold acallee_saved in Hz; lia).
  repeat (destruct Hc as [->|Hc]); try subst z; encE_kept HS.
- (* ---- the granted arm ---- *)
  destruct HQ2 as (ly' & S' & regs' & mem' & md' & -> & HJc & OK' & PO' & HP' & H10' & Hres4 & Hbl' & HH'
    & Hrb & Hra' & HG').
  rewrite R1c.
  assert (HARU' : ARU tfibsegs B ly' S' (U ++ [(res - HEAD, HEAD)]) W' mem' md')
    by (split; [exact (proj1 HJc) | split; [exact OK' | exact PO']]).
  destruct (fsw_after_callFPU B STK_preset_base64_encode (spZ regs) FS_PSTAT_FP [] ly S U W mem md W
    ly S U (ms_mem ms) mdT 0 STK_fuzz_malloc FS_PSTAT_FP 32 (ms_regs ms) ly' S'
    (U ++ [(res - HEAD, HEAD)]) W' regs' mem' md' 1
    (encR_extra regs) encR_cs 0x843d8 HJ HARU0 HJc (encE_fp_sub ly S ly S) OK' PO' HP' Hspc
    ltac:(lia) ltac:(rewrite HFM; lia) ltac:(rewrite HSTK, HFM; lia) ltac:(reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(unfold encR_cs; repeat constructor; cbn; lia)
    (encE_cs_of_vals W (ms_mem ms) (spZ regs) regs regs' VS1 VS8 VS9 VS18)) as (HJ2 & HARU2 & HS2).
  assert (Rsp' : spZ regs' = spZ regs - 32)
    by (unfold spZ at 1; rewrite (fsw_pres _ _ 2%bv HP' ltac:(encE_cs_side)); exact R2c).
  assert (Rk' : forall z, acallee_saved z -> z <> 2 -> z <> 8 -> z <> 9 -> z <> 18 ->
    getr regs' (Z_to_bv 5 z) = getr regs (Z_to_bv 5 z)).
  { intros z Hz H2 H8 H9 H18.
    rewrite (fsw_pres (ms_regs ms) regs' (Z_to_bv 5 z) HP'
      ltac:(rewrite Z_to_bv_unsigned, bv_wrap_small;
            [exact Hz | change (bv_modulus 5) with 32; unfold acallee_saved in Hz; lia])).
    assert (Hc : z = 3 \/ z = 4 \/ z = 19 \/ z = 20 \/ z = 21 \/ z = 22 \/ z = 23 \/
      z = 24 \/ z = 25 \/ z = 26 \/ z = 27) by (unfold acallee_saved in Hz; lia).
    repeat (destruct Hc as [->|Hc]); try subst z; encE_kept HS. }
  assert (R8' : getr regs' 8 = w64 len)
    by (rewrite (fsw_pres _ _ 8%bv HP' ltac:(encE_cs_side)), R8c; exact H11).
  assert (R9' : getr regs' 9 = w64 data)
    by (rewrite (fsw_pres _ _ 9%bv HP' ltac:(encE_cs_side)), R9c; exact H10).
  assert (R18' : getr regs' 18 = w64 SHADOW_OFF)
    by (rewrite (fsw_pres _ _ 18%bv HP' ltac:(encE_cs_side)); exact R18c).
  (* the Section R hypotheses at the call's post *)
  assert (HTAB : (forall v, 0 <= v < 64 ->
      val_mem tfibsegs (mrestrict (w_H W') mem') (G_B64 + v) 1 (WriterSpec.b64c v)) /\
    range_addressable (aview tfibsegs (w_H W') mem') SHADOW_OFF G_B64 65).
  { apply (enc_table ly' S' (U ++ [(res - HEAD, HEAD)]) W' mem' md' HARU' HH').
    apply (encE_aro_unp ly' S' (U ++ [(res - HEAD, HEAD)]) W' mem' md' HARU').
    exact (encE_aro_call STK_fuzz_malloc (spZ (ms_regs ms)) ly S U W (ms_mem ms) mdT ly' S'
             (U ++ [(res - HEAD, HEAD)]) W' mem' md' 1 HJc HARU0 OK' PO' HROc). }
  pose proof HTAB as (HTABc & HRATc).
  (* the input block, when there is one *)
  assert (HKD : exists kd, 0 < len -> In (data - HEAD, kd + HEAD) (ablocks B ly S) /\ len <= kd /\ 0 < kd).
  { destruct (Z_lt_le_dec 0 len) as [Hl|Hl].
    - destruct (HDB0 Hl) as (kd & (HinD & Hd16 & Hdpos & HdV) & Hkd).
      exists kd. intros _. split; [exact HinD | split; [exact Hkd | exact Hdpos]].
    - exists 1. intros Hc. lia. }
  destruct HKD as (kd & HDBc).
  assert (HKEEPc : forall i, 0 <= i < len ->
    mbyte tfibsegs (mrestrict (w_H W') mem') (data + i) = mbyte tfibsegs (mrestrict (w_H W) mem) (data + i)).
  { intros i Hi.
    destruct (HDBc ltac:(lia)) as (HinD & Hkd & Hdpos).
    assert (Hrqd : req_size (kd + HEAD) = kd + HEAD)
      by (unfold req_size; destruct (Z.eqb_spec (kd + HEAD) 0); unfold HEAD in *; lia).
    assert (HinD' : In (data - HEAD, kd + HEAD) (ablocks B ly' S'))
      by (rewrite Hbl'; apply in_or_app; left; exact HinD).
    rewrite (encE_blk_keep STK_fuzz_malloc (spZ (ms_regs ms)) ly S U W (ms_mem ms) mdT ly' S'
      (U ++ [(res - HEAD, HEAD)]) W' mem' md' 1 (data - HEAD) (kd + HEAD) (data + i)
      HJc HARU0 OK' PO' HinD HinD' ltac:(rewrite Hrqd; unfold HEAD in *; lia)).
    exact (mbyte_below (w_H W) mem (ms_mem ms) alloc_ceiling (data + i) SB ltac:(lia)). }
  assert (HDATc : garr8 tfibsegs (mrestrict (w_H W') mem') data bs).
  { apply (garr8_frame tfibsegs (mrestrict (w_H W) mem) _ data bs HZB).
    intros a Ha. rewrite HBSL in Ha. replace a with (data + (a - data)) by lia.
    exact (HKEEPc (a - data) ltac:(lia)). }
  assert (HQBc : In (res - HEAD, enc_size len + HEAD) (ablocks B ly' S'))
    by (rewrite Hbl'; apply in_or_app; right; left; reflexivity).
  assert (HGLc' : fs_glob tfibsegs W' mem' (live + enc_size len) (Z.max peak (live + enc_size len))
    ((cnt + 1) mod 2 ^ 64) fail)
    by (rewrite (Z.mod_small (cnt + 1) (2 ^ 64) ltac:(lia)); exact HG').
  assert (HFRAMEc :
    val_mem tfibsegs (mrestrict (w_H W') mem') (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) /\
    val_mem tfibsegs (mrestrict (w_H W') mem') (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) /\
    val_mem tfibsegs (mrestrict (w_H W') mem') (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) /\
    val_mem tfibsegs (mrestrict (w_H W') mem') (spZ regs - 32) 8 (bv_unsigned (getr regs 18))).
  { apply (encE_vals_of_cs W' mem' (spZ regs) regs regs').
    - pose proof (fsw_region_nth (Ereg regs' (encR_extra regs)) _
        (restrict (w_H W') (mkst regs' (Z_to_bv 64 0x843d8) mem' (seg_rom tfibsegs))) 0%nat _ HS2 eq_refl) as HRg.
      cbn [ms_mem restrict mkst] in HRg. exact HRg.
    - rewrite (ew_Ereg_nat regs' (encR_extra regs) 2 2%bv eq_refl). exact Rsp'. }
  assert (HY : encR_hyps ly S U W mem regs ly' S' W' mem' md' data len res live peak cnt fail kd bs).
  { unfold encR_hyps.
    split; [exact HLN|]. split; [exact HBS|]. split; [exact HBSL|]. split; [exact HDLO|].
    split; [exact HDHI|]. split; [exact HARU'|]. split; [exact HH'|]. split; [exact HQBc|].
    split; [exact Hbl'|]. split; [unfold HEAD in *; lia|]. split; [exact HDBc|].
    split; [exact (Hrb ltac:(lia))|]. split; [exact HGLc'|]. split; [exact HTABc|].
    split; [exact HRATc|]. split; [exact HDATc|]. split; [exact HKEEPc|]. split; [exact HFRAMEc|].
    split; [exact (conj Hal16 (conj Hceil H47)) | exact Hra]. }
  eapply SRr_mono;
    [ apply (encR_dispatch ly S U W mem md regs ly' S' W' mem' md' data len res live peak cnt fail kd bs regs'
        HY HJ2 HS2 R8' R9' H10' R18' Rsp' Rk')
    | intros W2 c2 _ HP; right; exists res; split; [exact Hcf|];
      split; [unfold HEAD in *; lia | exact HP] ].
  + intros ms2 md2 H3 HINV HLR Hms2 HG2.
    exact (KLOOP ly' S' W' mem' md' res kd ms2 md2 H3 HY HINV HLR Hms2 HG2).
  + intros ms2 md2 H3 HINV HER Hms2 HG2.
    exact (KTAIL ly' S' W' mem' md' res kd ms2 md2 H3 HY HINV HER Hms2 HG2).
Qed.
(* ==== END the entry block ==== *)

(* ---------------------------------------------------------------------------------------------------------- *)
(* 13. encode_proof: S0's encode_spec. The entry and the fuzz_malloc call are encR_entry (its refused arm is     *)
(*     encR_null_arm, its len < 3 dispatch encR_dispatch); len >= 3 runs the loop from round 0 (encR_loop_closed, *)
(*     each round encR_round_step) and leaves it at 0x845dc (encR_loop_exit); 0 < len < 3 goes to the tail at     *)
(*     0x845e0 (encR_tail). The NUL and the epilogue are encR_nul, inside those.                                  *)
(* ---------------------------------------------------------------------------------------------------------- *)
Theorem encode_proof : encode_spec B tfibsegs.
Proof.
unfold encode_spec.
intros ly S U W regs mem md ch data len bs live peak cnt fail
  HPRE HH _ H10 H11 HBS HBSL HLN HZB (HDLO & HDHI) HDB0 HGL HEV HLV HLIVE HCNT.
apply (encR_entry ly S U W regs mem md ch data len bs live peak cnt fail
  HPRE HH H10 H11 HBS HBSL HLN HZB HDLO HDHI HDB0 HGL HEV HLV HLIVE HCNT).
- (* len >= 3: the loop from round 0, left at 0x845dc *)
  intros lyc Sc Wc memc mdc q kd ms md' H3 HY HINV HR Hms HPRE0.
  destruct HY as (HLN' & HBS' & HBSL' & HDLO' & HDHI' & HARUc & HHEADS & HQB & HAB & HQ16 & HDB & HRBc
    & HGLOBc & HTABc & HRATc & HDATc & HKEEPc & HFRAMEc & HSP0 & HRA0).
  rewrite Hms.
  eapply encR_loop_closed with (r := 0).
  all: first
    [ solve [eassumption] | solve [lia]
    | intros ms' md'' R HR1 HR2 HINV' HX Hms' HPRE';
      eapply encR_loop_exit with (R := R); first [eassumption | lia] ].
- (* 0 < len < 3: the tail from R = 0 *)
  intros lyc Sc Wc memc mdc q kd ms md' Hl HY HINV HX Hms HPRE0.
  destruct HY as (HLN' & HBS' & HBSL' & HDLO' & HDHI' & HARUc & HHEADS & HQB & HAB & HQ16 & HDB & HRBc
    & HGLOBc & HTABc & HRATc & HDATc & HKEEPc & HFRAMEc & HSP0 & HRA0).
  eapply encR_tail with (R := 0); first [eassumption | lia].
Qed.

End W.
