(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths, module names and numbers changed; 4559 of its 4627 lines of code are new or changed and 1012 lines of the source are left out. *)
(* preset_base64_decode (fuzz_state.asan-ubsan, image B, 0x84c4c .. 0x84e70): the walk of decode_spec, ported from image
   A's closed walk (lib/A/FSW_dec_*.v) over B's kit (lib/B FSW_K / FSW_K3 / FSW_ret / FSW_rres / FSW_writer_tbl).
   B's code differs from A's by the 128-byte frame (lenp spilled at b + 8, ~q at b + 16, the 13 saved words at
   b + 24 .. b + 120, b = sp - 128), the register allocation (s0 = -1, s1 = q, s2 = text cursor, s3 = g_b64,
   s4 = shadow base, s5 = n, s6 = acc, s7 = bits, s8 = pad, s9 = s2 - 1, s10 = 61, s11 = the whitespace mask) and six
   UBSan guards; the engine decides the loop's back-edge, '=' and store guards from the atom facts of the loop states,
   the `beqz s2` after fuzz_malloc is decided by a condition (text >= 4096), the two lenp guards by lenp's atom fact.
   Only decode_spec's real-stack placement of *lenp is proved. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YI04 YI16 YK06 YO09 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import FSH_Base FSH_Rt FSPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp WriterValue PjStruct.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSH_Fn_reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree.
Import ListNotations.
Local Open Scope Z_scope.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSW_K YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSW_K YB1v FSH_Rt FSH_Base FSH_Fn_alloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import FSH_Fn_writer.

(* the walk's environment, in image A's walk's import order *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1w.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
FSH_Base FSH_Rt FSPstat FSH_Fn_alloc FSH_Fn_writer FSW_K FSW_K3 FSW_ret FSW_rres FSW_strkit FSW_writer_tbl.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSW_writer_model.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpecFacts.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".

(* ================= the shared definitions (port of lib/A/FSW_dec_defs.v) ================= *)
Definition DEC_F : Z := 128.
Definition DEC_RA_STRLEN : Z := 0x84c9c.
Definition DEC_RA_MALLOC : Z := 0x84cb0.
Definition DEC_HEAD : Z := 0x84cf8.
Definition DEC_RA_MEMCHR : Z := 0x84d50.
Definition DEC_RA_FREE : Z := 0x84dd8.
Definition DEC_WSMASK : Z := 4294977024.
Definition DEC_M1 : Z := 18446744073709551615.

(* the frame, b = entry sp - 128: lenp at b + 8, ~q at b + 16, the entry value of the j-th register of dec_saved at
   b + 24 + 8 j *)
Definition dec_saved : list (bv 5) := [27; 26; 25; 24; 23; 22; 21; 20; 19; 18; 9; 8; 1]%bv.
Definition dec_frame_ok (W : world tfibsegs) (mem : word -> option byte) (b : Z) (regs0 : bvmap 5 word) : Prop :=
  forall j r, nth_error dec_saved j = Some r ->
    val_mem tfibsegs (mrestrict (w_H W) mem) (b + 24 + 8 * Z.of_nat j) 8 (bv_unsigned (getr regs0 r)).
Definition dec_lenp_slot (W : world tfibsegs) (mem : word -> option byte) (b lenp : Z) : Prop :=
  val_mem tfibsegs (mrestrict (w_H W) mem) (b + 8) 8 lenp.
Definition dec_nq_slot (W : world tfibsegs) (mem : word -> option byte) (b q : Z) : Prop :=
  val_mem tfibsegs (mrestrict (w_H W) mem) (b + 16) 8 (DEC_M1 - q).

Record DE := mkDE {
  d_ly : alayout; d_S : astate; d_U : list (Z * Z); d_W : world tfibsegs; d_regs : bvmap 5 word;
  d_mem : word -> option byte; d_md : Model; d_ch : list (Z * Z * Z);
  d_ot : Z; d_text : Z; d_lenp : Z; d_tb : list Z; d_live : Z; d_peak : Z; d_cnt : Z; d_fail : Z; d_v : Z;
  d_FP : list (Z * Z) }.
Definition d_sp (d : DE) : Z := spZ (d_regs d).
Definition d_STKJ (d : DE) : Z := STK_preset_base64_decode + (d_ot d - d_sp d).
Definition d_n (d : DE) : Z := dec_size (d_tb d).

Section D. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* decode_spec's premises (the real-stack placement of *lenp) *)
Definition dec_entry_ok (d : DE) : Prop :=
  let ly := d_ly d in let S := d_S d in let U := d_U d in let W := d_W d in let regs := d_regs d in
  let mem := d_mem d in let tb := d_tb d in let text := d_text d in let lenp := d_lenp d in
  fpreU tfibsegs B STK_preset_base64_decode ly S U W regs mem (d_md d) (d_ch d) /\ fs_heads B ly S U /\
  Z.of_nat (length (frames S)) <= FRL_CRT_CALLEE /\
  getr regs 10 = w64 text /\ getr regs 11 = w64 lenp /\
  cstr_ok tfibsegs W mem text tb /\ wsrc_kept B tfibsegs ly S U W mem 0 text (tb ++ [0]) /\
  WriterSpec.bytes_ok tb /\ Z.of_nat (length tb) <= 2 ^ 28 /\
  lenp mod 8 = 0 /\
  val_mem tfibsegs (rdW W mem) lenp 8 (d_v d) /\ 0 <= d_v d < 2 ^ 64 /\
  (lenp + 8 <= text \/ text + Z.of_nat (length tb) + 1 <= lenp) /\
  fs_glob tfibsegs W mem (d_live d) (d_peak d) (d_cnt d) (d_fail d) /\
  st_nev S + dec_ev tb <= EV_MAX /\ blocks_bytes S + (dec_size tb + HEAD) <= LIVE_MAX /\
  d_live d + dec_size tb < 2 ^ 64 /\ d_cnt d + 1 < 2 ^ 64 /\
  (d_FP d = FS_PSTAT_FP /\ spZ regs <= lenp /\ lenp + 8 <= d_ot d /\ d_ot d mod 16 = 0 /\ d_ot d <= ly_top ly /\
   (forall a, spZ regs <= a < d_ot d -> apresent (w_H W) mem a) /\
   (exists chl, achain ly (aview tfibsegs (w_H W) (unpoison U mem)) (spZ regs) lenp chl)).

Definition dec_J (d : DE) (lyc : alayout) (Sc : astate) (Wc : world tfibsegs) (Uc : list (Z * Z))
    (memc : word -> option byte) (mdc : Model) (k : Z) : Prop :=
  ajournal tfibsegs B (d_STKJ d) (d_ot d) (d_FP d) (d_ly d) (d_S d) (d_W d) (unpoison (d_U d) (d_mem d)) (d_md d) []
    lyc Sc Wc (unpoison Uc memc) mdc k.

Definition dec_kept (d : DE) (Wc : world tfibsegs) (memc : word -> option byte) : Prop :=
  val_mem tfibsegs (rdW Wc memc) (d_lenp d) 8 (d_v d) /\
  wkeep tfibsegs (d_W d) Wc (d_mem d) memc (d_sp d) (d_ot d) (d_lenp d) 8 /\
  cstr_ok tfibsegs Wc memc (d_text d) (d_tb d) /\
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H Wc) memc).

(* the loop head 0x84cf8 *)
Definition dec_head (d : DE) (q : Z) (i : nat) (six : list Z) (pad acc : Z)
    (Wc : world tfibsegs) (lyc : alayout) (Sc : astate) (Uc : list (Z * Z)) (regsc : bvmap 5 word)
    (memc : word -> option byte) (mdc : Model) (k : Z) : Prop :=
  let tb := d_tb d in let text := d_text d in let n := Z.of_nat (length (WriterSpec.six_bytes six)) in
  dec_J d lyc Sc Wc Uc memc mdc k /\ ARU tfibsegs B lyc Sc Uc Wc memc mdc /\
  k = 1 /\ Uc = d_U d ++ [(q - HEAD, HEAD)] /\ fs_heads B lyc Sc Uc /\
  ablocks B lyc Sc = ablocks B (d_ly d) (d_S d) ++ [(q - HEAD, d_n d + HEAD)] /\
  4096 + HEAD <= q /\ fs_rblock tfibsegs B lyc Sc Wc memc q (d_n d) /\
  range_addressable (aview tfibsegs (w_H Wc) memc) SHADOW_OFF q (d_n d) /\
  d_cnt d <> d_fail d /\
  fs_glob tfibsegs Wc memc (d_live d + d_n d) (Z.max (d_peak d) (d_live d + d_n d)) (d_cnt d + 1) (d_fail d) /\
  spZ regsc = d_sp d - DEC_F /\ getr regsc 3 = getr (d_regs d) 3 /\ getr regsc 4 = getr (d_regs d) 4 /\
  getr regsc 8 = w64 DEC_M1 /\ getr regsc 9 = w64 q /\
  getr regsc 18 = w64 (text + Z.of_nat i) /\ getr regsc 19 = w64 G_B64 /\ getr regsc 20 = w64 SHADOW_OFF /\
  getr regsc 21 = w64 n /\ getr regsc 22 = w64 acc /\ 0 <= acc < 2 ^ 64 /\
  getr regsc 23 = w64 (6 * Z.of_nat (length six) mod 8) /\ getr regsc 24 = w64 pad /\
  getr regsc 25 = w64 (text + Z.of_nat i - 1) /\ getr regsc 26 = w64 61 /\ getr regsc 27 = w64 DEC_WSMASK /\
  dec_frame_ok Wc memc (d_sp d - DEC_F) (d_regs d) /\ dec_lenp_slot Wc memc (d_sp d - DEC_F) (d_lenp d) /\
  dec_nq_slot Wc memc (d_sp d - DEC_F) q /\
  dec_kept d Wc memc /\ zbytes_at tfibsegs Wc memc q (WriterSpec.six_bytes six) /\
  (i <= length tb)%nat /\ 0 <= pad <= Z.of_nat i /\ (length six <= i)%nat /\
  Forall (fun x => 0 <= x < 64) six /\ acc mod 64 = last six 0 /\
  WriterSpec.b64_dec tb =
    match WriterSpec.b64_scan pad six (skipn i tb) with
    | Some (six', pad') => if (pad' <=? 2) && WriterSpec.six_tail_ok six' then Some (WriterSpec.six_bytes six') else None
    | None => None
    end.

(* the call of fuzz_free on a refused text (pc A_fuzz_free, ra 0x84dd8, a0 = q, s0 = -1) *)
Definition dec_at_free (d : DE) (q : Z) (Wc : world tfibsegs) (lyc : alayout) (Sc : astate) (Uc : list (Z * Z))
    (regsc : bvmap 5 word) (memc : word -> option byte) (mdc : Model) (k : Z) : Prop :=
  dec_J d lyc Sc Wc Uc memc mdc k /\ ARU tfibsegs B lyc Sc Uc Wc memc mdc /\
  k = 1 /\ Uc = d_U d ++ [(q - HEAD, HEAD)] /\ fs_heads B lyc Sc Uc /\
  ablocks B lyc Sc = ablocks B (d_ly d) (d_S d) ++ [(q - HEAD, d_n d + HEAD)] /\
  4096 + HEAD <= q /\ fs_rblock tfibsegs B lyc Sc Wc memc q (d_n d) /\
  d_cnt d <> d_fail d /\ WriterSpec.b64_dec (d_tb d) = None /\
  fs_glob tfibsegs Wc memc (d_live d + d_n d) (Z.max (d_peak d) (d_live d + d_n d)) (d_cnt d + 1) (d_fail d) /\
  getr regsc 10 = w64 q /\ getr regsc 1 = w64 DEC_RA_FREE /\
  spZ regsc = d_sp d - DEC_F /\ getr regsc 3 = getr (d_regs d) 3 /\ getr regsc 4 = getr (d_regs d) 4 /\
  getr regsc 8 = w64 DEC_M1 /\
  dec_frame_ok Wc memc (d_sp d - DEC_F) (d_regs d) /\ dec_lenp_slot Wc memc (d_sp d - DEC_F) (d_lenp d) /\
  dec_kept d Wc memc.

Definition dec_post (d : DE) : world tfibsegs -> config -> Prop :=
  let ly := d_ly d in let S := d_S d in let U := d_U d in let W := d_W d in let regs := d_regs d in
  let mem := d_mem d in let md := d_md d in let tb := d_tb d in let lenp := d_lenp d in
  let live := d_live d in let peak := d_peak d in let cnt := d_cnt d in let fail := d_fail d in
  fun W' c' =>
    (cnt = fail /\
     fpostU tfibsegs B (d_STKJ d) (d_ot d) (d_FP d) regs ly S U W mem md 0 U
       (fun ly' S' W' regs' mem' md' =>
          getr regs' 10 = w64 0 /\ ablocks B ly' S' = ablocks B ly S /\
          wkeep tfibsegs W W' mem mem' (spZ regs) (d_ot d) lenp 8 /\
          val_mem tfibsegs (rdW W' mem') lenp 8 (d_v d) /\
          fs_glob tfibsegs W' mem' live peak ((cnt + 1) mod 2 ^ 64) SIZE_MAXZ) W' c')
    \/
    (cnt <> fail /\ WriterSpec.b64_dec tb = None /\
     fpostU tfibsegs B (d_STKJ d) (d_ot d) (d_FP d) regs ly S U W mem md EV_preset_base64_decode U
       (fun ly' S' W' regs' mem' md' =>
          getr regs' 10 = w64 0 /\ ablocks B ly' S' = ablocks B ly S /\
          wkeep tfibsegs W W' mem mem' (spZ regs) (d_ot d) lenp 8 /\
          val_mem tfibsegs (rdW W' mem') lenp 8 (d_v d) /\
          fs_glob tfibsegs W' mem' live (Z.max peak (live + dec_size tb)) ((cnt + 1) mod 2 ^ 64) fail) W' c')
    \/
    (exists q out, cnt <> fail /\ WriterSpec.b64_dec tb = Some out /\ q <> 0 /\
     fpostU tfibsegs B (d_STKJ d) (d_ot d) (d_FP d) regs ly S U W mem md 1 (U ++ [(q - HEAD, HEAD)])
       (fun ly' S' W' regs' mem' md' =>
          getr regs' 10 = w64 q /\ 4096 + HEAD <= q /\
          ablocks B ly' S' = ablocks B ly S ++ [(q - HEAD, dec_size tb + HEAD)] /\
          fs_rblock tfibsegs B ly' S' W' mem' q (dec_size tb) /\
          zbytes_at tfibsegs W' mem' q out /\
          wkeep tfibsegs W W' mem mem' (spZ regs) (d_ot d) lenp 8 /\
          val_mem tfibsegs (rdW W' mem') lenp 8 (Z.of_nat (length out)) /\
          cstr_ok tfibsegs W' mem' (d_text d) tb /\
          fs_glob tfibsegs W' mem' (live + dec_size tb) (Z.max peak (live + dec_size tb)) ((cnt + 1) mod 2 ^ 64) fail)
       W' c').

Definition dec_stage_entry : Prop :=
  forall d, dec_entry_ok d ->
  (forall Wc lyc Sc Uc regsc memc mdc k q, dec_head d q 0 [] 0 0 Wc lyc Sc Uc regsc memc mdc k ->
     SRr tfibsegs Wc (mkCfg (YK11.mkst regsc (Z_to_bv 64 DEC_HEAD) memc (YK11.seg_rom tfibsegs)) mdc) (dec_post d)) ->
  SRr tfibsegs (d_W d) (cfg_at tfibsegs A_preset_base64_decode (d_regs d) (d_mem d) (d_md d)) (dec_post d).
Definition dec_stage_loop : Prop :=
  forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k, dec_entry_ok d ->
  dec_head d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  (forall W3 ly3 S3 U3 regs3 mem3 md3 k3, dec_at_free d q W3 ly3 S3 U3 regs3 mem3 md3 k3 ->
     SRr tfibsegs W3 (cfg_at tfibsegs A_fuzz_free regs3 mem3 md3) (dec_post d)) ->
  SRr tfibsegs Wc (mkCfg (YK11.mkst regsc (Z_to_bv 64 DEC_HEAD) memc (YK11.seg_rom tfibsegs)) mdc) (dec_post d).
Definition dec_stage_free : Prop :=
  forall d q W3 ly3 S3 U3 regs3 mem3 md3 k3, dec_entry_ok d ->
  dec_at_free d q W3 ly3 S3 U3 regs3 mem3 md3 k3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs A_fuzz_free regs3 mem3 md3) (dec_post d).
End D.

(* ================= the composition (port of lib/A/FSW_dec_top.v) ================= *)
Section T. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

Lemma dec_walk : dec_stage_entry B -> dec_stage_loop B -> dec_stage_free B ->
  forall d, dec_entry_ok B d ->
  SRr tfibsegs (d_W d) (cfg_at tfibsegs A_preset_base64_decode (d_regs d) (d_mem d) (d_md d)) (dec_post B d).
Proof.
intros HE HL HF d Hd. apply (HE d Hd).
intros Wc lyc Sc Uc regsc memc mdc k q Hh. apply (HL d q 0%nat [] 0 0 Wc lyc Sc Uc regsc memc mdc k Hd Hh).
intros W3 ly3 S3 U3 regs3 mem3 md3 k3 Hf. exact (HF d q W3 ly3 S3 U3 regs3 mem3 md3 k3 Hd Hf).
Qed.

Theorem decode_of_stages : dec_stage_entry B -> dec_stage_loop B -> dec_stage_free B ->
  decode_spec B tfibsegs.
Proof.
intros HE HL HF ly S U W regs mem md ch ot text lenp tb live peak cnt fail v HPRE HH HFR H10 H11 HCS HWS HBO HLEN
  Hl8 Hspl Hlot Hot16 Hottop HCH HPRS HV Hv HDJ HG HEV HLV HLIVE HCNT.
assert (Hd : dec_entry_ok B (mkDE ly S U W regs mem md ch ot text lenp tb live peak cnt fail v FS_PSTAT_FP)).
{ unfold dec_entry_ok; cbn [d_ly d_S d_U d_W d_regs d_mem d_md d_ch d_ot d_text d_lenp d_tb d_live d_peak d_cnt
    d_fail d_v d_FP].
  repeat match goal with |- _ /\ _ => split end; first [assumption | reflexivity | lia]. }
eapply SRr_mono; [exact (dec_walk HE HL HF _ Hd)|].
cbv beta. intros W' c' _ HP.
unfold dec_post, d_STKJ, d_sp in HP. cbn [d_ly d_S d_U d_W d_regs d_mem d_md d_ch d_ot d_text d_lenp d_tb d_live d_peak
  d_cnt d_fail d_v d_FP] in HP.
unfold wpost. exact HP.
Qed.
End T.

(* ================= stage F: fuzz_free on a refused text and the return (port of lib/A/FSW_dec_F.v) ================= *)
Lemma decF_snoc_notin : forall {X Y : Type} (R : Y -> Y -> Prop) (f : X -> Y) (l : list X) (x : X),
  pairwise R (map f (l ++ [x])) -> ~ R (f x) (f x) -> ~ In x l.
Proof.
intros X Y R f l. induction l as [|y l IH]; intros x HP HR Hin; [destruct Hin|].
cbn [app map pairwise] in HP. destruct HP as [HF HP].
destruct Hin as [<-|Hin].
- apply HR. rewrite Forall_forall in HF. apply HF. rewrite map_app. apply in_or_app. right. left. reflexivity.
- exact (IH x HP HR Hin).
Qed.
Lemma decF_snoc_split : forall {X : Type} (l1 l2 l : list X) (x : X),
  l1 ++ x :: l2 = l ++ [x] -> ~ In x l -> l1 = l /\ l2 = [].
Proof.
intros X l1 l2 l x. revert l1 l. induction l2 as [|y l2' _] using rev_ind; intros l1 l E Hn.
- apply app_inj_tail in E as [E _]. split; [exact E | reflexivity].
- exfalso. rewrite app_comm_cons, app_assoc in E. apply app_inj_tail in E as [E _]. apply Hn. rewrite <- E.
  apply in_or_app. right. left. reflexivity.
Qed.

(* the last PT_LOAD of fs.asan-ubsan, [0xa1000, 0x5fd000) (tfibsegs's fourth segment), holds fuzz/alloc.c's statics *)
Lemma decF_img : forall a, 659456 <= a < 6279168 -> in_img tfibsegs a.
Proof.
intros a Ha. unfold in_img.
assert (H : option_map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) (nth_error tfibsegs 3) = Some (659456, 5619712))
  by (vm_compute; reflexivity).
destruct (nth_error tfibsegs 3) as [sg|] eqn:E; [|discriminate H].
exists sg. split; [exact (nth_error_In _ _ E)|].
cbn [option_map] in H. injection H as H1 H2. lia.
Qed.

Lemma decF_wf0 : forall f, 0 <= f -> regions_wf (fsT_ret_regions f [] []) = true.
Proof.
intros f Hf. unfold fsT_ret_regions. cbn [app regions_wf].
replace (region_wf fs_got_region) with true by (vm_compute; reflexivity).
replace (region_wf (fs_bcell_region 32)) with true by (vm_compute; reflexivity).
unfold region_wf, fstk_ret. cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks forallb].
rewrite (proj2 (Z.leb_le 0 f) Hf), (proj2 (Z.leb_le f f) (Z.le_refl f)), (proj2 (Z.leb_le 0 0) (Z.le_refl 0)).
rewrite !orb_true_r. reflexivity.
Qed.

Ltac decF_split H :=
  lazymatch type of H with
  | _ /\ _ => let a := fresh "HD" in destruct H as [a H]; decF_split H
  | _ => idtac
  end.

(* the resumed frame at 0x84dd8: word 3 + j (offset 24 + 8 j) holds the entry value of dec_saved's j-th register,
   extra atom 33 + j of the env Ereg regs (fs_extraT ++ decF_xs) *)
Definition decF_cs : list YP09.chunk :=
  map (fun j => YP09.mkChunk (24 + 8 * Z.of_nat j) (CVal 8 (SOff (33 + j) 0))) (seq 0 13).
Definition decF_xs (regs0 : bvmap 5 word) : list word := map (YK11.getr regs0) dec_saved.

(* s0 = -1 at the fuzz_free call: not 8-aligned, so the callee's frame chain is empty (achain's first arm) *)
Lemma achain_m1 : forall {rc : YM05.RunCeil} ly rd sp, achain ly rd sp DEC_M1 [].
Proof. intros rc ly rd sp. left. split; [right; right; unfold DEC_M1; lia | reflexivity]. Qed.

Section F. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HSS : FsShadowSyms B.
Hypothesis HFREE : fuzz_free_spec tfibsegs B.

Lemma dec_free_stage : dec_stage_free B.
Proof.
unfold dec_stage_free.
intros d q W3 ly3 S3 U3 regs3 mem3 md3 k3 HD HAF.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HSS as [HGOT HCELL].
assert (HHEAD : HEAD = 16) by reflexivity.
assert (HDECF : DEC_F = 128) by reflexivity.
assert (HSTKd : STK_preset_base64_decode = ltac:(let v := eval vm_compute in STK_preset_base64_decode in exact v)) by (vm_compute; reflexivity).
assert (HSTKf : STK_fuzz_free = ltac:(let v := eval vm_compute in STK_fuzz_free in exact v)) by (vm_compute; reflexivity).
assert (Hdsp : d_sp d = spZ (d_regs d)) by reflexivity.
assert (HSTKJ : d_STKJ d = STK_preset_base64_decode + (d_ot d - spZ (d_regs d))) by reflexivity.
assert (HEVd : EV_preset_base64_decode = 2) by reflexivity.
(* ---- the entry facts ---- *)
unfold dec_entry_ok in HD. cbv zeta in HD. decF_split HD.
lazymatch goal with Hx : fpreU tfibsegs B STK_preset_base64_decode _ _ _ _ _ _ _ _ |- _ => rename Hx into HPRE end.
lazymatch goal with Hx : fs_glob tfibsegs (d_W d) (d_mem d) _ _ _ _ |- _ => rename Hx into HGLOB0 end.
lazymatch goal with Hx : d_FP d = FS_PSTAT_FP |- _ => rename Hx into HFPd end.
lazymatch goal with Hx : forall a, spZ (d_regs d) <= a < d_ot d -> apresent _ _ a |- _ => rename Hx into HPR end.
destruct HPRE as (HPREU & _).
pose proof HPREU as (HAP & _ & _).
pose proof HAP as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & _ & _ & _).
pose proof Hstk as (Hsp16 & _ & Hceil & Hslo & Hshi & H47 & _ & Htop & Htop2).
pose proof HGLOB0 as (_ & _ & _ & _ & Hlive0 & _ & Hcnt0 & _).
assert (Hspot : spZ (d_regs d) <= d_ot d) by lia.
assert (Hot47 : d_ot d <= 2 ^ 47) by lia.
(* ---- the call site ---- *)
unfold dec_at_free in HAF.
destruct HAF as (HJ & HARU3 & -> & EU3 & HH3 & HAB3 & Hq & HRB & Hcf & Hdec & HG3 & R10 & R1 & Rsp & R3 & R4 & R8 & HFR
  & HLS & HKEPT).
unfold dec_J in HJ.
pose proof HJ as (HAR3 & _ & _ & _ & _ & _ & Hnev3 & _).
pose proof HRB as (_ & _ & Hn0 & _).
assert (Hra3 : raZ regs3 = DEC_RA_FREE) by (unfold raZ; rewrite R1; unfold w64; apply wz; unfold DEC_RA_FREE; lia).
assert (HFPRE : fpreU tfibsegs B STK_fuzz_free ly3 S3 U3 W3 regs3 mem3 md3 []).
{ apply (fsw_fpreU_atFP B (d_STKJ d) (d_ot d) (d_FP d) (d_ly d) (d_S d) U3 (d_W d) (unpoison (d_U d) (d_mem d)) (d_md d) []
    ly3 S3 W3 mem3 md3 1 regs3 STK_fuzz_free (spZ regs3 - d_ot d) [] HJ HARU3 (proj2 (proj2 (proj2 HKEPT)))).
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - rewrite R1. apply YK0s.ret_ok_even. unfold w64. rewrite wz by (unfold DEC_RA_FREE; lia). reflexivity.
  - rewrite Hra3. unfold DEC_RA_FREE. lia.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp.
  - replace (s0Z regs3) with DEC_M1 by (unfold s0Z; rewrite R8; unfold w64; rewrite wz by (unfold DEC_M1; lia); reflexivity).
    apply achain_m1. }
assert (HEVt : dec_ev (d_tb d) = 2) by (unfold dec_ev; rewrite Hdec; reflexivity).
assert (HNEV : st_nev S3 + 1 <= EV_MAX) by lia.
(* ---- the call: fuzz_free_spec's p <> 0 arm, U1 = d_U d, U2 = [] ---- *)
eapply SRr_bind.
{ apply (HFREE ly3 S3 U3 W3 regs3 mem3 md3 [] q (d_n d) (d_live d + d_n d) (Z.max (d_peak d) (d_live d + d_n d))
    (d_cnt d + 1) (d_fail d)).
  - exact R10.
  - exact HG3.
  - exact HH3.
  - right. split; [lia|]. exists (d_U d), []. split; [exact EU3|]. split; [exact HFPRE|]. split; [exact HRB | lia].
  - intros _. exact HNEV. }
intros W4 c4 Hle4 HR.
destruct HR as [(Hq0 & _) | (_ & U1 & U2 & EU & HPOST)]; [lia|].
unfold apost_baseU, fpostU in HPOST.
destruct HPOST as (ly4 & S4 & regs4 & mem4 & md4 & -> & HJc & OK4 & PO4 & HP4 & (Hsplit & _ & HG4)).
assert (HXU : ~ In (q - HEAD, HEAD) (d_U d)).
{ pose proof HARU3 as (_ & (_ & PWU) & _). rewrite EU3 in PWU.
  apply (decF_snoc_notin zdisjoint (fun y => y)); [rewrite map_id; exact PWU | cbv beta; unfold zdisjoint; cbn [fst snd]; lia]. }
destruct (decF_snoc_split U1 U2 (d_U d) (q - HEAD, HEAD) ltac:(rewrite <- EU; exact EU3) HXU) as [-> ->].
rewrite app_nil_r in HJc, OK4, PO4.
assert (HXB : ~ In (q - HEAD, d_n d + HEAD) (ablocks B (d_ly d) (d_S d))).
{ destruct (al_blocks _ _ LAWS ly3 S3 W3 (unpoison U3 mem3) md3 (q - HEAD) (d_n d + HEAD) HAR3
    ltac:(rewrite HAB3; apply in_or_app; right; left; reflexivity)) as (_ & _ & _ & _ & _ & PWB & _).
  rewrite HAB3 in PWB.
  apply (decF_snoc_notin zdisjoint (fun b => (fst b, req_size (snd b))) _ _ PWB).
  cbv beta. unfold zdisjoint. cbn [fst snd].
  pose proof (req_size_pos (d_n d + HEAD) ltac:(lia)) as (RQ1 & _). lia. }
assert (FPSUB : fsw_fp_sub B (d_ly d) (d_S d) ly3 S3 [] (d_FP d) (FS_PSTAT_FP ++ ablocks_fp [(q - HEAD, d_n d + HEAD)])).
{ intros a (r & Hr & Ha). apply in_app_or in Hr as [Hr|Hr].
  - right. right. left. split.
    + exists r. split; [|exact Ha]. rewrite HFPd. exact Hr.
    + unfold FS_PSTAT_FP in Hr. cbn [In] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Ha; apply decF_img; lia.
  - right. left. exists (q - HEAD), (d_n d + HEAD).
    split; [rewrite HAB3; apply in_or_app; right; left; reflexivity|].
    split; [exact HXB|]. cbn [ablocks_fp map In fst snd] in Hr. destruct Hr as [<-|[]]. cbn [fst snd] in Ha. exact Ha. }
(* ---- the resume at DEC_RA_FREE ---- *)
assert (HE2a : forall xs, bv_unsigned (ew (Ereg regs4 (fs_extraT ++ xs)) 2) = spZ regs4)
  by (intros xs; rewrite (ew_Ereg_nat regs4 (fs_extraT ++ xs) 2 2%bv eq_refl); reflexivity).
assert (Esp : YK11.getr regs4 2 = YK11.getr regs3 2) by exact (HP4 2 ltac:(unfold acallee_saved; lia)).
assert (Esp4 : spZ regs4 = spZ regs3) by (unfold spZ; rewrite Esp; reflexivity).
assert (HWF0 : regions_wf (fsT_ret_regions (d_ot d - spZ regs3) [] []) = true) by (apply decF_wf0; lia).
assert (HPD0 : pairwise_disjoint (Ereg regs4 (fs_extraT ++ [])) (fsT_ret_regions (d_ot d - spZ regs3) [] [])).
{ apply pairwise_disjoint_of_extents.
  unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, extent_of_region.
  cbn [map app YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite HE2a, Esp4.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia]. }
destruct (fsw_after_callFPU_args B (d_STKJ d) (d_ot d) (d_FP d) [] (d_ly d) (d_S d) (d_U d) W3 (d_mem d) (d_md d) (d_W d)
  ly3 S3 U3 mem3 md3 1 STK_fuzz_free (FS_PSTAT_FP ++ ablocks_fp [(q - HEAD, d_n d + HEAD)]) (d_ot d - spZ regs3) regs3
  ly4 S4 (d_U d) W4 regs4 mem4 md4 1 [] [] [] [] DEC_RA_FREE HGOT HCELL HJ HARU3 HJc FPSUB OK4 PO4 HP4
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HWF0 ltac:(constructor) ltac:(constructor) ltac:(constructor) HPD0
  ltac:(first [exact I | constructor | cbn; exact I]))
  as (HJ4 & HARU4 & _).
pose proof (ajournal_sub_init tfibsegs B (d_STKJ d) (d_ot d) (d_FP d) (d_ly d) (d_S d) (d_W d) (unpoison (d_U d) (d_mem d))
  (d_md d) [] ly4 S4 W4 (unpoison (d_U d) mem4) md4 (1 + 1) STK_preset_base64_decode (spZ (d_regs d)) []
  (spZ (d_regs d) - d_ot d) HJ4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HJr.
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & F1c & _).
assert (KEEP4 : forall a, alloc_ceiling <= a < 2 ^ 64 -> spZ regs3 <= a ->
  mbyte tfibsegs (mrestrict (w_H W4) mem4) a = mbyte tfibsegs (mrestrict (w_H W3) mem3) a).
{ intros a Ha Ha3. apply (mbyte_of_aview tfibsegs).
  rewrite <- (fsw_aview_unpoison_high B ly4 S4 (d_U d) W4 mem4 md4 a HARU4) by lia.
  rewrite <- (fsw_aview_unpoison_high B ly3 S3 U3 W3 mem3 md3 a HARU3) by lia.
  apply F1c; lia. }
assert (HS : st_ok tfibsegs (Ereg regs4 (fs_extraT ++ decF_xs (d_regs d))) (fss_retT DEC_RA_FREE 128 decF_cs [] [])
  (restrict (w_H W4) (YK11.mkst regs4 (Z_to_bv 64 DEC_RA_FREE) mem4 (YK11.seg_rom tfibsegs)))).
{ apply (fsw_resume_after_rtU_args_chunks B STK_preset_base64_decode (spZ (d_regs d)) [] ly4 S4 W4 (unpoison (d_U d) mem4)
    md4 [] ly4 S4 (d_U d) W4 mem4 md4 0 regs4 128 (decF_xs (d_regs d)) decF_cs [] [] DEC_RA_FREE HGOT HCELL HJr HARU4).
  - lia.
  - lia.
  - lia.
  - reflexivity.
  - vm_compute. reflexivity.
  - apply Forall_forall. intros c Hc. unfold decF_cs in Hc. apply in_map_iff in Hc as (j & <- & Hj). apply in_seq in Hj.
    destruct (nth_error dec_saved j) as [r|] eqn:Ej; [|apply nth_error_None in Ej; cbn [length dec_saved] in Ej; lia].
    pose proof (HFR j r Ej) as V.
    apply (chunk_ok_val tfibsegs _ _ _ _ 8 _ (bv_unsigned (YK11.getr (d_regs d) r))).
    + rewrite Z_to_bv_bv_unsigned. change (33 + j)%nat with (32 + S j)%nat. rewrite fsw_extra_atom.
      cbn [nth fs_extraT app]. unfold decF_xs. apply nth_error_nth. rewrite nth_error_map, Ej. reflexivity.
    + pose proof (u64_range (YK11.getr (d_regs d) r)). change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    + cbn. lia.
    + intros i Hi. cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in Hi.
      rewrite KEEP4 by lia.
      replace (spZ (d_regs d) - 128 + (24 + 8 * Z.of_nat j) + Z.of_nat i)
        with (d_sp d - DEC_F + 24 + 8 * Z.of_nat j + Z.of_nat i) by lia.
      exact (V i Hi).
  - constructor.
  - apply pairwise_disjoint_of_extents.
    unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, extent_of_region.
    cbn [map app YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite HE2a, Esp4.
    unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia].
  - first [exact I | constructor | cbn; exact I]. }
(* ---- the run 0x84dd8 .. 0x84e18 and the return ---- *)
rewrite R1. unfold w64.
fsw_aj_runU fsw_wr_tbl_ok HS HJ4 HARU4.
- cbv [fss_retT fsT_ret_regions ss_mem app].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ (d_regs d) - 128 - d_ot d);
    [reflexivity | rewrite HE2a, Esp4; lia | cbv [fstk_ret YP09.r_wlo]; lia | cbv [fstk_ret YP09.r_whi]; lia |].
  apply awr_ok_cons_ro; [cbv [fs_got_region YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_cons_ro; [cbv [fs_bcell_region YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_nil.
- pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres5 & _).
  assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (d_regs d) - 128 <= a < spZ (d_regs d)) ->
    ms_mem ms (Z_to_bv 64 a) = mem4 (Z_to_bv 64 a)).
  { intros a Ha Hna. apply HF. rewrite (wz a Ha). intros (r & Hin & Hr).
    cbv [fss_retT fsT_ret_regions ss_mem app In] in Hin.
    destruct Hin as [<-|[<-|[<-|[]]]];
      cbv [fstk_ret fs_got_region fs_bcell_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      try (rewrite HE2a, Esp4 in Hr); lia. }
  assert (MWE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (d_regs d) - 128 <= a < spZ (d_regs d)) ->
    mrestrict (w_H W4) (ms_mem ms) (Z_to_bv 64 a) = mrestrict (w_H W4) mem4 (Z_to_bv 64 a))
    by (intros a Ha Hna; unfold mrestrict; rewrite (MEQ a Ha Hna); reflexivity).
  assert (MB5 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (d_regs d) - 128 <= a < spZ (d_regs d)) ->
    mbyte tfibsegs (mrestrict (w_H W4) (ms_mem ms)) a = mbyte tfibsegs (mrestrict (w_H W4) mem4) a)
    by (intros a Ha Hna; unfold mbyte; rewrite (MWE a Ha Hna); reflexivity).
  assert (SB : same_below mem4 (ms_mem ms) alloc_ceiling) by (intros x Hx; apply MEQ; lia).
  eapply SRr_mono.
  2:{ intros W5 c5 _ HP5. unfold dec_post. cbv beta zeta. right. left.
      split; [exact Hcf|]. split; [exact Hdec|]. exact HP5. }
  eapply (fsw_retU B fsw_wr_tbl fsw_wr_tbl_ok).
  + exact HS.
  + vm_compute. reflexivity.
  + vm_compute. reflexivity.
  + rewrite (fsw_reg_extra (w_H W4) regs4 (fs_extraT ++ decF_xs (d_regs d)) _ ms 1%bv 13 HS
      ltac:(vm_compute; reflexivity)).
    cbn [nth app fs_extraT decF_xs map dec_saved]. exact Hra.
  + exact HJ4.
  + exact HARU4.
  + lazymatch type of HS with
    | st_ok _ _ ?ssf _ =>
      apply (fsw_preserved (w_H W4) _ ssf ms (d_regs d) (fun r : bv 5 => sr_get (ss_regs ssf) r) HS);
      [vm_compute; reflexivity|]
    end.
    intros r Hr; cbv [CALLEE_SAVED In] in Hr;
      repeat (destruct Hr as [<-|Hr]); [..|destruct Hr]; cbv beta;
      lazymatch goal with
      | |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e'
      end;
      first
      [ apply fsw_sp_back; rewrite HE2a, Esp4; lia
      | rewrite fsw_SOff0, (ew_Ereg_nat regs4 _ 3 3%bv eq_refl),
          (fsw_pres regs3 regs4 3%bv HP4 ltac:(unfold acallee_saved; change (bv_unsigned 3%bv) with 3; lia)), R3;
        reflexivity
      | rewrite fsw_SOff0, (ew_Ereg_nat regs4 _ 4 4%bv eq_refl),
          (fsw_pres regs3 regs4 4%bv HP4 ltac:(unfold acallee_saved; change (bv_unsigned 4%bv) with 4; lia)), R4;
        reflexivity
      | rewrite fsw_SOff0;
        lazymatch goal with
        | |- ew _ ?n = _ => let j := eval vm_compute in (n - 32)%nat in change n with (32 + j)%nat
        end;
        rewrite ew_Ereg_extra; reflexivity ].
  + intros mat5. cbv beta.
    split; [unfold w64; exact (fsw_reg_lit (w_H W4) _ _ ms 10%bv 0 HS ltac:(vm_compute; reflexivity) ltac:(lia))|].
    split.
    { destruct Hsplit as (l1 & l2 & E3 & E4). rewrite E4.
      destruct (decF_snoc_split l1 l2 (ablocks B (d_ly d) (d_S d)) (q - HEAD, d_n d + HEAD)
        ltac:(rewrite <- E3; exact HAB3) HXB) as [-> ->].
      apply app_nil_r. }
    split.
    { intros a Ha Hna. pose proof HKEPT as (_ & WK3 & _).
      destruct (WK3 a Ha Hna) as [WK3m _].
      split.
      - rewrite MB5 by lia. rewrite KEEP4 by lia. exact WK3m.
      - split; intros _; apply (apresent_writable tfibsegs).
        + apply (fsw_apresent_unpoison B ly4 S4 (d_U d) W4 (ms_mem ms) _ a HARU4); [lia|]. apply Hpres5. lia.
        + apply HPR; lia. }
    split.
    { pose proof HKEPT as (VL3 & _). intros i Hi.
      rewrite MB5 by lia. rewrite KEEP4 by lia. exact (VL3 i Hi). }
    pose proof HG4 as HG4'. replace (d_live d + d_n d - d_n d) with (d_live d) in HG4' by lia.
    rewrite Z.mod_small by lia.
    exact (fs_glob_below W4 mem4 (ms_mem ms) _ _ _ _ SB HG4').
Qed.
End F.

(* ================= stage E: entry -> strlen -> fuzz_malloc (port of lib/A/FSW_dec_E.v) ================= *)
(* the resume states after strlen (0x84c9c) and fuzz_malloc (0x84cb0): the 128-byte frame at atom 2 = sp - 128 with the
   13 saved words at offsets 24 .. 120; the saved registers the code changed before the calls (s4 = the shadow base,
   s0 = lenp, s2 = text, ra) are the extra atoms 33 .. 36 *)
Definition decE_xs (d : DE) : list word :=
  [getr (d_regs d) 20; getr (d_regs d) 8; getr (d_regs d) 18; getr (d_regs d) 1].
Definition decE_cs : list YP09.chunk :=
  [YP09.mkChunk 24 (CVal 8 (SOff 27 0)); YP09.mkChunk 32 (CVal 8 (SOff 26 0)); YP09.mkChunk 40 (CVal 8 (SOff 25 0));
   YP09.mkChunk 48 (CVal 8 (SOff 24 0)); YP09.mkChunk 56 (CVal 8 (SOff 23 0)); YP09.mkChunk 64 (CVal 8 (SOff 22 0));
   YP09.mkChunk 72 (CVal 8 (SOff 21 0)); YP09.mkChunk 80 (CVal 8 (SOff 33 0)); YP09.mkChunk 88 (CVal 8 (SOff 19 0));
   YP09.mkChunk 96 (CVal 8 (SOff 35 0)); YP09.mkChunk 104 (CVal 8 (SOff 9 0)); YP09.mkChunk 112 (CVal 8 (SOff 34 0));
   YP09.mkChunk 120 (CVal 8 (SOff 36 0))].
Definition decE_kregs : list (bv 5) := [9; 19; 21; 22; 23; 24; 25; 26; 27]%bv.

(* reading registers the engine left as SOff n z *)
Lemma decL_soff : forall E n z v, ew E n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + z < 2 ^ 64 ->
  sv_denot E (SOff n z) = w64 (v + z).
Proof.
intros E n z v Hn Hv Hz. apply bv_eq. rewrite denot_SOff, Hn. unfold w64.
rewrite (wz v Hv), (wz (v + z) Hz). apply zcanon_id. unfold M64. lia.
Qed.
Lemma decL_reg : forall {fx : YK11.FPState} (H : word -> bool) E ss ms (r : bv 5) e w,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = e -> sv_denot E e = w -> getr (ms_regs ms) r = w.
Proof. intros fx H E ss ms r e w HS He Hw. rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), He. exact Hw. Qed.

(* ~q = q xor -1 *)
Lemma decE_lxor_m1 : forall q, 0 <= q < 2 ^ 64 -> Z.lxor q 18446744073709551615 = 18446744073709551615 - q.
Proof.
intros q Hq.
assert (O : 18446744073709551615 = Z.ones 64) by reflexivity. rewrite O.
assert (L : Z.land (Z.lxor q (Z.ones 64)) q = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.lxor_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 64).
  - rewrite Z.ones_spec_low by lia. destruct (Z.testbit q i); reflexivity.
  - rewrite Z.ones_spec_high by lia. rewrite <- (Z.mod_small q (2 ^ 64)) by lia.
    rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
assert (X : Z.lxor (Z.lxor q (Z.ones 64)) q = Z.ones 64).
{ rewrite (Z.lxor_comm q (Z.ones 64)), Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r. reflexivity. }
pose proof (Z.add_nocarry_lxor _ _ L) as A. rewrite X in A. rewrite <- O in A |- *. lia.
Qed.
Lemma decE_nq_den : forall E q, ew E 10 = Z_to_bv 64 q -> 0 <= q < 2 ^ 64 ->
  sv_denot E (SAlu ALU_XOR (SOff 10 0) (SLit (-1))) = Z_to_bv 64 (DEC_M1 - q).
Proof.
intros E q H10 Hq. apply bv_eq.
change (bv_unsigned (sv_denot E ?x)) with (U E x).
rewrite unsigned_lit_small by (unfold DEC_M1; lia).
rewrite U_SAlu, (U_atom E 10 q H10 Hq), U_SLit. cbn [zalu_raw].
replace (zcanon (-1)) with 18446744073709551615 by (vm_compute; reflexivity).
rewrite decE_lxor_m1 by exact Hq. unfold DEC_M1. apply zcanon_small. lia.
Qed.

Section E0. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Definition decE_res (B : asyms) (d : DE) (W' : world tfibsegs) (ly' : alayout) (S' : astate) (U' : list (Z * Z))
    (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (k : Z) : Prop :=
  ajournal tfibsegs B STK_preset_base64_decode (d_sp d) (d_FP d) (d_ly d) (d_S d) (d_W d)
    (unpoison (d_U d) (d_mem d)) (d_md d) [] ly' S' W' (unpoison U' mem') md' k /\
  ARU tfibsegs B ly' S' U' W' mem' md' /\
  st_ok tfibsegs (Ereg regs' (fs_extraT ++ decE_xs d)) (fss_retT DEC_RA_MALLOC DEC_F decE_cs [] [])
    (restrict (w_H W') (YK11.mkst regs' (Z_to_bv 64 DEC_RA_MALLOC) mem' (YK11.seg_rom tfibsegs))) /\
  spZ regs' = d_sp d - DEC_F /\ getr regs' 3 = getr (d_regs d) 3 /\ getr regs' 4 = getr (d_regs d) 4 /\
  getr regs' 8 = w64 (d_lenp d) /\ getr regs' 18 = w64 (d_text d) /\ getr regs' 20 = w64 SHADOW_OFF /\
  (forall r, In r decE_kregs -> getr regs' r = getr (d_regs d) r) /\
  dec_kept B d W' mem'.

Lemma decE_cs_den : forall d regs, (forall r, In r decE_kregs -> getr regs r = getr (d_regs d) r) ->
  forall j r, nth_error dec_saved j = Some r ->
  exists e, nth_error decE_cs j = Some (YP09.mkChunk (24 + 8 * Z.of_nat j) (CVal 8 e)) /\
    sv_denot (Ereg regs (fs_extraT ++ decE_xs d)) e = getr (d_regs d) r.
Proof.
intros d regs HK j r Hj.
do 13 (destruct j as [|j];
  [cbn in Hj; injection Hj as <-; eexists; split; [reflexivity|];
   rewrite fsw_SOff0;
   first
   [ lazymatch goal with |- ew _ ?n = getr _ ?q => rewrite (ew_Ereg_nat regs _ n q eq_refl) end;
     apply HK; cbv [decE_kregs In]; auto 20
   | lazymatch goal with |- ew _ ?n = _ =>
       let j := eval compute in (n - 32)%nat in change n with (32 + j)%nat end;
     rewrite ew_Ereg_extra; reflexivity ] |]).
cbn in Hj. destruct j; discriminate Hj.
Qed.
Lemma decE_chunks_of_frame : forall d (W : world tfibsegs) m b regs,
  (forall r, In r decE_kregs -> getr regs r = getr (d_regs d) r) ->
  dec_frame_ok W m b (d_regs d) ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs (fs_extraT ++ decE_xs d)) (mrestrict (w_H W) m) b) decE_cs.
Proof.
intros d W m b regs HK HF. apply Forall_forall. intros c Hc.
destruct (In_nth_error _ _ Hc) as (j & Hj).
assert (Hlt : (j < length dec_saved)%nat).
{ apply nth_error_Some. intros E. apply nth_error_None in E. pose proof (nth_error_Some decE_cs j) as [H1 _].
  assert (length decE_cs = length dec_saved) as EL by reflexivity. rewrite Hj in H1. specialize (H1 ltac:(discriminate)). lia. }
destruct (nth_error dec_saved j) as [r|] eqn:Hr; [|apply nth_error_None in Hr; lia].
destruct (decE_cs_den d regs HK j r Hr) as (e & Hc' & He). rewrite Hj in Hc'. injection Hc' as ->.
apply (chunk_ok_val tfibsegs _ _ _ _ 8 e (bv_unsigned (getr (d_regs d) r))).
- rewrite He. symmetry. apply Z_to_bv_bv_unsigned.
- pose proof (u64_range (getr (d_regs d) r)). cbn [Z.of_N]. lia.
- cbn [Z.of_N]. lia.
- replace (b + (24 + 8 * Z.of_nat j)) with (b + 24 + 8 * Z.of_nat j) by lia. exact (HF j r Hr).
Qed.
Lemma decE_frame_of_chunks : forall d (W : world tfibsegs) m b regs,
  (forall r, In r decE_kregs -> getr regs r = getr (d_regs d) r) ->
  Forall (YP09.chunk_ok tfibsegs (Ereg regs (fs_extraT ++ decE_xs d)) (mrestrict (w_H W) m) b) decE_cs ->
  dec_frame_ok W m b (d_regs d).
Proof.
intros d W m b regs HK HC j r Hj.
destruct (decE_cs_den d regs HK j r Hj) as (e & Hc & He).
pose proof (proj1 (Forall_forall _ _) HC _ (nth_error_In _ _ Hc)) as Hck.
replace (b + 24 + 8 * Z.of_nat j) with (b + (24 + 8 * Z.of_nat j)) by lia.
apply (val_of_chunk_ok tfibsegs _ _ _ _ 8 e (bv_unsigned (getr (d_regs d) r)) Hck).
- rewrite He. symmetry. apply Z_to_bv_bv_unsigned.
- pose proof (u64_range (getr (d_regs d) r)). cbn [Z.of_N]. lia.
- cbn [Z.of_N]. lia.
Qed.

Lemma decE_widen : forall B STK sp ot FP ly S (W : world tfibsegs) mem md ly' S' (W' : world tfibsegs) mem' md' k,
  ajournal tfibsegs B STK sp FP ly S W mem md [] ly' S' W' mem' md' k ->
  sp <= ot -> ot mod 16 = 0 -> ot <= ly_top ly ->
  (forall a, sp <= a < ot -> apresent (w_H W') mem' a) ->
  ajournal tfibsegs B (STK + (ot - sp)) ot FP ly S W mem md [] ly' S' W' mem' md' k.
Proof.
intros B STK sp ot FP ly S W mem md ly' S' W' mem' md' k
  (J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10 & J11 & J12 & J13 & J14 & J15 & J16 & J17) Hot Hal Htop Hpres.
pose proof J15 as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop0 & Htop2).
unfold ajournal.
repeat (split; [eassumption|]).
split; [intros a Ha Hn; apply J9; [exact Ha | lia]|].
repeat (split; [eassumption|]).
split; [intros a Ha; destruct (Z_lt_le_dec a sp) as [L|L]; [apply J14; lia | apply Hpres; lia]|].
split; [|split; eassumption].
unfold astk_ok. repeat split; lia.
Qed.
End E0.

Ltac decE_cs_side := unfold acallee_saved; lazymatch goal with |- context [bv_unsigned ?q] =>
  let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end; lia.
Ltac decE_in := cbv [In]; repeat (first [left; reflexivity | right]).
Definition decE_csl : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Section S0. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* the frame chunks of the entry state at the strlen call: offsets from the entry sp, atoms of the entry env *)
Definition decE_cs0 : list YP09.chunk :=
  [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0));
   YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0));
   YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
   YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
   YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
   YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
   YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
(* the a0 the code passes to fuzz_malloc: ((len >> 2) << 1) + (len >> 2) + 3 *)
Definition decE_size_sv : sv :=
  SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL (SAlu ALU_SRL (SOff 10 0) (SLit 2)) (SLit 1))
    (SAlu ALU_SRL (SOff 10 0) (SLit 2))) (SLit 3).
Definition decE_avk (d : DE) (W : world tfibsegs) (m m' : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> a < alloc_ceiling \/ d_sp d <= a ->
    aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a.

Lemma decE_size_den : forall E (len : Z), ew E 10 = Z_to_bv 64 len -> 0 <= len < 2 ^ 32 ->
  sv_denot E decE_size_sv = Z_to_bv 64 (len / 4 * 3 + 3).
Proof.
intros E len H10 Hl. unfold decE_size_sv. apply bv_eq.
assert (D : 0 <= len / 4 <= len) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
change (bv_unsigned (sv_denot E ?x)) with (U E x).
rewrite unsigned_lit_small by lia.
rewrite !U_SAlu, (U_atom E 10 len H10 ltac:(lia)), !U_lit by lia. cbn [zalu_raw].
change (Z.land 2 63) with 2. change (Z.land 1 63) with 1.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4.
unfold zcanon, M64. rewrite (Z.mod_small (len / 4)) by lia.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
repeat rewrite Z.mod_small by lia. lia.
Qed.

Lemma decE_pstat_img : forall a, inFP FS_PSTAT_FP a -> in_img tfibsegs a.
Proof.
intros a (r & Hr & Ha).
assert (Hb : forallb (fun r : Z * Z => existsb (fun s => (Z.of_N (seg_base s) <=? fst r) &&
  (snd r <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs) FS_PSTAT_FP = true) by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) Hb r Hr) as H. apply existsb_exists in H as (s & Hs & Hss).
apply andb_prop in Hss as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists s. split; [exact Hs | lia].
Qed.

Lemma decE_restrict_of_mbyte : forall (H H' : word -> bool) (m m' : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ in_img tfibsegs a ->
  mbyte tfibsegs (mrestrict H' m') a = mbyte tfibsegs (mrestrict H m) a ->
  mrestrict H' m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a).
Proof.
intros H H' m m' a Ha Hn E. unfold mbyte in E. rewrite (YCbq.seg_rom_none tfibsegs a Ha Hn) in E.
destruct (mrestrict H' m' (Z_to_bv 64 a)), (mrestrict H m (Z_to_bv 64 a)); congruence.
Qed.
Lemma decE_writable_eq : forall (m m' : word -> option byte) a,
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> (writable_at tfibsegs m a <-> writable_at tfibsegs m' a).
Proof. intros m m' a H. unfold writable_at, wview. rewrite H. reflexivity. Qed.

Lemma decE_val_mem_av : forall (W : world tfibsegs) m m' a (n : nat) v,
  (forall i, 0 <= i < Z.of_nat n -> aview tfibsegs (w_H W) m' (a + i) = aview tfibsegs (w_H W) m (a + i)) ->
  val_mem tfibsegs (mrestrict (w_H W) m) a n v -> val_mem tfibsegs (mrestrict (w_H W) m') a n v.
Proof.
intros W m m' a n v Hk Hv k Hk'. rewrite (mbyte_of_aview tfibsegs _ _ _ _ _ (Hk (Z.of_nat k) ltac:(lia))). exact (Hv k Hk').
Qed.

Lemma decE_glob_av : forall (W : world tfibsegs) m m' live peak cnt fail,
  (forall a, 0 <= a < alloc_ceiling -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
  fs_glob tfibsegs W m live peak cnt fail -> fs_glob tfibsegs W m' live peak cnt fail.
Proof.
intros W m m' live peak cnt fail AV (G1 & G2 & G3 & G4 & R). pose proof asan_consts as (C1 & _).
assert (VB : forall a v, 0 <= a -> a + 8 <= alloc_ceiling -> val_mem tfibsegs (mrestrict (w_H W) m) a 8 v ->
  val_mem tfibsegs (mrestrict (w_H W) m') a 8 v)
  by (intros a v Ha Hb Hv; apply (decE_val_mem_av W m); [intros i Hi; apply AV; cbn in Hi; lia | exact Hv]).
unfold fs_glob, fs_glob_at. unfold G_LIVE, G_PEAK, G_COUNT, G_FAIL in *.
split; [apply VB; [lia | lia | exact G1]|].
split; [apply VB; [lia | lia | exact G2]|].
split; [apply VB; [lia | lia | exact G3]|].
split; [apply VB; [lia | lia | exact G4]|].
exact R.
Qed.

Lemma decE_ro_av : forall B (W : world tfibsegs) m m',
  (forall a, 0 <= a < alloc_ceiling -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) m) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) m').
Proof.
intros B W m m' AV HR a Ha Ho He. pose proof asan_consts as (C1 & _).
assert (Hb : 0 <= a < alloc_ceiling).
{ destruct Ha as [(sg & Hin & Hw & Hr) | Hr]; [|unfold FS_RLO, FS_RHI in Hr; lia].
  assert (Hi : in_img tfibsegs a) by (exists sg; split; [exact Hin | exact Hr]).
  pose proof (fs_segs_img a Hi) as Hl. unfold FS_IMG_END in Hl. lia. }
rewrite (AV a Hb). exact (HR a Ha Ho He).
Qed.

Lemma decE_cstr_av : forall (W : world tfibsegs) m m' p l,
  (forall a, 0 <= a < alloc_ceiling -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a) ->
  cstr_ok tfibsegs W m p l -> cstr_ok tfibsegs W m' p l.
Proof.
intros W m m' p l AV H. pose proof asan_consts as (C1 & _).
unfold cstr_ok, cstr in H |- *.
repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
repeat match goal with |- _ /\ _ => split end; try assumption; lazymatch goal with
  | Hg : garr8 _ (mrestrict _ m) p (l ++ [0]) |- garr8 _ _ p (l ++ [0]) =>
      apply (garr8_frame tfibsegs _ _ p (l ++ [0]) Hg); intros a Ha; rewrite length_app in Ha; cbn [length] in Ha;
      apply (mbyte_of_aview tfibsegs); apply AV; lia
  | Hra : range_addressable (aview _ _ m) ?o ?q ?n |- range_addressable (aview _ _ m') ?o ?q ?n =>
      intros x Hx; destruct (Hra x Hx) as (s & Hs1 & Hs2); exists s; split; [|exact Hs2];
      rewrite AV; [exact Hs1|]; unfold shadow_of_addr, SHADOW_OFF; lia
  | Hhv : shadow_hull_vis (aview _ _ m) ?q ?n |- shadow_hull_vis (aview _ _ m') ?q ?n =>
      intros s Hsr; rewrite AV; [exact (Hhv s Hsr)|]; unfold shadow_addr, SHADOW_OFF in Hsr; lia
  | Htl : forall a, _ -> aview _ _ m a <> None |- forall a, _ -> aview _ _ m' a <> None =>
      intros a Ha; rewrite AV; [exact (Htl a Ha)|];
      pose proof (Z.mod_pos_bound (p + Z.of_nat (length l)) 8 ltac:(lia));
      pose proof (Z.div_mod (p + Z.of_nat (length l)) 8 ltac:(lia));
      pose proof (Z.div_mod alloc_ceiling 4096 ltac:(lia));
      pose proof (proj2 YM05.alloc_ceiling_value); lia
  end.
Qed.

Lemma decE_cs0_den : forall regs j r, nth_error dec_saved j = Some r ->
  exists e, nth_error decE_cs0 j = Some (YP09.mkChunk (-104 + 8 * Z.of_nat j) (CVal 8 e)) /\
    sv_denot (Ereg regs fs_extraT) e = getr regs r.
Proof.
intros regs j r Hj.
do 13 (destruct j as [|j];
  [cbn in Hj; injection Hj as <-; eexists; split; [reflexivity|];
   rewrite fsw_SOff0;
   lazymatch goal with |- ew _ ?n = getr _ ?q => exact (ew_Ereg_nat regs _ n q eq_refl) end |]).
cbn in Hj. destruct j; discriminate Hj.
Qed.
Lemma decE_frame_of_cs0 : forall (W : world tfibsegs) m sp regs,
  Forall (YP09.chunk_ok tfibsegs (Ereg regs fs_extraT) (mrestrict (w_H W) m) sp) decE_cs0 ->
  dec_frame_ok W m (sp - 128) regs.
Proof.
intros W m sp regs HC j r Hj.
destruct (decE_cs0_den regs j r Hj) as (e & Hc & He).
pose proof (proj1 (Forall_forall _ _) HC _ (nth_error_In _ _ Hc)) as Hck.
replace (sp - 128 + 24 + 8 * Z.of_nat j) with (sp + (-104 + 8 * Z.of_nat j)) by lia.
apply (val_of_chunk_ok tfibsegs _ _ _ _ 8 e (bv_unsigned (getr regs r)) Hck).
- rewrite He. symmetry. apply Z_to_bv_bv_unsigned.
- pose proof (u64_range (getr regs r)). cbn [Z.of_N]. lia.
- cbn [Z.of_N]. lia.
Qed.

Lemma decE_frame_avk : forall d (W : world tfibsegs) E rs m m',
  frame_of E rs m m' ->
  (forall r a, In r rs -> base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
     alloc_ceiling <= a < d_sp d) ->
  decE_avk d W m m'.
Proof.
intros d W E rs m m' HF Hw a Ha Hn. apply (aview_at tfibsegs). apply HF. rewrite (wz a Ha).
intros (r & Hin & Hr). pose proof (Hw r a Hin Hr). lia.
Qed.

Lemma decE_kept_avk : forall B d (W : world tfibsegs) m m',
  alloc_ceiling <= d_sp d -> 0 <= d_lenp d -> (d_lenp d + 8 <= alloc_ceiling \/ d_sp d <= d_lenp d) ->
  d_lenp d + 8 <= 2 ^ 64 -> d_ot d <= 2 ^ 47 ->
  decE_avk d W m m' -> dec_kept B d W m -> dec_kept B d W m'.
Proof.
intros B d W m m' Hsp Hl0 Hl Hl64 Hot AVK (K1 & K2 & K3 & K4).
pose proof asan_consts as (C1 & _).
assert (AV : forall a, 0 <= a < alloc_ceiling -> aview tfibsegs (w_H W) m' a = aview tfibsegs (w_H W) m a)
  by (intros a Ha; apply AVK; lia).
split; [|split; [|split]].
- apply (decE_val_mem_av W m); [|exact K1]. intros i Hi. cbn in Hi. apply AVK; lia.
- intros a Ha Hn. destruct (K2 a Ha Hn) as [E1 E2].
  assert (Eb : mbyte tfibsegs (mrestrict (w_H W) m') a = mbyte tfibsegs (mrestrict (w_H W) m) a)
    by (apply (mbyte_of_aview tfibsegs); apply AVK; lia).
  split; [rewrite Eb; exact E1|].
  rewrite E2.
  assert (Hni : ~ in_img tfibsegs a) by (intros Hin; pose proof (fs_segs_img a Hin); unfold FS_IMG_END in *; lia).
  exact (decE_writable_eq _ _ a (decE_restrict_of_mbyte _ _ _ _ a ltac:(lia) Hni Eb)).
- exact (decE_cstr_av W m m' _ _ AV K3).
- exact (decE_ro_av B W m m' AV K4).
Qed.
End S0.

Section P. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HSS : FsShadowSyms B.
Hypothesis HIMG : fs_img_facts tfibsegs B.

Lemma decE_null : forall d W' ly' S' regs' mem' md',
  dec_entry_ok B d -> d_cnt d = d_fail d ->
  decE_res B d W' ly' S' (d_U d) regs' mem' md' 0 ->
  getr regs' 10 = w64 0 ->
  ablocks B ly' S' = ablocks B (d_ly d) (d_S d) ->
  fs_glob tfibsegs W' mem' (d_live d) (d_peak d) (d_cnt d + 1) SIZE_MAXZ ->
  SRr tfibsegs W' (mkCfg (YK11.mkst regs' (Z_to_bv 64 DEC_RA_MALLOC) mem' (YK11.seg_rom tfibsegs)) md') (dec_post B d).
Proof.
intros d W' ly' S' regs' mem' md' HOK Hcf HRES HA0 HBL HG'.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Esp : d_sp d = spZ (d_regs d)) by reflexivity.
assert (HSTK : 128 <= STK_preset_base64_decode) by (vm_compute; discriminate).
assert (HF128 : DEC_F = 128) by reflexivity.
destruct HOK as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & Vlenp & _ & _ & HGLOB & _ & _ & _ & HCNT & HPL).
destruct HPRE as (HPREU & _).
pose proof (fsw_ARU B STK_preset_base64_decode (d_ly d) (d_S d) (d_U d) (d_W d) (d_regs d) (d_mem d) (d_md d) (d_ch d)
  HPREU) as HARU0.
pose proof HPREU as (HAP & _ & _).
pose proof HAP as (HAR & Hra & _ & _ & _ & Hstk & _ & _ & _).
pose proof Hstk as (Hsp16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (Hcnt0 : 0 <= d_cnt d) by (destruct HGLOB as (_ & _ & _ & _ & _ & _ & Hc & _); lia).
destruct HPL as (_ & Hsl & Hlo & Hot16 & Hottop & HPRES & _).
assert (Hspot : d_sp d <= d_ot d) by lia.
(* ---- the resumed state after fuzz_malloc ---- *)
destruct HRES as (HJ & HARU & HS0 & Gsp & G3 & G4 & _ & _ & _ & HK & HKEPT).
destruct HKEPT as (Vl' & HWK & _ & _).
assert (E2 : bv_unsigned (ew (Ereg regs' (fs_extraT ++ decE_xs d)) 2) = d_sp d - DEC_F)
  by (rewrite (ew_Ereg_nat regs' (fs_extraT ++ decE_xs d) 2 2%bv eq_refl); exact Gsp).
(* ---- a0 = 0: the `beqz a0` at 0x84cb0 is taken ---- *)
assert (HS : st_ok tfibsegs (Ereg regs' (fs_extraT ++ decE_xs d))
  (add_cond (fss_retT DEC_RA_MALLOC DEC_F decE_cs [] []) (mkAC BC_EQ (SOff 10 0) (SLit 0)))
  (restrict (w_H W') (YK11.mkst regs' (Z_to_bv 64 DEC_RA_MALLOC) mem' (YK11.seg_rom tfibsegs)))).
{ apply YP06.st_ok_add_cond; [exact HS0|].
  rewrite fsw_SOff0, (ew_Ereg_nat regs' (fs_extraT ++ decE_xs d) 10 10%bv eq_refl), HA0.
  vm_compute. reflexivity. }
clear HS0.
(* ---- the run to the `ret` 0x84e18 and the return, into fpostU at the raised top ---- *)
assert (MAIN : SRr tfibsegs W' (mkCfg (YK11.mkst regs' (Z_to_bv 64 DEC_RA_MALLOC) mem' (YK11.seg_rom tfibsegs)) md')
  (fpostU tfibsegs B (d_STKJ d) (d_ot d) (d_FP d) (d_regs d) (d_ly d) (d_S d) (d_U d) (d_W d) (d_mem d) (d_md d) 0 (d_U d)
     (fun (ly2 : alayout) (S2 : astate) (W2 : world tfibsegs) (regs2 : bvmap 5 word)
          (mem2 : word -> option byte) (md2 : Model) =>
        getr regs2 10 = w64 0 /\ ablocks B ly2 S2 = ablocks B (d_ly d) (d_S d) /\
        wkeep tfibsegs (d_W d) W2 (d_mem d) mem2 (spZ (d_regs d)) (d_ot d) (d_lenp d) 8 /\
        val_mem tfibsegs (mrestrict (w_H W2) mem2) (d_lenp d) 8 (d_v d) /\
        fs_glob tfibsegs W2 mem2 (d_live d) (d_peak d) ((d_cnt d + 1) mod 2 ^ 64) SIZE_MAXZ))).
{ fsw_aj_runU fsw_wr_tbl_ok HS HJ HARU.
  - unfold add_cond, fss_retT, fsT_ret_regions. cbn [ss_mem app].
    eapply awr_ok_cons_stack_off with (n := 2%nat) (d := - DEC_F);
      [reflexivity | rewrite E2; lia | cbv [fstk_ret YP09.r_wlo]; lia | cbv [fstk_ret YP09.r_whi]; lia |].
    apply awr_ok_cons_ro; [cbv [fs_got_region YP09.r_wlo YP09.r_whi]; lia|].
    apply awr_ok_cons_ro; [cbv [fs_bcell_region YP09.r_wlo YP09.r_whi]; lia|].
    apply awr_ok_nil.
  - assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp d - DEC_F <= a < d_sp d) ->
      ms_mem ms (Z_to_bv 64 a) = mem' (Z_to_bv 64 a)).
    { intros a Ha Hna. apply HF. rewrite (wz a Ha). intros (r & Hin & Hr).
      unfold add_cond, fss_retT, fsT_ret_regions in Hin. cbn [ss_mem app In] in Hin.
      destruct Hin as [<-|[<-|[<-|[]]]];
        cbv [fstk_ret fs_got_region fs_bcell_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        try (rewrite E2 in Hr); lia. }
    assert (MWE : forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp d - DEC_F <= a < d_sp d) ->
      mrestrict (w_H W') (ms_mem ms) (Z_to_bv 64 a) = mrestrict (w_H W') mem' (Z_to_bv 64 a))
      by (intros a Ha Hna; unfold mrestrict; rewrite (MEQ a Ha Hna); reflexivity).
    assert (MB : forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp d - DEC_F <= a < d_sp d) ->
      mbyte tfibsegs (mrestrict (w_H W') (ms_mem ms)) a = mbyte tfibsegs (mrestrict (w_H W') mem') a)
      by (intros a Ha Hna; unfold mbyte; rewrite (MWE a Ha Hna); reflexivity).
    assert (SB : same_below mem' (ms_mem ms) alloc_ceiling) by (intros x Hx; apply MEQ; lia).
    assert (HKEEP : wkeep tfibsegs (d_W d) W' (d_mem d) (ms_mem ms) (spZ (d_regs d)) (d_ot d) (d_lenp d) 8).
    { intros a Ha Hno. destruct (HWK a Ha Hno) as [Hm Hw]. split.
      - rewrite (MB a ltac:(lia) ltac:(lia)). exact Hm.
      - exact (iff_trans Hw (decE_writable_eq _ _ a (MWE a ltac:(lia) ltac:(lia)))). }
    assert (VL : val_mem tfibsegs (mrestrict (w_H W') (ms_mem ms)) (d_lenp d) 8 (d_v d)).
    { intros k Hk. rewrite (MB (d_lenp d + Z.of_nat k) ltac:(lia) ltac:(lia)). exact (Vl' k Hk). }
    assert (HGL : fs_glob tfibsegs W' (ms_mem ms) (d_live d) (d_peak d) ((d_cnt d + 1) mod 2 ^ 64) SIZE_MAXZ).
    { rewrite Z.mod_small by lia. exact (fs_glob_below W' mem' (ms_mem ms) _ _ _ _ SB HG'). }
    assert (R1 : getr (ms_regs ms) 1%bv = getr (d_regs d) 1%bv).
    { lazymatch type of HS with
      | st_ok _ _ ?ssf _ =>
        exact (fsw_reg_extra (w_H W') regs' (fs_extraT ++ decE_xs d) ssf ms 1%bv 4 HS ltac:(vm_compute; reflexivity))
      end. }
    eapply (fsw_retU B fsw_wr_tbl fsw_wr_tbl_ok).
    + exact HS.
    + vm_compute; reflexivity.
    + vm_compute; reflexivity.
    + rewrite R1. exact Hra.
    + unfold d_STKJ.
      apply (decE_widen B STK_preset_base64_decode (d_sp d) (d_ot d) (d_FP d) (d_ly d) (d_S d) (d_W d)
        (unpoison (d_U d) (d_mem d)) (d_md d) ly' S' W' (unpoison (d_U d) (ms_mem ms)) _ 0 HJ Hspot Hot16 Hottop).
      intros a Ha.
      pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & J9 & _).
      apply (apresent_transfer tfibsegs (w_H (d_W d)) (w_H W') (unpoison (d_U d) (d_mem d))
        (unpoison (d_U d) (ms_mem ms)) a); [lia | | apply J9; lia |].
      * intros Hi. pose proof (fs_segs_img a Hi) as Hb. unfold FS_IMG_END in Hb. lia.
      * apply (fsw_apresent_poison B (d_ly d) (d_S d) (d_U d) (d_W d) (d_mem d) (d_md d) a HARU0); [lia|].
        exact (HPRES a Ha).
    + exact HARU.
    + lazymatch type of HS with
      | st_ok _ _ ?ssf _ =>
        apply (fsw_preserved (w_H W') (Ereg regs' (fs_extraT ++ decE_xs d)) ssf ms (d_regs d)
          (fun r : bv 5 => sr_get (ss_regs ssf) r) HS);
        [vm_compute; reflexivity|];
        let r := fresh "r" in let Hr := fresh "Hr" in
        intros r Hr; cbv [CALLEE_SAVED In] in Hr;
        repeat (destruct Hr as [<-|Hr]); [..|destruct Hr]
      end;
      cbv beta;
      lazymatch goal with
      | |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e'
      end;
      first
      [ apply fsw_sp_back; rewrite E2; lia
      | rewrite fsw_SOff0;
        first
        [ lazymatch goal with |- ew _ ?n = getr _ ?q => rewrite (ew_Ereg_nat regs' _ n q eq_refl) end;
          first [exact G3 | exact G4 | apply HK; cbv [decE_kregs In]; auto 20]
        | lazymatch goal with |- ew _ ?n = _ =>
            let j := eval compute in (n - 32)%nat in change n with (32 + j)%nat end;
          rewrite ew_Ereg_extra; reflexivity ] ].
    + intros mat2. cbv beta.
      split.
      { unfold w64. lazymatch type of HS with
        | st_ok _ _ ?ssf _ => exact (fsw_reg_lit (w_H W') _ ssf ms 10%bv 0 HS ltac:(vm_compute; reflexivity) ltac:(lia))
        end. }
      split; [exact HBL|]. split; [exact HKEEP|]. split; [exact VL | exact HGL]. }
eapply SRr_mono; [exact MAIN|].
intros W2 c2 _ HP. cbv beta zeta delta [dec_post]. left. split; [exact Hcf | exact HP].
Qed.

Lemma decQ_apresent_of_mbyte : forall (H : word -> bool) (m : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ in_img tfibsegs a -> mbyte tfibsegs (mrestrict H m) a <> None -> apresent H m a.
Proof.
intros H m a Ha Hn Hb. unfold apresent. unfold mbyte, mrestrict in Hb.
rewrite (YCbq.seg_rom_none tfibsegs a Ha Hn) in Hb.
revert Hb. destruct (H (Z_to_bv 64 a)); intros Hb; [exfalso; apply Hb; reflexivity|].
split; [reflexivity|].
revert Hb. destruct (m (Z_to_bv 64 a)) as [b|]; intros Hb; [exists b; reflexivity | exfalso; apply Hb; reflexivity].
Qed.
Lemma decQ_mbyte_of_apresent : forall (H : word -> bool) (m : word -> option byte) a,
  apresent H m a -> mbyte tfibsegs (mrestrict H m) a <> None.
Proof. intros H m a [Hh [b Hb]]. unfold mbyte, mrestrict. rewrite Hh, Hb. discriminate. Qed.

Lemma decE_nonnull : forall d q W' ly' S' regs' mem' md',
  dec_entry_ok B d -> d_cnt d <> d_fail d ->
  decE_res B d W' ly' S' (d_U d ++ [(q - HEAD, HEAD)]) regs' mem' md' 1 ->
  getr regs' 10 = w64 q -> 4096 + HEAD <= q ->
  ablocks B ly' S' = ablocks B (d_ly d) (d_S d) ++ [(q - HEAD, d_n d + HEAD)] ->
  fs_heads B ly' S' (d_U d ++ [(q - HEAD, HEAD)]) ->
  fs_rblock tfibsegs B ly' S' W' mem' q (d_n d) ->
  range_addressable (aview tfibsegs (w_H W') mem') SHADOW_OFF q (d_n d) ->
  fs_glob tfibsegs W' mem' (d_live d + d_n d) (Z.max (d_peak d) (d_live d + d_n d)) (d_cnt d + 1) (d_fail d) ->
  (forall Wc lyc Sc Uc regsc memc mdc k q0, dec_head B d q0 0 [] 0 0 Wc lyc Sc Uc regsc memc mdc k ->
     SRr tfibsegs Wc (mkCfg (YK11.mkst regsc (Z_to_bv 64 DEC_HEAD) memc (YK11.seg_rom tfibsegs)) mdc) (dec_post B d)) ->
  SRr tfibsegs W' (mkCfg (YK11.mkst regs' (Z_to_bv 64 DEC_RA_MALLOC) mem' (YK11.seg_rom tfibsegs)) md') (dec_post B d).
Proof.
intros d q W' ly' S' regs' mem' md' HOK Hcf HRES G10 Hq HBL HHD HRB HRA HGL HK.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HF128 : 128 <= STK_preset_base64_decode) by (vm_compute; discriminate).
destruct HRES as (HJ & HARU & HS & Esp & R3 & R4 & R8 & R18 & R20 & RK & HKEPT).
pose proof HJ as (J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10 & J11 & J12 & J13 & J14 & J15 & J16 & J17).
pose proof J15 as (Hsp16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HOK as (HPRE & _ & _ & _ & _ & HCS0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPLACE).
pose proof HCS0 as (_ & Htx4 & Htxc & _).
destruct HPRE as (HPREU & _).
pose proof HPREU as (HAP & _ & _).
pose proof HAP as (HAR0 & _).
unfold d_sp in *. unfold DEC_F in Esp.
destruct HPLACE as (_ & Hsl & Hlo & Hot16 & Hottop & Hpres0 & _).
assert (Hspot : spZ (d_regs d) <= d_ot d) by lia.
(* ---- q's block: below alloc_ceiling ---- *)
pose proof HRB as (HinB & Hq16 & Hn0 & VH).
pose proof HARU as (HARc & _ & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc HinB) as (_ & Hb4096 & Hbceil & _).
pose proof (req_size_pos (d_n d + HEAD) ltac:(unfold HEAD; lia)) as (RQ1 & RQ2).
unfold HEAD in Hq, Hb4096, Hbceil, RQ1, RQ2.
(* ---- the resumed env and the conditions a0 = q <> 0, s2 = text <> 0 ---- *)
set (E := Ereg regs' (fs_extraT ++ decE_xs d)) in *.
assert (E10 : ew E 10 = Z_to_bv 64 q) by (unfold E; rewrite (ew_Ereg_nat regs' _ 10 10%bv eq_refl); exact G10).
assert (E18 : ew E 18 = Z_to_bv 64 (d_text d)) by (unfold E; rewrite (ew_Ereg_nat regs' _ 18 18%bv eq_refl); exact R18).
assert (E2 : bv_unsigned (ew E 2) = spZ (d_regs d) - 128)
  by (unfold E; rewrite (ew_Ereg_nat regs' _ 2 2%bv eq_refl); exact Esp).
assert (HSc : st_ok tfibsegs E
  (add_cond (add_cond (fss_retT DEC_RA_MALLOC DEC_F decE_cs [] []) (mkAC BC_NE (SOff 10 0) (SLit 0)))
     (mkAC BC_NE (SOff 18 0) (SLit 0)))
  (restrict (w_H W') (YK11.mkst regs' (Z_to_bv 64 DEC_RA_MALLOC) mem' (YK11.seg_rom tfibsegs)))).
{ apply (st_ok_add_cond tfibsegs); [apply (st_ok_add_cond tfibsegs); [exact HS|]|].
  - rewrite branch_ne_U, (U_atom E 10 q E10 ltac:(lia)), U_lit by lia.
    apply Bool.negb_true_iff, Z.eqb_neq. lia.
  - rewrite branch_ne_U, (U_atom E 18 (d_text d) E18 ltac:(lia)), U_lit by lia.
    apply Bool.negb_true_iff, Z.eqb_neq. lia. }
clear HS.
(* ---- the run from 0x84cb0 to the loop head 0x84cf8 ---- *)
fsw_aj_run_toU fsw_wr_tbl_ok HSc HJ HARU DEC_HEAD.
- cbn [add_cond fss_retT fsT_ret_regions ss_mem app].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -128);
    [reflexivity | rewrite E2; lia | cbv [fstk_ret YP09.r_wlo]; lia | cbv [fstk_ret YP09.r_whi DEC_F]; lia |].
  apply awr_ok_cons_ro; [cbv [fs_got_region YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_cons_ro; [cbv [fs_bcell_region YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_nil.
- assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (d_regs d) - 128 <= a < spZ (d_regs d)) ->
    ms_mem ms (Z_to_bv 64 a) = mem' (Z_to_bv 64 a)).
  { intros a Ha Hna. apply HF. rewrite (wz a Ha). intros (r & Hin & Hr).
    cbn [add_cond fss_retT fsT_ret_regions ss_mem app In] in Hin.
    destruct Hin as [<-|[<-|[<-|[]]]];
      cbv [fstk_ret fs_got_region fs_bcell_region YP09.r_base YP09.r_wlo YP09.r_whi base_val DEC_F] in Hr;
      try (rewrite E2 in Hr); lia. }
  assert (MWE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (d_regs d) - 128 <= a < spZ (d_regs d)) ->
    mrestrict (w_H W') (ms_mem ms) (Z_to_bv 64 a) = mrestrict (w_H W') mem' (Z_to_bv 64 a))
    by (intros a Ha Hna; unfold mrestrict; rewrite (MEQ a Ha Hna); reflexivity).
  assert (MB : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (d_regs d) - 128 <= a < spZ (d_regs d)) ->
    mbyte tfibsegs (mrestrict (w_H W') (ms_mem ms)) a = mbyte tfibsegs (mrestrict (w_H W') mem') a)
    by (intros a Ha Hna; unfold mbyte; rewrite (MWE a Ha Hna); reflexivity).
  assert (SB : same_below mem' (ms_mem ms) alloc_ceiling) by (intros x Hx; apply MEQ; lia).
  assert (MV : forall a k v, 0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
    (spZ (d_regs d) <= a \/ a + Z.of_nat k <= spZ (d_regs d) - 128) ->
    val_mem tfibsegs (mrestrict (w_H W') mem') a k v -> val_mem tfibsegs (mrestrict (w_H W') (ms_mem ms)) a k v)
    by (intros a k v H0 Hk Hout Hv i Hi; rewrite (MB (a + Z.of_nat i) ltac:(lia) ltac:(lia)); exact (Hv i Hi)).
  destruct HKEPT as (KV & KW & KC & KR).
  assert (KV' : val_mem tfibsegs (mrestrict (w_H W') (ms_mem ms)) (d_lenp d) 8 (d_v d))
    by (apply (MV (d_lenp d) 8%nat (d_v d)); [lia | lia | lia | exact KV]).
  assert (KW' : wkeep tfibsegs (d_W d) W' (d_mem d) (ms_mem ms) (spZ (d_regs d)) (d_ot d) (d_lenp d) 8).
  { intros a Ha Hno. destruct (KW a Ha Hno) as [K1 K2]. split.
    - rewrite (MB a ltac:(lia) ltac:(lia)). exact K1.
    - pose proof (decE_writable_eq (mrestrict (w_H W') mem') (mrestrict (w_H W') (ms_mem ms)) a
        (MWE a ltac:(lia) ltac:(lia))) as WE. tauto. }
  assert (KC' : cstr_ok tfibsegs W' (ms_mem ms) (d_text d) (d_tb d)) by exact (cstr_ok_below W' mem' (ms_mem ms) _ _ SB KC).
  assert (KR' : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W') (ms_mem ms)))
    by exact (arodata_below B W' mem' (ms_mem ms) SB KR).
  assert (HRB' : fs_rblock tfibsegs B ly' S' W' (ms_mem ms) q (d_n d)).
  { unfold fs_rblock. split; [exact HinB|]. split; [exact Hq16|]. split; [exact Hn0|].
    exact (val_mem_below (w_H W') mem' (ms_mem ms) alloc_ceiling (q - HEAD) 8%nat (d_n d) SB
             ltac:(unfold HEAD; lia) ltac:(unfold HEAD; lia) VH). }
  assert (HRA' : range_addressable (aview tfibsegs (w_H W') (ms_mem ms)) SHADOW_OFF q (d_n d)).
  { eapply range_addressable_agree; [|exact HRA].
    intros x Hx. apply (aview_below (w_H W') mem' (ms_mem ms) alloc_ceiling _ SB).
    unfold shadow_of_addr, SHADOW_OFF.
    pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia. }
  assert (HGL' : fs_glob tfibsegs W' (ms_mem ms) (d_live d + d_n d) (Z.max (d_peak d) (d_live d + d_n d))
                   (d_cnt d + 1) (d_fail d))
    by exact (fs_glob_below W' mem' (ms_mem ms) _ _ _ _ SB HGL).
  assert (HPRES : forall a, spZ (d_regs d) <= a < d_ot d ->
    apresent (w_H W') (unpoison (d_U d ++ [(q - HEAD, HEAD)]) (ms_mem ms)) a).
  { intros a Ha.
    assert (Ha64 : 0 <= a < 2 ^ 64) by lia.
    assert (Hni : ~ in_img tfibsegs a)
      by (intros Hi; pose proof (fs_segs_img a Hi) as Hi'; unfold FS_IMG_END in Hi'; lia).
    apply (fsw_apresent_poison B ly' S' _ W' (ms_mem ms) _ a HARU);
      [first [lia | unfold kHighMemBeg in *; lia]|].
    apply (decQ_apresent_of_mbyte _ _ a Ha64 Hni).
    destruct (Z.le_gt_cases (d_lenp d) a) as [L1|L1];
      [destruct (Z.lt_ge_cases a (d_lenp d + 8)) as [L2|L2]|].
    - pose proof (KV' (Z.to_nat (a - d_lenp d)) ltac:(lia)) as Hb.
      rewrite Z2Nat.id in Hb by lia. replace (d_lenp d + (a - d_lenp d)) with a in Hb by lia.
      rewrite Hb. discriminate.
    - destruct (KW' a Ha ltac:(lia)) as [K1 _]. rewrite K1. apply decQ_mbyte_of_apresent. exact (Hpres0 a Ha).
    - destruct (KW' a Ha ltac:(lia)) as [K1 _]. rewrite K1. apply decQ_mbyte_of_apresent. exact (Hpres0 a Ha). }
  lazymatch type of HSc with
  | st_ok _ _ ?ssf _ =>
    assert (RA : forall (r r' : bv 5) n, sr_get (ss_regs ssf) r = SOff n 0 -> Z.of_nat n = bv_unsigned r' ->
                  getr (ms_regs ms) r = getr regs' r')
      by (intros r r' n H1 H2; exact (fsw_reg_atom (w_H W') regs' (fs_extraT ++ decE_xs d) ssf ms r r' n HSc H1 H2));
    assert (RL : forall (r : bv 5) z, sr_get (ss_regs ssf) r = SLit z -> 0 <= z < 2 ^ 64 ->
                  getr (ms_regs ms) r = Z_to_bv 64 z)
      by (intros r z H1 H2; exact (fsw_reg_lit (w_H W') E ssf ms r z HSc H1 H2));
    assert (RE : forall (r : bv 5) e w, sr_get (ss_regs ssf) r = e -> sv_denot E e = w -> getr (ms_regs ms) r = w)
      by (intros r e w H1 H2; exact (decL_reg (w_H W') E ssf ms r e w HSc H1 H2));
    assert (HREG0 : region_ok tfibsegs E (mrestrict (w_H W') (ms_mem ms))
                      (YP09.mkRegion (Some 2%nat) 0 128 0 128
                         (YP09.mkChunk 16 (CVal 8 (SAlu ALU_XOR (SOff 10 0) (SLit (-1)))) ::
                          YP09.mkChunk 8 (CVal 8 (SOff 8 0)) :: decE_cs)))
      by exact (fsw_region_nth E ssf (restrict (w_H W') ms) 0 _ HSc eq_refl);
    assert (Hshape : ms = YK11.mkst (ms_regs ms) (Z_to_bv 64 DEC_HEAD) (ms_mem ms) (YK11.seg_rom tfibsegs))
      by exact (st_ok_restrict_mkst tfibsegs (w_H W') E ssf ms HSc eq_refl)
  end.
  rewrite Hshape.
  apply (HK W' ly' S' (d_U d ++ [(q - HEAD, HEAD)]) (ms_regs ms) (ms_mem ms) _ 1 q).
  unfold dec_head. cbv zeta.
  split.
  { unfold dec_J, d_STKJ, d_sp.
    exact (decE_widen B STK_preset_base64_decode (spZ (d_regs d)) (d_ot d) _ _ _ _ _ _ _ _ _ _ _ _
             HJ Hspot Hot16 Hottop HPRES). }
  split; [exact HARU|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [exact HHD|].
  split; [exact HBL|].
  split; [unfold HEAD; lia|].
  split; [exact HRB'|].
  split; [exact HRA'|].
  split; [exact Hcf|].
  split; [exact HGL'|].
  (* registers *)
  split; [unfold spZ at 1, d_sp, DEC_F; rewrite (RA 2%bv 2%bv 2%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)); exact Esp|].
  split; [rewrite (RA 3%bv 3%bv 3%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)); exact R3|].
  split; [rewrite (RA 4%bv 4%bv 4%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)); exact R4|].
  split; [exact (RL 8%bv DEC_M1 ltac:(vm_compute; reflexivity) ltac:(unfold DEC_M1; lia))|].
  split; [rewrite (RA 9%bv 10%bv 10%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)); exact G10|].
  split; [rewrite (RA 18%bv 18%bv 18%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)), R18;
          change (Z.of_nat 0) with 0; rewrite Z.add_0_r; reflexivity|].
  split; [exact (RL 19%bv G_B64 ltac:(vm_compute; reflexivity) ltac:(unfold G_B64; lia))|].
  split; [rewrite (RA 20%bv 20%bv 20%nat ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)); exact R20|].
  split; [exact (RL 21%bv 0 ltac:(vm_compute; reflexivity) ltac:(lia))|].
  split; [exact (RL 22%bv 0 ltac:(vm_compute; reflexivity) ltac:(lia))|].
  split; [lia|].
  split; [exact (RL 23%bv 0 ltac:(vm_compute; reflexivity) ltac:(lia))|].
  split; [exact (RL 24%bv 0 ltac:(vm_compute; reflexivity) ltac:(lia))|].
  split; [apply (RE 25%bv (SOff 18 (-1))); [vm_compute; reflexivity|];
          change (Z.of_nat 0) with 0; rewrite Z.add_0_r;
          apply decL_soff; [exact E18 | lia | lia]|].
  split; [exact (RL 26%bv 61 ltac:(vm_compute; reflexivity) ltac:(lia))|].
  split; [exact (RL 27%bv DEC_WSMASK ltac:(vm_compute; reflexivity) ltac:(unfold DEC_WSMASK; lia))|].
  (* the frame: the 13 saved words, the spilled lenp and ~q *)
  pose proof HREG0 as (_ & _ & _ & HCH).
  cbn [YP09.r_base YP09.r_chunks base_val] in HCH. rewrite E2 in HCH.
  split.
  { unfold d_sp, DEC_F. apply (decE_frame_of_chunks d W' (ms_mem ms) _ regs' RK).
    exact (Forall_inv_tail (Forall_inv_tail HCH)). }
  split.
  { unfold dec_lenp_slot, d_sp, DEC_F.
    apply (fsw_field E (mrestrict (w_H W') (ms_mem ms)) 2%nat (spZ (d_regs d) - 128) _ 0 128 0 128 8 8%N
                  (SOff 8 0) (d_lenp d) HREG0 E2 (or_intror (or_introl eq_refl))).
    - rewrite fsw_SOff0. unfold E. rewrite (ew_Ereg_nat regs' _ 8 8%bv eq_refl). exact R8.
    - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    - cbn. lia. }
  split.
  { unfold dec_nq_slot, d_sp, DEC_F.
    apply (fsw_field E (mrestrict (w_H W') (ms_mem ms)) 2%nat (spZ (d_regs d) - 128) _ 0 128 0 128 16 8%N
                  (SAlu ALU_XOR (SOff 10 0) (SLit (-1))) (DEC_M1 - q) HREG0 E2 (or_introl eq_refl)).
    - apply decE_nq_den; [exact E10 | lia].
    - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold DEC_M1. lia.
    - cbn. lia. }
  split; [unfold dec_kept, d_sp; split; [exact KV'|]; split; [exact KW'|]; split; [exact KC' | exact KR']|].
  split; [exact (garr8_nil tfibsegs _ _)|].
  split; [lia|].
  split; [lia|].
  split; [cbn; lia|].
  split; [constructor|].
  split; [reflexivity|].
  reflexivity.
Qed.

Lemma decK_ro_img : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> in_img tfibsegs a.
Proof.
intros a [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr]|].
assert (Hb : existsb (fun s => (Z.of_N (seg_base s) <=? FS_RLO) &&
  (FS_RHI <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs = true) by (vm_compute; reflexivity).
apply existsb_exists in Hb as (s & Hs & Hss). apply andb_prop in Hss as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists s. split; [exact Hs | lia].
Qed.
Lemma decK_ro_not_pstat : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> ~ inFP FS_PSTAT_FP a.
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
Lemma decK_ro_strs_img : forall s l a, In (s, l) FS_RO_STRS -> s <= a < s + Z.of_nat (length l) + 1 ->
  in_img tfibsegs a.
Proof.
intros s l a Hin Ha.
assert (Hb : forallb (fun r : Z * list Z => existsb (fun sg => (Z.of_N (seg_base sg) <=? fst r) &&
  (fst r + Z.of_nat (length (snd r)) + 1 <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) tfibsegs) FS_RO_STRS = true)
  by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) Hb (s, l) Hin) as H. cbn [fst snd] in H.
apply existsb_exists in H as (sg & Hsg & Hss). apply andb_prop in Hss as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
exists sg. split; [exact Hsg | lia].
Qed.
Lemma decK_pstat_closed : ~ YI16.sink_open_fp FS_PSTAT_FP.
Proof. apply sink_closed_pos. unfold FS_PSTAT_FP. repeat (apply Forall_cons; [cbn [fst]; lia|]). apply Forall_nil. Qed.

Lemma decK_sh_range : forall x, 0 <= x < 2 ^ 61 -> 0 <= shadow_addr x < 2 ^ 64.
Proof.
intros x Hx. unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_le_upper_bound x 8 (2 ^ 61) ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma decK_amem_data : forall p n a, 4096 <= p -> amem_range p n -> p <= a < p + n ->
  0 <= a < 2 ^ 64 /\ (a < SHADOW_OFF \/ kHighMemBeg <= a).
Proof.
intros p n a H1 H3 H4. pose proof asan_consts as (_ & _ & C3 & C4 & C5).
unfold amem_range, SHADOW_OFF in *. lia.
Qed.
Lemma decK_bv8_inj : forall x y, 0 <= x < 256 -> 0 <= y < 256 -> Z_to_bv 8 x = Z_to_bv 8 y -> x = y.
Proof.
intros x y Hx Hy E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E.
rewrite (bv_wrap_small 8 x), (bv_wrap_small 8 y) in E by (change (bv_modulus 8) with 256; lia). exact E.
Qed.
Lemma decK_cstr_same : forall (m : word -> option byte) tb l p,
  garr8 tfibsegs m p (tb ++ [0]) -> garr8 tfibsegs m p (l ++ [0]) ->
  Forall (fun c => c <> 0) tb -> Forall (fun c => c <> 0) l -> tb = l.
Proof.
intros m tb. induction tb as [|c tb IH]; intros l p H1 H2 N1 N2.
- destruct l as [|c' l]; [reflexivity|]. exfalso.
  pose proof (garr8_mbyte tfibsegs m p _ 0 H1 ltac:(cbn; lia)) as E1.
  pose proof (garr8_mbyte tfibsegs m p _ 0 H2 ltac:(cbn; lia)) as E2.
  pose proof (garr8_bytes_ok tfibsegs m p _ H2) as BO. unfold bytes_ok in BO. cbn [app] in BO.
  apply Forall_inv in BO. apply Forall_inv in N2. cbn [nth app] in E1, E2. rewrite E1 in E2.
  assert (E : Z_to_bv 8 0 = Z_to_bv 8 c') by congruence.
  apply N2. symmetry. apply decK_bv8_inj; [lia | lia | exact E].
- destruct l as [|c' l].
  + exfalso.
    pose proof (garr8_mbyte tfibsegs m p _ 0 H1 ltac:(cbn; lia)) as E1.
    pose proof (garr8_mbyte tfibsegs m p _ 0 H2 ltac:(cbn; lia)) as E2.
    pose proof (garr8_bytes_ok tfibsegs m p _ H1) as BO. unfold bytes_ok in BO. cbn [app] in BO.
    apply Forall_inv in BO. apply Forall_inv in N1. cbn [nth app] in E1, E2. rewrite E1 in E2.
    assert (E : Z_to_bv 8 c = Z_to_bv 8 0) by congruence.
    apply N1. apply decK_bv8_inj; [lia | lia | exact E].
  + change ((c :: tb) ++ [0]) with ([c] ++ (tb ++ [0])) in H1.
    change ((c' :: l) ++ [0]) with ([c'] ++ (l ++ [0])) in H2.
    apply (garr8_app tfibsegs) in H1 as [H1a H1b]. apply (garr8_app tfibsegs) in H2 as [H2a H2b].
    pose proof (garr8_mbyte tfibsegs m p _ 0 H1a ltac:(cbn; lia)) as E1.
    pose proof (garr8_mbyte tfibsegs m p _ 0 H2a ltac:(cbn; lia)) as E2.
    pose proof (garr8_bytes_ok tfibsegs m p _ H1a) as BO1. pose proof (garr8_bytes_ok tfibsegs m p _ H2a) as BO2.
    unfold bytes_ok in BO1, BO2. apply Forall_inv in BO1. apply Forall_inv in BO2.
    cbn [nth] in E1, E2. rewrite E1 in E2. assert (E : Z_to_bv 8 c = Z_to_bv 8 c') by congruence.
    assert (Ec : c = c') by (apply decK_bv8_inj; [lia | lia | exact E]). subst c'.
    cbn [length Z.of_nat] in H1b, H2b.
    rewrite (IH l (p + 1) H1b H2b (Forall_inv_tail N1) (Forall_inv_tail N2)). reflexivity.
Qed.
Lemma decK_unp_data : forall ly S U (W : world tfibsegs) mem md a,
  ARU tfibsegs B ly S U W mem md -> 0 <= a < 2 ^ 64 -> a < SHADOW_OFF \/ kHighMemBeg <= a ->
  aview tfibsegs (w_H W) (unpoison U mem) a = aview tfibsegs (w_H W) mem a.
Proof.
intros ly S U W mem md a H Ha Hr. apply aview_unpoison_out. rewrite (wz a Ha).
destruct (in_ush U a) eqn:E; [|reflexivity]. exfalso.
pose proof (ush_facts tfibsegs B ly S U W mem md a H E) as (_ & L1 & L2). lia.
Qed.
Lemma decK_vis_unp : forall (W : world tfibsegs) mem U s,
  upoisoned tfibsegs W mem U -> aview tfibsegs (w_H W) (unpoison U mem) s <> None -> aview tfibsegs (w_H W) mem s <> None.
Proof.
intros W mem U s HP Hv. rewrite (aview_mod tfibsegs (w_H W) (unpoison U mem) s) in Hv.
rewrite (aview_mod tfibsegs (w_H W) mem s).
assert (Hs : 0 <= s mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
destruct (in_ush U (s mod 2 ^ 64)) eqn:E.
- rewrite (HP _ E). discriminate.
- rewrite aview_unpoison_out in Hv; [exact Hv|]. rewrite (wz _ Hs). exact E.
Qed.
Lemma decK_ush_out : forall U x n,
  (forall r, In r U -> fst r mod 8 = 0 /\ snd r mod 8 = 0 /\ (fst r + snd r <= x \/ x + n <= fst r)) ->
  forall y, x <= y < x + n -> in_ush U (shadow_addr y) = false.
Proof.
intros U x n HU y Hy. destruct (in_ush U (shadow_addr y)) eqn:E; [|reflexivity]. exfalso.
apply in_ush_spec in E as ([a c] & Hr & Hs). destruct (HU _ Hr) as (A8 & C8 & D). cbn [fst snd] in *.
apply Z.mod_divide in A8 as [i ->]; [|lia]. apply Z.mod_divide in C8 as [j ->]; [|lia].
unfold shadow_addr in Hs. rewrite !Z.div_mul in Hs by lia.
pose proof (Z.div_mod y 8 ltac:(lia)). pose proof (Z.mod_pos_bound y 8 ltac:(lia)). lia.
Qed.
Lemma decK_cstr_unp : forall ly S U (W : world tfibsegs) mem md p l,
  ARU tfibsegs B ly S U W mem md -> cstr_ok tfibsegs W (unpoison U mem) p l ->
  (forall y, p <= y < p + Z.of_nat (length l) + 1 -> in_ush U (shadow_addr y) = false) ->
  cstr_ok tfibsegs W mem p l.
Proof.
intros ly S U W mem md p l H ((Hg & Hnz) & H4096 & Hcl & H32 & Ham & Hra & Hhv & Htl) HO.
pose proof asan_consts as (C1 & _).
assert (AV : forall a, p <= a < p + (Z.of_nat (length l) + 8) ->
  aview tfibsegs (w_H W) (unpoison U mem) a = aview tfibsegs (w_H W) mem a).
{ intros a Ha. destruct (decK_amem_data p (Z.of_nat (length l) + 8) a H4096 Ham Ha) as [Ha1 Ha2].
  exact (decK_unp_data ly S U W mem md a H Ha1 Ha2). }
split; [split; [|exact Hnz]|].
{ apply (garr8_frame tfibsegs _ _ p (l ++ [0]) Hg). intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
  apply (mbyte_of_aview tfibsegs). symmetry. apply AV. lia. }
split; [exact H4096|]. split; [exact Hcl|]. split; [exact H32|]. split; [exact Ham|].
split.
{ eapply range_addressable_agree; [|exact Hra]. intros x Hx. symmetry. apply aview_unpoison_out.
  change (shadow_of_addr SHADOW_OFF x) with (shadow_addr x). rewrite wz; [apply HO; lia|]. apply decK_sh_range. lia. }
split.
{ intros s Hs. exact (decK_vis_unp W mem U s (proj2 (proj2 H)) (Hhv s Hs)). }
intros a Ha. rewrite <- AV; [exact (Htl a Ha)|].
pose proof (Z.mod_pos_bound (p + Z.of_nat (length l)) 8 ltac:(lia)).
pose proof (Z.div_mod (p + Z.of_nat (length l)) 8 ltac:(lia)).
pose proof (Z.div_mod alloc_ceiling 4096 ltac:(lia)).
pose proof (proj2 YM05.alloc_ceiling_value). lia.
Qed.
Lemma decK_cstr_blk : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p l b m,
  ajournal tfibsegs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  In (b, m) (ablocks B ly S) -> In (b, m) (ablocks B ly' S') -> b <= p -> p + Z.of_nat (length l) + 1 <= b + m ->
  (forall a, p <= a < p + Z.of_nat (length l) + 1 -> ~ inFP FP a) ->
  cstr tfibsegs W mem p l -> 4096 <= p -> p + Z.of_nat (length l) + 1 <= alloc_ceiling ->
  Z.of_nat (length l) < 2 ^ 32 -> amem_range p (Z.of_nat (length l) + 8) ->
  cstr_ok tfibsegs W' mem' p l.
Proof.
intros STK sp0 FP ly S W mem md own ly' S' W' mem' md' k p l b m HJ Hin Hin' Hb Hbm HnF (Hg & Hnz) H4096 Hcl H32 Ham.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof HJ as (HAR' & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
assert (Hm : 0 < m) by lia.
assert (Hrq : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
split; [split; [|exact Hnz]|].
{ apply (garr8_frame tfibsegs _ _ p (l ++ [0]) Hg). intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
  apply (mbyte_of_aview tfibsegs). replace a with (b + (a - b)) by lia.
  apply (F2 b m (a - b) Hin Hin'); [rewrite Hrq; lia | replace (b + (a - b)) with a by lia; apply HnF; lia]. }
split; [exact H4096|]. split; [exact Hcl|]. split; [clear H32; (destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR' Hin') as (_ & _ & _ & _ & _ & _ & HmxL); unfold MALLOC_MAX in HmxL; lia)|]. split; [exact Ham|].
split.
{ apply (range_addressable_of_block tfibsegs B LAWS ly' S' W' mem' md' b m p _ HAR' Hin' Hb). rewrite Hrq. lia. }
split.
{ destruct (al_shadow _ _ LAWS ly' S' W' mem' md' b m HAR' Hin') as (_ & Hhv').
  apply (shadow_hull_vis_sub _ b (req_size m) p _ Hhv' Hb); rewrite ?Hrq; lia. }
intros a Ha. apply (block_word_tail_vis B ly' S' W' mem' md' b m HAR' Hin' Hm).
pose proof (word_end_mono (p + Z.of_nat (length l)) (b + m - 1) ltac:(lia)). lia.
Qed.
Lemma decK_heads_disj : forall ly S U (W : world tfibsegs) mem md b m x n,
  AR tfibsegs B ly S W mem md -> fs_heads B ly S U -> In (b, m) (ablocks B ly S) ->
  b + 16 <= x -> x + n <= b + req_size m ->
  forall r, In r U -> fst r + snd r <= x \/ x + n <= fst r.
Proof.
intros ly S U W mem md b m x n HAR FH Hb Hx Hxn r Hr.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct (FH r Hr) as (E16 & m' & Hm' & M16).
destruct r as [q s]. cbn [fst snd] in *. subst s.
destruct (Z.eq_dec q b) as [->|NE]; [left; lia|].
pose proof (sep_blocks tfibsegs B LAWS ly S W mem md q m' b m HAR Hm' Hb
  ltac:(intros E; injection E as E1 E2; exact (NE E1))) as D.
unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.
Lemma decK_new_disj : forall ly S (W : world tfibsegs) mem md (A : list (Z * Z)) b m x y,
  AR tfibsegs B ly S W mem md -> ablocks B ly S = A ++ [(x, y)] -> In (b, m) A ->
  zdisjoint (b, req_size m) (x, req_size y).
Proof.
intros ly S W mem md A b m x y HAR E Hin.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
assert (Hx : In (x, y) (ablocks B ly S)) by (rewrite E; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS ly S W mem md x y HAR Hx) as (_ & _ & _ & _ & _ & PW & _).
apply in_split in Hin as (l1 & l2 & EA). rewrite E, EA in PW.
apply (YCbq.pairwise_In2 zdisjoint _ _ _ (map (fun b0 : Z * Z => (fst b0, req_size (snd b0))) l1)
  (map (fun b0 : Z * Z => (fst b0, req_size (snd b0))) l2) [] PW).
rewrite !map_app. cbn [map]. rewrite <- app_assoc. reflexivity.
Qed.
Lemma decK_aro_unp : forall ly S U (W : world tfibsegs) mem md,
  ARU tfibsegs B ly S U W mem md -> arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) mem) ->
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) (unpoison U mem)).
Proof.
intros ly S U W mem md H HR a Hro Hno Her. pose proof (fs_segs_img a (decK_ro_img a Hro)) as Hb.
rewrite (decK_unp_data ly S U W mem md a H);
  [exact (HR a Hro Hno Her) | unfold FS_IMG_END in Hb; lia | left; unfold FS_IMG_END, SHADOW_OFF in *; lia].
Qed.

(* the caller's objects survive fuzz_malloc *)
Lemma decE_kept_malloc : forall d memC mdC regsC ly' S' U' W' mem' md' kc,
  dec_entry_ok B d ->
  ARU tfibsegs B (d_ly d) (d_S d) (d_U d) (d_W d) memC mdC ->
  dec_kept B d (d_W d) memC ->
  spZ regsC = d_sp d - DEC_F ->
  ajournal tfibsegs B STK_fuzz_malloc (spZ regsC) FS_PSTAT_FP (d_ly d) (d_S d) (d_W d) (unpoison (d_U d) memC) mdC []
    ly' S' W' (unpoison U' mem') md' kc ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' -> fs_heads B ly' S' U' ->
  ((U' = d_U d /\ ablocks B ly' S' = ablocks B (d_ly d) (d_S d)) \/
   (exists q, U' = d_U d ++ [(q - HEAD, HEAD)] /\
      ablocks B ly' S' = ablocks B (d_ly d) (d_S d) ++ [(q - HEAD, d_n d + HEAD)])) ->
  dec_kept B d W' mem'.
Proof.
intros d memC mdC regsC ly' S' U' W' mem' md' kc HE HARU HK Hsp HJ HUOK' HUPO' HFH' HBL.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & _ & C3 & _).
destruct HK as (HV & HWK & HCS & HRO).
destruct HE as (_ & HFH & _ & _ & _ & _ & HWS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPL).
pose proof HJ as (J1 & J2 & J3 & J4 & J5 & J6 & J7 & J8 & J9 & J10 & J11 & J12 & J13 & J14 & J15 & J16 & J17).
pose proof J15 as (_ & HSTK0 & Hceil & Hslo & Hshi & H47 & _ & _ & Htop2).
unfold d_sp, DEC_F in *.
destruct HPL as (_ & Hsl & Hlo & _ & Hot & _).
assert (HAR0 : AR tfibsegs B (d_ly d) (d_S d) (d_W d) (unpoison (d_U d) memC) mdC) by exact (proj1 HARU).
assert (HARU' : ARU tfibsegs B ly' S' U' W' mem' md') by (split; [exact J1 | split; assumption]).
assert (SEQ : forall a, spZ (d_regs d) <= a < 2 ^ 47 ->
  aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H (d_W d)) memC a).
{ intros a Ha.
  rewrite <- (fsw_aview_unpoison_high B ly' S' U' W' mem' md' a HARU' ltac:(lia)).
  rewrite <- (fsw_aview_unpoison_high B (d_ly d) (d_S d) (d_U d) (d_W d) memC mdC a HARU ltac:(lia)).
  apply J9; lia. }
assert (HRO' : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W') mem')).
{ intros a Hro Hno Her. pose proof (decK_ro_img a Hro) as Hi. pose proof (fs_segs_img a Hi) as Hb.
  assert (Hd : 0 <= a < 2 ^ 64 /\ (a < SHADOW_OFF \/ kHighMemBeg <= a)) by (unfold FS_IMG_END, SHADOW_OFF in *; lia).
  rewrite <- (decK_unp_data ly' S' U' W' mem' md' a HARU' (proj1 Hd) (proj2 Hd)).
  rewrite (J11 a Hi Hno Her (decK_ro_not_pstat a Hro) (fp_spares_closed FS_PSTAT_FP a decK_pstat_closed)).
  rewrite (decK_unp_data (d_ly d) (d_S d) (d_U d) (d_W d) memC mdC a HARU (proj1 Hd) (proj2 Hd)).
  exact (HRO a Hro Hno Her). }
unfold dec_kept, d_sp.
split.
{ intros k Hk. rewrite (mbyte_of_aview tfibsegs (w_H (d_W d)) (w_H W') memC mem' (d_lenp d + Z.of_nat k)
    (SEQ (d_lenp d + Z.of_nat k) ltac:(lia))).
  exact (HV k Hk). }
split.
{ intros a Ha Hn. destruct (HWK a Ha Hn) as (W1 & W2).
  assert (M1 : mbyte tfibsegs (mrestrict (w_H W') mem') a = mbyte tfibsegs (mrestrict (w_H (d_W d)) memC) a)
    by (apply (mbyte_of_aview tfibsegs); apply SEQ; lia).
  split; [rewrite M1; exact W1|].
  assert (Hni : ~ in_img tfibsegs a) by (intros Hi; pose proof (fs_segs_img a Hi); unfold FS_IMG_END in *; lia).
  pose proof (decE_restrict_of_mbyte _ _ _ _ a ltac:(lia) Hni M1) as RAW.
  assert (WEQ : writable_at tfibsegs (mrestrict (w_H (d_W d)) memC) a <->
                writable_at tfibsegs (mrestrict (w_H W') mem') a)
    by (unfold writable_at, wview; rewrite RAW; reflexivity).
  exact (iff_trans W2 WEQ). }
split; [|exact HRO'].
set (LEN := Z.of_nat (length (d_tb d))) in *.
assert (BLK : forall b m, In (b, m) (ablocks B (d_ly d) (d_S d)) -> b <= d_text d -> d_text d + LEN + 1 <= b + m ->
  (forall r, In r (d_U d) -> fst r + snd r <= d_text d \/ d_text d + LEN + 1 <= fst r) ->
  cstr_ok tfibsegs W' mem' (d_text d) (d_tb d)).
{ intros b m Hin Hb Hbm HU0.
  assert (Hin' : In (b, m) (ablocks B ly' S'))
    by (destruct HBL as [(_ & ->) | (q & _ & ->)]; [exact Hin | apply in_or_app; left; exact Hin]).
  pose proof HCS as ((Hg & Hnz) & H4096 & Hcl & H32 & Ham & _).
  assert (Hm : 0 < m) by lia.
  assert (Hrq : req_size m = m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
  assert (Hcu : cstr tfibsegs (d_W d) (unpoison (d_U d) memC) (d_text d) (d_tb d)).
  { split; [|exact Hnz]. apply (garr8_frame tfibsegs _ _ (d_text d) (d_tb d ++ [0]) Hg).
    intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
    apply (mbyte_of_aview tfibsegs).
    destruct (decK_amem_data (d_text d) (LEN + 8) a H4096 Ham ltac:(lia)) as [Ha1 Ha2].
    exact (decK_unp_data _ _ _ _ _ _ a HARU Ha1 Ha2). }
  assert (HC1 : cstr_ok tfibsegs W' (unpoison U' mem') (d_text d) (d_tb d)).
  { apply (decK_cstr_blk STK_fuzz_malloc (spZ regsC) FS_PSTAT_FP (d_ly d) (d_S d) (d_W d) (unpoison (d_U d) memC) mdC []
      ly' S' W' (unpoison U' mem') md' kc (d_text d) (d_tb d) b m HJ Hin Hin' Hb Hbm);
      [| exact Hcu | exact H4096 | exact Hcl | lia | exact Ham].
    intros a Ha Hf. apply (blk_img tfibsegs B LAWS _ _ _ _ _ b m a HAR0 Hin); [rewrite Hrq; lia | exact (decE_pstat_img a Hf)]. }
  apply (decK_cstr_unp ly' S' U' W' mem' md' _ _ HARU' HC1).
  intros y Hy. apply (decK_ush_out U' (d_text d) (LEN + 1)); [|lia].
  intros r Hr. destruct (upoison_ok_In B ly' S' U' r HUOK' Hr) as (A8 & _ & C8 & _).
  split; [exact A8|]. split; [exact C8|].
  destruct HBL as [(-> & _) | (q & -> & HBq)].
  - destruct (HU0 r Hr); lia.
  - apply in_app_or in Hr as [Hr | [<- | []]]; [destruct (HU0 r Hr); lia|].
    pose proof (decK_new_disj ly' S' W' _ md' (ablocks B (d_ly d) (d_S d)) b m (q - HEAD) (d_n d + HEAD)
      J1 HBq Hin) as D.
    unfold zdisjoint in D. cbn [fst snd] in D |- *.
    assert (Hn0 : 0 <= d_n d) by (unfold d_n, dec_size; pose proof (Z.div_pos (Z.of_nat (length (d_tb d))) 4 ltac:(lia) ltac:(lia)); lia).
    assert (Hrq' : req_size (d_n d + HEAD) = d_n d + HEAD) by (unfold req_size, HEAD in *; destruct (Z.eqb_spec (d_n d + 16) 0); lia).
    rewrite Hrq, Hrq' in D. unfold HEAD in *. lia. }
destruct HWS as [(E0 & _) | [(p0 & k0 & _ & (HinB & Hp16 & Hk0 & _) & Hps & Hpe) |
  [(p0 & k0 & _ & HinB & Hps & Hpe & HU) | (l & Hinl & _)]]].
- destruct (d_tb d); discriminate E0.
- rewrite length_app in Hpe. cbn [length] in Hpe.
  assert (Hrq : req_size (k0 + HEAD) = k0 + HEAD) by (unfold req_size, HEAD in *; destruct (Z.eqb_spec (k0 + 16) 0); lia).
  apply (BLK (p0 - HEAD) (k0 + HEAD) HinB); [unfold HEAD; lia | unfold LEN, HEAD; lia |].
  intros r Hr.
  destruct (decK_heads_disj (d_ly d) (d_S d) (d_U d) (d_W d) (unpoison (d_U d) memC) mdC (p0 - HEAD) (k0 + HEAD)
    (d_text d) (LEN + 1) HAR0 HFH HinB ltac:(unfold HEAD; lia) ltac:(rewrite Hrq; unfold LEN, HEAD; lia) r Hr); lia.
- rewrite length_app in Hpe. cbn [length] in Hpe.
  apply (BLK p0 k0 HinB Hps); [unfold LEN; lia|].
  intros r Hr. destruct (HU r Hr) as [X|X]; [left; exact X | right; rewrite length_app in X; cbn [length] in X; unfold LEN; lia].
- pose proof HIMG as (_ & HIM).
  pose proof (decK_aro_unp _ _ _ _ _ _ HARU HRO) as HROu0.
  destruct (HIM _ _ _ _ _ HAR0 HROu0) as (_ & _ & HS0 & _).
  pose proof (proj1 (proj1 (Forall_forall _ _) HS0 (d_text d, l) Hinl)) as HCl0. cbn [fst snd] in HCl0.
  destruct HCl0 as ((Hgl & Hnzl) & Hl4096 & Hlcl & _ & Hlam & _).
  pose proof HCS as ((Hg & Hnz) & _).
  assert (Hgl' : garr8 tfibsegs (mrestrict (w_H (d_W d)) memC) (d_text d) (l ++ [0])).
  { apply (garr8_frame tfibsegs _ _ (d_text d) (l ++ [0]) Hgl). intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
    apply (mbyte_of_aview tfibsegs).
    destruct (decK_amem_data (d_text d) (Z.of_nat (length l) + 8) a ltac:(lia) Hlam ltac:(lia)) as [Ha1 Ha2].
    symmetry. exact (decK_unp_data _ _ _ _ _ _ a HARU Ha1 Ha2). }
  pose proof (decK_cstr_same _ (d_tb d) l (d_text d) Hg Hgl' Hnz Hnzl) as Etl. subst l.
  pose proof (decK_aro_unp ly' S' U' W' mem' md' HARU' HRO') as HROu'.
  destruct (HIM _ _ _ _ _ J1 HROu') as (_ & _ & HS1 & _).
  pose proof (proj1 (proj1 (Forall_forall _ _) HS1 (d_text d, d_tb d) Hinl)) as HC1. cbn [fst snd] in HC1.
  apply (decK_cstr_unp ly' S' U' W' mem' md' _ _ HARU' HC1).
  intros y Hy.
  pose proof (decK_ro_strs_img (d_text d) (d_tb d) y Hinl Hy) as Hiy.
  pose proof (fs_segs_img y Hiy) as Hyb.
  assert (NB : forall p n, In (p, n) (ablocks B ly' S') -> ~ (p <= y < p + req_size n))
    by (intros p n Hpn Hr; exact (blk_img tfibsegs B LAWS _ _ _ _ _ p n y J1 Hpn Hr Hiy)).
  pose proof (ARU_shadow_out_block tfibsegs B ly' S' U' W' mem' md' y HARU' ltac:(unfold FS_IMG_END in Hyb; lia) NB) as X.
  rewrite wz in X; [exact X|]. apply decK_sh_range. unfold FS_IMG_END in Hyb. lia.
Qed.

Hypothesis HSTRLEN : astrlen_realizesU tfibsegs B PC_strlen.
Hypothesis HMALLOC : fuzz_malloc_spec tfibsegs B.

Lemma decE_spine : forall d, dec_entry_ok B d ->
  (forall W' ly' S' regs' mem' md',
     d_cnt d = d_fail d -> decE_res B d W' ly' S' (d_U d) regs' mem' md' 0 -> getr regs' 10 = w64 0 ->
     ablocks B ly' S' = ablocks B (d_ly d) (d_S d) ->
     fs_glob tfibsegs W' mem' (d_live d) (d_peak d) (d_cnt d + 1) SIZE_MAXZ ->
     SRr tfibsegs W' (mkCfg (YK11.mkst regs' (Z_to_bv 64 DEC_RA_MALLOC) mem' (YK11.seg_rom tfibsegs)) md') (dec_post B d)) ->
  (forall q W' ly' S' regs' mem' md',
     d_cnt d <> d_fail d -> decE_res B d W' ly' S' (d_U d ++ [(q - HEAD, HEAD)]) regs' mem' md' 1 ->
     getr regs' 10 = w64 q -> 4096 + HEAD <= q ->
     ablocks B ly' S' = ablocks B (d_ly d) (d_S d) ++ [(q - HEAD, d_n d + HEAD)] ->
     fs_heads B ly' S' (d_U d ++ [(q - HEAD, HEAD)]) ->
     fs_rblock tfibsegs B ly' S' W' mem' q (d_n d) ->
     range_addressable (aview tfibsegs (w_H W') mem') SHADOW_OFF q (d_n d) ->
     fs_glob tfibsegs W' mem' (d_live d + d_n d) (Z.max (d_peak d) (d_live d + d_n d)) (d_cnt d + 1) (d_fail d) ->
     SRr tfibsegs W' (mkCfg (YK11.mkst regs' (Z_to_bv 64 DEC_RA_MALLOC) mem' (YK11.seg_rom tfibsegs)) md') (dec_post B d)) ->
  SRr tfibsegs (d_W d) (cfg_at tfibsegs A_preset_base64_decode (d_regs d) (d_mem d) (d_md d)) (dec_post B d).
Proof.
intros d Hd KN KQ.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : STK_preset_base64_decode = ltac:(let v := eval vm_compute in STK_preset_base64_decode in exact v)) by reflexivity.
assert (FM : STK_fuzz_malloc = ltac:(let v := eval vm_compute in STK_fuzz_malloc in exact v)) by reflexivity.
assert (FR : STK_RT_STR = ltac:(let v := eval vm_compute in STK_RT_STR in exact v)) by reflexivity.
assert (FE : ESTACK = 4096) by reflexivity.
pose proof Hd as Hd0.
destruct d as [ly S U W regs mem md ch ot text lenp tb live peak cnt fail v FP].
unfold dec_entry_ok in Hd0.
cbn [d_ly d_S d_U d_W d_regs d_mem d_md d_ch d_ot d_text d_lenp d_tb d_live d_peak d_cnt d_fail d_v d_FP] in Hd0.
cbn [d_ly d_S d_U d_W d_regs d_mem d_md d_ch d_ot d_text d_lenp d_tb d_live d_peak d_cnt d_fail d_v d_FP d_n] in KN, KQ |- *.
set (d := mkDE ly S U W regs mem md ch ot text lenp tb live peak cnt fail v FP) in *.
destruct Hd0 as (HPRE & HH & HFRL & H10 & H11 & HCS & HWS & HBO & HLEN & Hl8 & HV & Hv & HDJ & HGL & HEV & HLV
  & HLIVE & HCNT & HPL).
destruct HPRE as (HPREU & HRO).
pose proof (fsw_ARU B STK_preset_base64_decode _ _ _ _ _ _ _ _ HPREU) as HARU0.
pose proof HPREU as (HAP & HUOK & HUPO).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HCS as (_ & Htx4 & Htxc & Htx32 & _).
destruct HPL as (HFP & Hsl & Hlo & Hot16 & Hottop & Hpot & Hchl).
assert (Hl0 : 0 <= lenp) by lia.
assert (Hl64 : lenp + 8 <= 2 ^ 64) by lia.
assert (Hlpl : lenp + 8 <= alloc_ceiling \/ spZ regs <= lenp) by (right; exact Hsl).
assert (Hotb : spZ regs <= ot <= 2 ^ 47) by lia.
assert (Hsplo : alloc_ceiling + 128 <= spZ regs) by (rewrite FS in Hslo; lia).
assert (HK0 : dec_kept B d W mem).
{ split; [exact HV|]. split; [intros a _ _; split; [reflexivity | tauto]|]. split; [exact HCS | exact HRO]. }
(* ---- entry state and the journal at the entry sp ---- *)
assert (HS : st_ok tfibsegs (Ereg regs fs_extraT) (fss0T A_preset_base64_decode 128)
  (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 A_preset_base64_decode) mem (YK11.seg_rom tfibsegs)))).
{ apply (fsw_entryT B STK_preset_base64_decode 128 ly S U W regs mem md ch A_preset_base64_decode
    (proj1 HSS) (proj2 HSS) HPREU); [rewrite FS; lia | vm_compute; reflexivity]. }
set (E := Ereg regs fs_extraT) in HS.
assert (E2 : bv_unsigned (ew E 2) = spZ regs)
  by (unfold E; rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl); reflexivity).
assert (HJ : ajournal tfibsegs B STK_preset_base64_decode (spZ regs) FP ly S W (unpoison U mem) md []
               ly S W (unpoison U mem) md 0)
  by exact (ajournal_init tfibsegs B STK_preset_base64_decode FP ly S W regs (unpoison U mem) md ch HAP).
(* ---- run 1: entry -> PC_strlen ---- *)
unfold cfg_at.
fsw_aj_run_toU fsw_wr_tbl_ok HS HJ HARU0 PC_strlen.
{ cbv [fss0T fsT_regions ss_mem].
  eapply awr_ok_cons_stack with (n := 2%nat);
    [reflexivity | exact E2 | cbv [fstk YP09.r_wlo]; rewrite FS; lia | cbv [fstk YP09.r_whi]; lia |].
  apply awr_ok_cons_ro; [cbv [fs_got_region YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_cons_ro; [cbv [fs_bcell_region YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_nil. }
rename ms into ms1.
lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (mdT := m) in * end.
assert (AV1 : decE_avk d W mem (ms_mem ms1)).
{ apply (decE_frame_avk d W E _ mem (ms_mem ms1) HF).
  intros r a Hin Ha. cbv [fss0T fsT_regions ss_mem In] in Hin.
  destruct Hin as [<-|[<-|[<-|[]]]];
    cbv [fstk fs_got_region fs_bcell_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    try rewrite E2 in Ha; change (d_sp d) with (spZ regs); rewrite FS in Hslo; lia. }
assert (Hspc : alloc_ceiling <= d_sp d) by (change (d_sp d) with (spZ regs); lia).
assert (Hotc : d_ot d <= 2 ^ 47) by (change (d_ot d) with ot; lia).
pose proof (decE_kept_avk B d W mem (ms_mem ms1) Hspc Hl0 Hlpl Hl64 Hotc AV1 HK0) as HK1.
assert (AVB1 : forall a, 0 <= a < alloc_ceiling -> aview tfibsegs (w_H W) (ms_mem ms1) a = aview tfibsegs (w_H W) mem a)
  by (intros a Ha; apply AV1; lia).
pose proof (decE_glob_av W mem (ms_mem ms1) live peak cnt fail AVB1 HGL) as HG1.
pose proof (fsw_reg_lit _ E _ ms1 1%bv DEC_RA_STRLEN HS ltac:(vm_compute; reflexivity)
  ltac:(unfold DEC_RA_STRLEN; lia)) as R1.
pose proof (fsw_reg_off _ E _ ms1 2%bv 2 (-128) (spZ regs) HS ltac:(vm_compute; reflexivity) E2 ltac:(lia)) as R2.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms1 3%bv 3%bv 3 HS ltac:(vm_compute; reflexivity) eq_refl) as R3.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms1 4%bv 4%bv 4 HS ltac:(vm_compute; reflexivity) eq_refl) as R4.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms1 8%bv 11%bv 11 HS ltac:(vm_compute; reflexivity) eq_refl) as R8.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms1 10%bv 10%bv 10 HS ltac:(vm_compute; reflexivity) eq_refl) as R10.
pose proof (fsw_reg_atom _ regs fs_extraT _ ms1 18%bv 10%bv 10 HS ltac:(vm_compute; reflexivity) eq_refl) as R18.
pose proof (fsw_reg_extra _ regs fs_extraT _ ms1 20%bv 0 HS ltac:(vm_compute; reflexivity)) as R20.
cbn [nth fs_extraT] in R20.
assert (RK1 : forall r, In r decE_kregs -> getr (ms_regs ms1) r = getr regs r).
{ intros r Hr. cbv [decE_kregs In] in Hr. repeat (destruct Hr as [<-|Hr]); [..|destruct Hr];
  lazymatch goal with |- getr _ ?r = _ =>
    let n := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
    exact (fsw_reg_atom _ regs fs_extraT _ ms1 r r n HS ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
  end. }
assert (Hspt : spZ (ms_regs ms1) = spZ regs - 128) by (unfold spZ at 1; rewrite R2; lia).
assert (HFR1 : dec_frame_ok W (ms_mem ms1) (spZ regs - 128) regs).
{ apply decE_frame_of_cs0.
  lazymatch type of HS with st_ok _ _ ?ss _ =>
    pose proof (fsw_region_nth E ss (restrict (w_H W) ms1) 0 _ HS eq_refl) as HR0 end.
  destruct HR0 as (_ & _ & _ & HC0). cbn [YP09.r_base YP09.r_chunks base_val ms_mem restrict] in HC0.
  rewrite E2 in HC0. exact HC0. }
clear HF HFr HG.
(* ---- the call of strlen (pc PC_strlen, ra 0x84c9c, a0 = text) ---- *)
pose proof HK1 as (K1v & K1w & K1c & K1r).
pose proof HARU0 as (HAR1 & HUOK0 & HPO1).
assert (HRO1u : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) (unpoison U (ms_mem ms1)))).
{ intros a Ha Ho He.
  assert (Hb : 0 <= a < SHADOW_OFF).
  { destruct Ha as [(sg & Hin & Hw & Hr) | Hr]; [|unfold FS_RLO, FS_RHI in Hr; unfold SHADOW_OFF; lia].
    assert (Hi : in_img tfibsegs a) by (exists sg; split; [exact Hin | exact Hr]).
    pose proof (fs_segs_img a Hi) as Hl. unfold FS_IMG_END in Hl. unfold SHADOW_OFF; lia. }
  assert (Hb64 : 0 <= a < 2 ^ 64) by (unfold SHADOW_OFF in Hb; lia).
  rewrite (decK_unp_data ly S U W (ms_mem ms1) mdT a HARU0 Hb64 (or_introl (proj2 Hb))). exact (K1r a Ha Ho He). }
assert (HROM1 : rom_view tfibsegs W (ms_mem ms1)).
{ pose proof HIMG as (_ & HIM).
  destruct (HIM ly S W (unpoison U (ms_mem ms1)) mdT HAR1 HRO1u) as (HRV & _).
  intros a Ha. pose proof Ha as (sg & Hin & Hw & Hr).
  assert (Hi : in_img tfibsegs a) by (exists sg; split; [exact Hin | exact Hr]).
  pose proof (fs_segs_img a Hi) as Hl.
  assert (Hb : 0 <= a < SHADOW_OFF) by (unfold FS_IMG_END in Hl; unfold SHADOW_OFF; lia).
  assert (Hb64 : 0 <= a < 2 ^ 64) by (unfold SHADOW_OFF in Hb; lia).
  rewrite <- (decK_unp_data ly S U W (ms_mem ms1) mdT a HARU0 Hb64 (or_introl (proj2 Hb))). exact (HRV a Ha). }
assert (HPRE1 : ecall_preU_k tfibsegs B STK_RT_STR ly S U W (ms_regs ms1) (ms_mem ms1) mdT).
{ apply (fsw_ecall_preU_k_at B STK_preset_base64_decode (spZ regs) FP ly S W (unpoison U mem) md [] ly S U W
    (ms_mem ms1) mdT 0 (ms_regs ms1) (-128) STK_RT_STR HJ HARU0).
  - rewrite Hspt. lia.
  - reflexivity.
  - lia.
  - rewrite FE, FS. lia.
  - rewrite FR. lia.
  - rewrite FR, FS. lia.
  - rewrite R1. apply ret_ok_even. rewrite unsigned_lit_small by (unfold DEC_RA_STRLEN; lia). reflexivity.
  - rewrite R3. exact Hgp.
  - rewrite R4. exact Htp. }
assert (H10T : getr (ms_regs ms1) 10 = w64 text) by (rewrite R10; exact H10).
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms1 HS eq_refl). cbn [ss_pc].
eapply SRr_bind.
{ apply (fsw_intrin_atU B STK_preset_base64_decode (spZ regs) FP ly S W (unpoison U mem) md [] ly S U W (ms_mem ms1)
    mdT 0 U (fun a => spZ (ms_regs ms1) - STK_RT_STR <= a < spZ (ms_regs ms1)) (Z_to_bv 64 DEC_RA_STRLEN) _
    (fun regs2 mem2 md2 => aregs_preserved (ms_regs ms1) regs2 /\ getr regs2 10 = w64 (Z.of_nat (length tb)) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (ms_regs ms1) - STK_RT_STR <= a < spZ (ms_regs ms1)) ->
          aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) (ms_mem ms1) a)) HJ).
  - eapply SRr_mono; [exact (HSTRLEN ly S U W (ms_regs ms1) (ms_mem ms1) mdT text tb HPRE1 HROM1 H10T K1c)|].
    intros W2 c2 _ (EW & regs2 & mem2 & md2 & v0 & Ec & HAR2 & PO2 & HP2 & Hsame & H10v & Hv0 & Hlen & Hfr & Hgr).
    split; [exact EW|]. exists regs2, mem2, md2.
    split.
    { rewrite Ec. unfold cfg_at, raZ, w64. rewrite R1, unsigned_lit_small by (unfold DEC_RA_STRLEN; lia).
      reflexivity. }
    split; [split; [exact HAR2 | split; [exact HUOK0 | exact PO2]]|].
    split; [exact Hsame|].
    split.
    { intros a Ha Hn. destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:Eu.
      - apply (aview_unpoison_in tfibsegs). exact Eu.
      - rewrite (aview_unpoison_out tfibsegs (w_H W) U mem2 a Eu),
          (aview_unpoison_out tfibsegs (w_H W) U (ms_mem ms1) a Eu).
        exact (Hfr a Ha Hn). }
    split.
    { intros a (Hh & b & Hb). split; [exact Hh|]. unfold unpoison in Hb |- *.
      destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))); [eexists; reflexivity|].
      destruct (Hgr a (conj Hh (ex_intro _ b Hb))) as (_ & b' & Hb'). exists b'. exact Hb'. }
    split; [exact HP2|]. split; [rewrite H10v, Hlen; reflexivity|]. exact Hfr.
  - intros a Ha. left; left. rewrite Hspt, FR in Ha. rewrite FS. lia. }
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HARU2 & HP2 & H102 & Hfr2).
(* ---- the resumed state at 0x84c9c ---- *)
assert (RK2 : forall r, In r decE_kregs -> getr regs2 r = getr regs r).
{ intros r Hr. rewrite <- (RK1 r Hr). apply (fsw_pres _ _ r HP2).
  cbv [decE_kregs In] in Hr. repeat (destruct Hr as [<-|Hr]); [..|destruct Hr]; decE_cs_side. }
assert (Hsp2 : spZ regs2 = spZ regs - 128).
{ unfold spZ at 1. rewrite (fsw_pres _ _ 2%bv HP2) by decE_cs_side. exact Hspt. }
assert (KEEP2 : forall a, spZ regs - 128 <= a < spZ regs ->
  mbyte tfibsegs (mrestrict (w_H W) mem2) a = mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms1)) a).
{ intros a Ha. apply (mbyte_of_aview tfibsegs). apply Hfr2; [lia|]. rewrite Hspt, FR. lia. }
assert (AV2 : decE_avk d W (ms_mem ms1) mem2).
{ intros a Ha Hs. apply Hfr2; [exact Ha|]. rewrite Hspt, FR. change (d_sp d) with (spZ regs) in Hs. lia. }
pose proof (decE_kept_avk B d W (ms_mem ms1) mem2 Hspc Hl0 Hlpl Hl64 Hotc AV2 HK1) as HK2.
assert (AVB2 : forall a, 0 <= a < alloc_ceiling -> aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) (ms_mem ms1) a)
  by (intros a Ha; apply AV2; lia).
pose proof (decE_glob_av W _ mem2 live peak cnt fail AVB2 HG1) as HG2.
assert (HPD2 : pairwise_disjoint (Ereg regs2 (fs_extraT ++ decE_xs d)) (fsT_ret_regions 128 decE_cs [])).
{ apply pairwise_disjoint_of_extents.
  unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, extent_of_region.
  cbn [map app YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl). change (bv_unsigned (getr regs2 2)) with (spZ regs2). rewrite Hsp2.
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia]. }
assert (HS2 : st_ok tfibsegs (Ereg regs2 (fs_extraT ++ decE_xs d)) (fss_retT DEC_RA_STRLEN 128 decE_cs [] [])
  (restrict (w_H W) (YK11.mkst regs2 (Z_to_bv 64 DEC_RA_STRLEN) mem2 (YK11.seg_rom tfibsegs)))).
{ apply (fsw_resume_after_rtU_args B STK_preset_base64_decode (spZ regs) FP ly S W (unpoison U mem) md [] ly S U W
    mem2 md2 0 (ms_regs ms1) regs2 (ms_mem ms1) 128 (decE_xs d) decE_cs [] [] DEC_RA_STRLEN (proj1 HSS) (proj2 HSS)
    HJ2 HARU2 HP2 Hspt).
  - lia.
  - rewrite FS. lia.
  - reflexivity.
  - vm_compute. reflexivity.
  - repeat constructor; cbn; lia.
  - exact (decE_chunks_of_frame d W (ms_mem ms1) (spZ regs - 128) regs2 RK2 HFR1).
  - exact KEEP2.
  - constructor.
  - exact HPD2.
  - exact I. }
clear HS.
(* ---- run 2: 0x84c9c -> A_fuzz_malloc ---- *)
fsw_aj_run_toU fsw_wr_tbl_ok HS2 HJ2 HARU2 A_fuzz_malloc.
{ cbv [fss_retT fsT_ret_regions ss_mem app].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -128);
    [reflexivity
    | rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl); change (bv_unsigned (getr regs2 2)) with (spZ regs2); lia
    | cbv [fstk_ret YP09.r_wlo]; rewrite FS; lia | cbv [fstk_ret YP09.r_whi]; lia |].
  apply awr_ok_cons_ro; [cbv [fs_got_region YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_cons_ro; [cbv [fs_bcell_region YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_nil. }
rename ms into ms3.
lazymatch goal with |- SRr _ _ (mkCfg _ ?m) _ => set (mdC := m) in * end.
assert (AV3 : decE_avk d W mem2 (ms_mem ms3)).
{ apply (decE_frame_avk d W _ _ mem2 (ms_mem ms3) HF).
  intros r a Hin Ha. cbv [fss_retT fsT_ret_regions ss_mem app In] in Hin.
  destruct Hin as [<-|[<-|[<-|[]]]];
    cbv [fstk_ret fs_got_region fs_bcell_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    try (rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl) in Ha;
         change (bv_unsigned (getr regs2 2)) with (spZ regs2) in Ha);
    change (d_sp d) with (spZ regs); lia. }
clear HF HFr HG.
pose proof (decE_kept_avk B d W mem2 (ms_mem ms3) Hspc Hl0 Hlpl Hl64 Hotc AV3 HK2) as HK3.
assert (AVB3 : forall a, 0 <= a < alloc_ceiling -> aview tfibsegs (w_H W) (ms_mem ms3) a = aview tfibsegs (w_H W) mem2 a)
  by (intros a Ha; apply AV3; lia).
pose proof (decE_glob_av W _ _ live peak cnt fail AVB3 HG2) as HG3.
pose proof (fsw_reg_lit _ _ _ ms3 1%bv DEC_RA_MALLOC HS2 ltac:(vm_compute; reflexivity)
  ltac:(unfold DEC_RA_MALLOC; lia)) as R1c.
assert (PC : forall r : bv 5, In r decE_csl ->
  getr (ms_regs ms3) r = getr (ms_regs ms1) r).
{ intros r Hr. cbv [decE_csl In] in Hr. repeat (destruct Hr as [<-|Hr]); [..|destruct Hr];
  lazymatch goal with |- getr _ ?r = _ =>
    let n := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
    rewrite (fsw_reg_atom _ regs2 _ _ ms3 r r n HS2 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity));
    apply (fsw_pres _ _ r HP2); decE_cs_side end. }
assert (I2 : In (2%bv : bv 5) decE_csl) by (cbv [decE_csl]; decE_in).
assert (I3 : In (3%bv : bv 5) decE_csl) by (cbv [decE_csl]; decE_in).
assert (I4 : In (4%bv : bv 5) decE_csl) by (cbv [decE_csl]; decE_in).
assert (I8 : In (8%bv : bv 5) decE_csl) by (cbv [decE_csl]; decE_in).
assert (I18 : In (18%bv : bv 5) decE_csl) by (cbv [decE_csl]; decE_in).
assert (I20 : In (20%bv : bv 5) decE_csl) by (cbv [decE_csl]; decE_in).
assert (Hspc3 : spZ (ms_regs ms3) = spZ regs - 128) by (unfold spZ at 1; rewrite (PC 2%bv I2); exact Hspt).
assert (Hs0c : s0Z (ms_regs ms3) = lenp).
{ unfold s0Z. rewrite (PC 8%bv I8), R8, H11. unfold w64. rewrite unsigned_lit_small by lia. reflexivity. }
assert (R10c : getr (ms_regs ms3) 10 = w64 (dec_size tb)).
{ lazymatch type of HS2 with st_ok _ _ ?ss _ =>
    rewrite (st_ok_restrict_reg tfibsegs (w_H W) _ ss ms3 10%bv HS2);
    assert (Hr10 : sr_get (ss_regs ss) 10%bv = decE_size_sv) by (vm_compute; reflexivity) end.
  rewrite Hr10. unfold w64, dec_size. apply decE_size_den; [|lia].
  rewrite (ew_Ereg_nat regs2 _ 10 10%bv eq_refl). exact H102. }
assert (HCH : exists ch1, achain ly (aview tfibsegs (w_H W) (unpoison U (ms_mem ms3))) (spZ regs - 128) lenp ch1).
{ destruct Hchl as (chl & Hchl). exists chl.
  apply (achain_lower ly _ (spZ regs) (spZ regs - 128) lenp chl); [|lia].
  apply (achain_kept ly (aview tfibsegs (w_H W) (unpoison U mem)) _ (spZ regs) lenp chl (spZ regs) Hchl); [lia | lia |].
  intros a Ha. pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & J9 & _). apply J9; lia. }
destruct HCH as (ch1 & Hach).
pose proof HARU2 as (HAR3 & HUOK3 & HPO3).
pose proof HK3 as (K3v & K3w & K3c & K3r).
assert (HPREc : fpreU tfibsegs B STK_fuzz_malloc ly S U W (ms_regs ms3) (ms_mem ms3) mdC ch1).
{ apply (fsw_fpreU_atFP B STK_preset_base64_decode (spZ regs) FP ly S U W (unpoison U mem) md [] ly S W
    (ms_mem ms3) mdC 0 (ms_regs ms3) STK_fuzz_malloc (-128) ch1 HJ2 HARU2 K3r).
  - rewrite Hspc3. lia.
  - reflexivity.
  - lia.
  - rewrite FM. lia.
  - rewrite FS, FM. lia.
  - rewrite R1c. apply ret_ok_even. rewrite unsigned_lit_small by (unfold DEC_RA_MALLOC; lia). reflexivity.
  - unfold raZ. rewrite R1c, unsigned_lit_small by (unfold DEC_RA_MALLOC; lia). unfold DEC_RA_MALLOC. lia.
  - rewrite (PC 3%bv I3), R3. exact Hgp.
  - rewrite (PC 4%bv I4), R4. exact Htp.
  - rewrite Hspc3, Hs0c. exact Hach. }
assert (HN1 : 0 <= Z.of_nat (length tb) / 4 <= 2 ^ 26)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (Hn1 : 1 <= dec_size tb) by (unfold dec_size; lia).
assert (Hn0 : 0 < dec_size tb) by lia.
assert (Hn2 : dec_size tb + HEAD < MALLOC_MAX) by (unfold dec_size, HEAD, MALLOC_MAX; lia).
assert (Hev1 : 1 <= dec_ev tb)
  by (unfold dec_ev, EV_fuzz_malloc, EV_preset_base64_decode; destruct (WriterSpec.b64_dec tb); lia).
assert (HEV1 : st_nev S + 1 <= EV_MAX) by lia.
assert (HLV1 : blocks_bytes S + (dec_size tb + HEAD) <= LIVE_MAX) by exact HLV.
assert (HFPS : fsw_fp_sub B ly S ly S [] FP FS_PSTAT_FP).
{ intros a Ha. right; right; left. split; [|exact (decE_pstat_img a Ha)]. rewrite HFP. exact Ha. }
assert (HFR3 : dec_frame_ok W (ms_mem ms3) (spZ regs - 128) regs).
{ apply (decE_frame_of_chunks d W (ms_mem ms3) (spZ regs - 128) regs2 RK2).
  lazymatch type of HS2 with st_ok _ _ ?ss _ =>
    pose proof (fsw_region_nth _ ss (restrict (w_H W) ms3) 0 _ HS2 eq_refl) as HR0 end.
  destruct HR0 as (_ & _ & _ & HC0). cbn [YP09.r_base YP09.r_chunks base_val ms_mem restrict] in HC0.
  rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl) in HC0. change (bv_unsigned (getr regs2 2)) with (spZ regs2) in HC0.
  rewrite Hsp2 in HC0. exact HC0. }
assert (AFTER : forall W' ly' S' U' regs' mem' md' kc,
  ajournal tfibsegs B STK_fuzz_malloc (spZ (ms_regs ms3)) FS_PSTAT_FP ly S W (unpoison U (ms_mem ms3)) mdC []
    ly' S' W' (unpoison U' mem') md' kc ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' -> fs_heads B ly' S' U' ->
  aregs_preserved (ms_regs ms3) regs' ->
  ((U' = U /\ ablocks B ly' S' = ablocks B ly S) \/
   (exists q, U' = U ++ [(q - HEAD, HEAD)] /\ ablocks B ly' S' = ablocks B ly S ++ [(q - HEAD, dec_size tb + HEAD)])) ->
  decE_res B d W' ly' S' U' regs' mem' md' (0 + kc)).
{ intros W' ly' S' U' regs' mem' md' kc HJc OK' PO' HH' HP' HAR'.
  assert (PB : forall r : bv 5, In r decE_csl ->
    getr regs' r = getr (ms_regs ms1) r).
  { intros r Hr. rewrite <- (PC r Hr). apply (fsw_pres _ _ r HP').
    cbv [decE_csl In] in Hr. repeat (destruct Hr as [<-|Hr]); [..|destruct Hr]; decE_cs_side. }
  assert (RKc : forall r, In r decE_kregs -> getr regs' r = getr regs r).
  { intros r Hr. rewrite <- (RK1 r Hr). apply PB.
    cbv [decE_kregs In] in Hr. cbv [decE_csl]. repeat (destruct Hr as [<-|Hr]); [..|destruct Hr]; decE_in. }
  assert (Hspr : spZ regs' = spZ regs - 128) by (unfold spZ at 1; rewrite (PB 2%bv I2); exact Hspt).
  assert (HPD' : pairwise_disjoint (Ereg regs' (fs_extraT ++ decE_xs d)) (fsT_ret_regions 128 decE_cs [])).
  { apply pairwise_disjoint_of_extents.
    unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, extent_of_region.
    cbn [map app YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite (ew_Ereg_nat regs' _ 2 2%bv eq_refl). change (bv_unsigned (getr regs' 2)) with (spZ regs'). rewrite Hspr.
    unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia]. }
  assert (Hf1 : 0 < 128) by lia. assert (Hf2 : 0 <= STK_fuzz_malloc) by (rewrite FM; lia).
  assert (Hf3 : STK_fuzz_malloc + 128 <= STK_preset_base64_decode) by (rewrite FS, FM; lia).
  assert (Hf4 : 128 mod 16 = 0) by reflexivity.
  assert (Hwf : regions_wf (fsT_ret_regions 128 decE_cs []) = true) by (vm_compute; reflexivity).
  assert (Hbd : Forall (fun c => 0 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= 128) decE_cs)
    by (repeat constructor; cbn; lia).
  pose proof (decE_chunks_of_frame d W (ms_mem ms3) (spZ regs - 128) regs' RKc HFR3) as Hcs.
  assert (Hrs : Forall (region_ok tfibsegs (Ereg regs' (fs_extraT ++ decE_xs d)) (mrestrict (w_H W') mem')) [])
    by constructor.
  assert (Hgf : atoms_ok (Ereg regs' (fs_extraT ++ decE_xs d)) []) by exact I.
  pose proof (fsw_after_callFPU_args B STK_preset_base64_decode (spZ regs) FP [] ly S U W mem md W ly S U (ms_mem ms3)
    mdC 0 STK_fuzz_malloc FS_PSTAT_FP 128 (ms_regs ms3) ly' S' U' W' regs' mem' md' kc (decE_xs d) decE_cs [] []
    DEC_RA_MALLOC (proj1 HSS) (proj2 HSS) HJ2 HARU2 HJc HFPS OK' PO' HP' Hspc3 Hf1 Hf2 Hf3 Hf4 Hwf Hbd Hcs Hrs HPD' Hgf)
    as (HJ' & HARU' & HS').
  pose proof (decE_kept_malloc d (ms_mem ms3) mdC (ms_regs ms3) ly' S' U' W' mem' md' kc Hd HARU2 HK3 Hspc3 HJc OK' PO' HH' HAR')
    as HK'.
  split; [exact HJ'|]. split; [exact HARU'|]. split; [exact HS'|].
  split; [exact Hspr|].
  split; [rewrite (PB 3%bv I3); exact R3|].
  split; [rewrite (PB 4%bv I4); exact R4|].
  split; [rewrite (PB 8%bv I8), R8; exact H11|].
  split; [rewrite (PB 18%bv I18), R18; exact H10|].
  split; [rewrite (PB 20%bv I20), R20; reflexivity|].
  split; [exact RKc|].
  exact HK'. }
(* ---- the call ---- *)
rewrite (st_ok_restrict_mkst tfibsegs (w_H W) _ _ ms3 HS2 eq_refl). cbn [ss_pc].
eapply SRr_bind; [exact (HMALLOC ly S U W (ms_regs ms3) (ms_mem ms3) mdC ch1 (dec_size tb) live peak cnt fail
  HPREc HH R10c Hn1 Hn2 HG3 (fun _ => HLIVE) HCNT HEV1 (fun _ => HLV1))|].
intros W' c' _ [(Hcf & HQ1) | (Hcf & res & HQ2)].
- destruct HQ1 as (ly' & S' & regs' & mem' & md' & -> & HJc & OK' & PO' & HP' & H10' & Hbl' & HH' & HG').
  rewrite R1c.
  exact (KN W' ly' S' regs' mem' md' Hcf
    (AFTER W' ly' S' U regs' mem' md' 0 HJc OK' PO' HH' HP' (or_introl (conj eq_refl Hbl'))) H10' Hbl' HG').
- destruct HQ2 as (ly' & S' & regs' & mem' & md' & -> & HJc & OK' & PO' & HP' & H10' & Hres4 & Hbl' & HH' & Hrb & Hra'
    & HG').
  rewrite R1c.
  exact (KQ res W' ly' S' regs' mem' md' Hcf
    (AFTER W' ly' S' _ regs' mem' md' 1 HJc OK' PO' HH' HP' (or_intror (ex_intro _ res (conj eq_refl Hbl'))))
    H10' Hres4 Hbl' HH' (Hrb Hn0) Hra' HG').
Qed.

Lemma dec_entry_ok_stage : dec_stage_entry B.
Proof.
intros d Hd Hk. apply (decE_spine d Hd).
- intros W' ly' S' regs' mem' md' Hcf Hres H10 Hbl HG.
  exact (decE_null d W' ly' S' regs' mem' md' Hd Hcf Hres H10 Hbl HG).
- intros q W' ly' S' regs' mem' md' Hcf Hres H10 Hq Hbl HH Hrb Hra HG.
  exact (decE_nonnull d q W' ly' S' regs' mem' md' Hd Hcf Hres H10 Hq Hbl HH Hrb Hra HG Hk).
Qed.
End P.

(* ================= the loop: shared states and arithmetic (ports of lib/A/FSW_dec_L0 .. L3) ================= *)
Definition DEC_EXIT_PAD : Z := 0x84e34.          (* `blt 2, s8` of the NUL exit *)
Definition DEC_CEIL : Z := 0x7fffff800000.       (* the upper bound of alloc_ceiling (YCbq.v asan_consts) *)

(* the frame chunks at a cut: lenp (atom 33), ~q (atom 34), the entry value of nth j dec_saved (atom 35 + j) *)
Definition decL_cs : list YP09.chunk :=
  [YP09.mkChunk 8 (CVal 8 (SOff 33 0)); YP09.mkChunk 16 (CVal 8 (SOff 34 0));
   YP09.mkChunk 24 (CVal 8 (SOff 35 0)); YP09.mkChunk 32 (CVal 8 (SOff 36 0)); YP09.mkChunk 40 (CVal 8 (SOff 37 0));
   YP09.mkChunk 48 (CVal 8 (SOff 38 0)); YP09.mkChunk 56 (CVal 8 (SOff 39 0)); YP09.mkChunk 64 (CVal 8 (SOff 40 0));
   YP09.mkChunk 72 (CVal 8 (SOff 41 0)); YP09.mkChunk 80 (CVal 8 (SOff 42 0)); YP09.mkChunk 88 (CVal 8 (SOff 43 0));
   YP09.mkChunk 96 (CVal 8 (SOff 44 0)); YP09.mkChunk 104 (CVal 8 (SOff 45 0)); YP09.mkChunk 112 (CVal 8 (SOff 46 0));
   YP09.mkChunk 120 (CVal 8 (SOff 47 0))].
Definition decL_xs (d : DE) (q : Z) : list word :=
  Z_to_bv 64 (d_lenp d) :: Z_to_bv 64 (DEC_M1 - q) :: map (fun r => getr (d_regs d) r) dec_saved.
(* the text byte at the head: read through s9 + 1 (s9 = atom 25), its value atom 48 *)
Definition decL_txr : YP09.region := YP09.mkRegion (Some 25%nat) 1 2 1 1 [YP09.mkChunk 1 (CVal 1 (SOff 48 0))].
(* the byte q + n the iteration after memchr may store (atom 48, an alias of s1 + s5) *)
Definition decL_str : YP09.region := YP09.mkRegion (Some 48%nat) 0 1 0 1 [].
(* *lenp, the 8 bytes the success tail stores, at atom 33 *)
Definition decL_lpr : YP09.region := YP09.mkRegion (Some 33%nat) 0 8 0 8 [].
Definition decL_Bx : sv := SOff 20 0.
Definition decL_hSH : list shent := [mkSHE 18 0 1].
Definition decL_mSH : list shent := [mkSHE 48 0 1].
Definition decL_lSH : list shent := [mkSHE 33 0 8].
Definition decL_sgf (plo phi blo bhi : Z) : list (nat * afact) :=
  [(8%nat, mkAF DEC_M1 DEC_M1 0); (9%nat, mkAF (4096 + HEAD) DEC_CEIL 4);
   (18%nat, mkAF 4096 DEC_CEIL 0); (19%nat, mkAF G_B64 G_B64 0); (20%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
   (21%nat, mkAF 0 (2 ^ 30) 0); (22%nat, mkAF 0 (2 ^ 64 - 1) 0); (23%nat, mkAF blo bhi 1);
   (24%nat, mkAF plo phi 0); (25%nat, mkAF 4095 (DEC_CEIL - 1) 0); (26%nat, mkAF 61 61 0);
   (27%nat, mkAF DEC_WSMASK DEC_WSMASK 0); (34%nat, mkAF (DEC_M1 - DEC_CEIL) (DEC_M1 - 4112) 0)].
Definition decL_hgf : list (nat * afact) := (48%nat, mkAF 0 255 0) :: decL_sgf 0 (2 ^ 28) 0 6.
Definition decL_hss : sstate := fss_retT DEC_HEAD DEC_F decL_cs [decL_txr] decL_hgf.
Definition decL_mgf : list (nat * afact) := (48%nat, mkAF 4096 (DEC_CEIL - 1) 0) :: decL_sgf 0 (2 ^ 28) 0 6.
Definition decL_mss0 : sstate := fss_retT DEC_RA_MEMCHR DEC_F decL_cs [decL_str] decL_mgf.
Definition decL_mss : sstate :=
  mkSS DEC_RA_MEMCHR sr_atoms (ss_mem decL_mss0) None
    (mkFacts (f_atoms (ss_facts decL_mss0)) [] [(SAlu ALU_ADD (SOff 9 0) (SOff 21 0), SOff 48 0)]).
Definition decL_lgf : list (nat * afact) := (33%nat, mkAF (2 ^ 46) (2 ^ 47 - 8) 3) :: decL_sgf 0 2 0 6.
Definition decL_lss : sstate := fss_retT DEC_EXIT_PAD DEC_F decL_cs [decL_lpr] decL_lgf.

Definition decL_E (d : DE) (q : Z) (regs : bvmap 5 word) (ex : list word) : env :=
  Ereg regs (fs_extraT ++ decL_xs d q ++ ex).
Lemma decL_E_lenp : forall d q regs ex, ew (decL_E d q regs ex) 33 = Z_to_bv 64 (d_lenp d).
Proof. intros d q regs ex. unfold decL_E. change 33%nat with (32 + 1)%nat. rewrite ew_Ereg_extra. reflexivity. Qed.
Lemma decL_E_nq : forall d q regs ex, ew (decL_E d q regs ex) 34 = Z_to_bv 64 (DEC_M1 - q).
Proof. intros d q regs ex. unfold decL_E. change 34%nat with (32 + 2)%nat. rewrite ew_Ereg_extra. reflexivity. Qed.
Lemma decL_E_ex : forall d q regs ex j, ew (decL_E d q regs ex) (48 + j) = nth j ex (Z_to_bv 64 0).
Proof.
intros d q regs ex j. unfold decL_E. replace (48 + j)%nat with (32 + 16 + j)%nat by lia.
rewrite <- Nat.add_assoc. rewrite ew_Ereg_extra. reflexivity.
Qed.
Lemma decL_E_reg : forall d q regs ex (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r ->
  ew (decL_E d q regs ex) n = getr regs r.
Proof. intros d q regs ex n r H. unfold decL_E. apply ew_Ereg_nat. exact H. Qed.
Lemma decLN_E_sav : forall d q regs ex (j : nat), (j < 13)%nat ->
  ew (decL_E d q regs ex) (35 + j) = getr (d_regs d) (nth j dec_saved 0%bv).
Proof.
intros d q regs ex j Hj. unfold decL_E. replace (35 + j)%nat with (32 + (3 + j))%nat by lia.
rewrite ew_Ereg_extra. unfold decL_xs, fs_extraT, dec_saved.
do 13 (destruct j as [|j]; [reflexivity|]). lia.
Qed.
Lemma decL_w64u : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z.
Proof. intros z Hz. unfold w64. apply wz. exact Hz. Qed.

(* ---- the arithmetic of the loop (lib/A/FSW_dec_L2.v, B's atoms) ---- *)
Definition decLA_out (pad : Z) (six rest : list Z) : option (list Z) :=
  match WriterSpec.b64_scan pad six rest with
  | Some (six', pad') => if (pad' <=? 2) && WriterSpec.six_tail_ok six' then Some (WriterSpec.six_bytes six') else None
  | None => None
  end.
Lemma decLA_fin : forall (P : Z -> bool) (lo n : nat), forallb (fun k => P (Z.of_nat k)) (seq lo n) = true ->
  forall c, Z.of_nat lo <= c < Z.of_nat lo + Z.of_nat n -> P c = true.
Proof.
  intros P lo n H c Hc. rewrite forallb_forall in H. specialize (H (Z.to_nat c)).
  rewrite Z2Nat.id in H by lia. apply H. apply in_seq. lia.
Qed.
Lemma decLA_swrap64_small : forall x, 0 <= x < 2 ^ 63 -> bv_swrap 64 x = x.
Proof. intros x Hx. apply bv_swrap_small. change (bv_half_modulus 64) with (2 ^ 63). lia. Qed.
Lemma decLA_sw32_mod256 : forall y, bv_wrap 64 (bv_swrap 32 y) mod 256 = y mod 256.
Proof.
  intros y. unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31).
  change (bv_modulus 32) with (2 ^ 32). change (bv_modulus 64) with (2 ^ 64).
  Z.div_mod_to_equations; lia.
Qed.
Lemma decLA_shr_low : forall x s m, 0 <= s -> s + 8 <= m ->
  Z.shiftr (x mod 2 ^ m) s mod 2 ^ 8 = Z.shiftr x s mod 2 ^ 8.
Proof.
  intros x s m Hs Hm. apply Z.bits_inj'. intros i Hi.
  destruct (Z.lt_ge_cases i 8) as [Hl | Hg].
  - rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
    rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma decLA_lor_add64 : forall x y, 0 <= x < 64 -> 0 <= y -> y mod 64 = 0 -> Z.lor x y = x + y.
Proof.
  intros x y Hx Hy Hm.
  assert (L : Z.land x y = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 6).
    - replace (Z.testbit y i) with false; [apply andb_false_r|].
      symmetry. rewrite <- (Z.mod_pow2_bits_low y 6 i) by lia. change (2 ^ 6) with 64. rewrite Hm. apply Z.bits_0.
    - replace (Z.testbit x i) with false; [reflexivity|].
      symmetry. rewrite <- (Z.mod_small x 64) by lia. change 64 with (2 ^ 6). apply Z.mod_pow2_bits_high. lia. }
  rewrite <- Z.lxor_lor by exact L. symmetry. apply Z.add_nocarry_lxor. exact L.
Qed.
Lemma decLA_last_range : forall six, Forall (fun x => 0 <= x < 64) six -> 0 <= last six 0 < 64.
Proof.
  induction six as [|a t IH]; intros H; [cbn; lia|].
  inversion H as [|? ? Ha Ht]; subst.
  destruct t as [|b t'].
  - cbn. exact Ha.
  - change (last (a :: b :: t') 0) with (last (b :: t') 0). apply IH. exact Ht.
Qed.
Definition decLA_snoc_byte (k l v : Z) : list Z :=
  if k mod 4 =? 1 then [l * 4 + v / 16]
  else if k mod 4 =? 2 then [(l mod 16) * 16 + v / 4]
  else if k mod 4 =? 3 then [(l mod 4) * 64 + v]
  else [].
Lemma decLA_six_bytes_snoc : forall six v,
  WriterSpec.six_bytes (six ++ [v]) =
  WriterSpec.six_bytes six ++ decLA_snoc_byte (Z.of_nat (length six)) (last six 0) v.
Proof.
  intros six v. induction six as [|a|a b|a b c|a b c d l IH] using WriterSpecFacts.list4_ind.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - assert (E : decLA_snoc_byte (Z.of_nat (length (a :: b :: c :: d :: l))) (last (a :: b :: c :: d :: l) 0) v
                = decLA_snoc_byte (Z.of_nat (length l)) (last l 0) v).
    { unfold decLA_snoc_byte.
      replace (Z.of_nat (length (a :: b :: c :: d :: l))) with (Z.of_nat (length l) + 1 * 4) by (cbn [length]; lia).
      rewrite Z.mod_add by lia. destruct l as [|e l]; reflexivity. }
    rewrite E. cbn [app WriterSpec.six_bytes]. rewrite IH. reflexivity.
Qed.
Lemma decLA_snoc_code : forall k l v, 0 <= k -> 0 <= l < 64 -> 0 <= v < 64 -> 2 <= 6 * k mod 8 ->
  decLA_snoc_byte k l v = [Z.shiftr (l * 64 + v) (6 * k mod 8 - 2) mod 256].
Proof.
  intros k l v Hk Hl Hv Hb. unfold decLA_snoc_byte.
  assert (H4 : k mod 4 = 1 \/ k mod 4 = 2 \/ k mod 4 = 3) by (Z.div_mod_to_equations; lia).
  destruct H4 as [H|[H|H]]; rewrite H.
  - replace (6 * k mod 8) with 6 by (Z.div_mod_to_equations; lia). cbn [Z.eqb Pos.eqb].
    change (6 - 2) with 4. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16. f_equal.
    Z.div_mod_to_equations; lia.
  - replace (6 * k mod 8) with 4 by (Z.div_mod_to_equations; lia). cbn [Z.eqb Pos.eqb].
    change (4 - 2) with 2. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 2) with 4. f_equal.
    Z.div_mod_to_equations; lia.
  - replace (6 * k mod 8) with 2 by (Z.div_mod_to_equations; lia). cbn [Z.eqb Pos.eqb].
    change (2 - 2) with 0. rewrite Z.shiftr_0_r. f_equal.
    Z.div_mod_to_equations; lia.
Qed.
Lemma decLA_br_ltu : forall E (na nb : nat) x y, ew E na = Z_to_bv 64 x -> ew E nb = Z_to_bv 64 y ->
  0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_LTU (sv_denot E (SOff na 0)) (sv_denot E (SOff nb 0)) = (x <? y).
Proof.
  intros E na nb x y Ha Hb Hx Hy. rewrite YI04.branch_ltu_U.
  rewrite (YI04.U_atom E na x Ha Hx), (YI04.U_atom E nb y Hb Hy). reflexivity.
Qed.
Lemma decLA_br_ne : forall E (na nb : nat) x y, ew E na = Z_to_bv 64 x -> ew E nb = Z_to_bv 64 y ->
  0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SOff na 0)) (sv_denot E (SOff nb 0)) = negb (x =? y).
Proof.
  intros E na nb x y Ha Hb Hx Hy. rewrite YI04.branch_ne_U.
  rewrite (YI04.U_atom E na x Ha Hx), (YI04.U_atom E nb y Hb Hy). reflexivity.
Qed.
Lemma decLA_br_eq0 : forall E (na : nat) x, ew E na = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff na 0)) (sv_denot E (SLit 0)) = (x =? 0).
Proof.
  intros E na x Ha Hx. rewrite YI04.branch_eq_U.
  rewrite (YI04.U_atom E na x Ha Hx), (YI04.U_lit E 0) by lia. reflexivity.
Qed.
Lemma decLA_br_ne0 : forall E (na : nat) x, ew E na = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SOff na 0)) (sv_denot E (SLit 0)) = negb (x =? 0).
Proof.
  intros E na x Ha Hx. rewrite YI04.branch_ne_U.
  rewrite (YI04.U_atom E na x Ha Hx), (YI04.U_lit E 0) by lia. reflexivity.
Qed.
Lemma decLA_signed_lit : forall E z, 0 <= z < 2 ^ 63 -> bv_signed (sv_denot E (SLit z)) = z.
Proof.
  intros E z Hz. cbn [sv_denot]. rewrite YP0m.signed_lit. rewrite (YP0m.zcanon_small z) by lia.
  apply decLA_swrap64_small. exact Hz.
Qed.
Lemma decLA_signed_atom : forall E (na : nat) x, ew E na = Z_to_bv 64 x -> 0 <= x < 2 ^ 63 ->
  bv_signed (sv_denot E (SOff na 0)) = x.
Proof.
  intros E na x Ha Hx. cbn [sv_denot]. rewrite Ha, YP0m.unsigned_lit, Z.add_0_r, YP0m.signed_lit.
  rewrite (YP0m.zcanon_small x) by lia. rewrite (YP0m.zcanon_small x) by lia.
  apply decLA_swrap64_small. exact Hx.
Qed.
Lemma decLA_br_ge_lit : forall E (na : nat) x z, ew E na = Z_to_bv 64 x -> 0 <= x < 2 ^ 63 -> 0 <= z < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E (SLit z)) (sv_denot E (SOff na 0)) = (x <=? z).
Proof.
  intros E na x z Ha Hx Hz. cbn [branch_taken]. unfold bv_lts.
  rewrite (decLA_signed_lit E z Hz), (decLA_signed_atom E na x Ha Hx).
  rewrite Z.leb_antisym. reflexivity.
Qed.
Lemma decLA_br_lt_lit : forall E (na : nat) x z, ew E na = Z_to_bv 64 x -> 0 <= x < 2 ^ 63 -> 0 <= z < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E (SLit z)) (sv_denot E (SOff na 0)) = (z <? x).
Proof.
  intros E na x z Ha Hx Hz. cbn [branch_taken]. unfold bv_lts.
  rewrite (decLA_signed_lit E z Hz), (decLA_signed_atom E na x Ha Hx). reflexivity.
Qed.
(* `beqz ((mask >> c) & 1)` with mask = 0x100002600 is taken iff c is no whitespace, for c <= 61 *)
Lemma decLA_br_ws_eq : forall E (nm nc : nat) c, ew E nm = Z_to_bv 64 DEC_WSMASK -> ew E nc = Z_to_bv 64 c -> 0 <= c <= 61 ->
  branch_taken BC_EQ (sv_denot E (SAlu ALU_AND (SAlu ALU_SRL (SOff nm 0) (SOff nc 0)) (SLit 1))) (sv_denot E (SLit 0))
  = negb (WriterSpec.b64_ws c).
Proof.
  intros E nm nc c Hm Hc Hr. rewrite YI04.branch_eq_U.
  rewrite (YI04.U_and_lit E _ 1) by lia. rewrite (YI04.U_lit E 0) by lia.
  rewrite YP0e.U_SAlu. cbn [zalu_raw].
  rewrite (YI04.U_atom E nm DEC_WSMASK Hm) by (unfold DEC_WSMASK; lia).
  rewrite (YI04.U_atom E nc c Hc) by lia.
  apply Bool.eqb_prop.
  apply (decLA_fin (fun n => Bool.eqb (Z.land (zcanon (Z.shiftr DEC_WSMASK (Z.land n 63))) 1 =? 0)
                               (negb (WriterSpec.b64_ws n))) 0 62); [vm_compute; reflexivity | lia].
Qed.
Lemma decLA_br_exit_and : forall E (na nb : nat) acc b, ew E na = Z_to_bv 64 acc -> 0 <= acc < 2 ^ 64 ->
  ew E nb = Z_to_bv 64 b -> 0 <= b <= 5 ->
  branch_taken BC_NE
    (sv_denot E (SAlu ALU_AND (SOff na 0)
       (SAlu ALU_XOR (SAluw ALU_SLL (SLit 18446744073709551615) (SOff nb 0)) (SLit (-1)))))
    (sv_denot E (SLit 0))
  = negb (acc mod 2 ^ b =? 0).
Proof.
  intros E na nb acc b Ha Hacc Hb Hbr. rewrite YI04.branch_ne_U. rewrite (YI04.U_lit E 0) by lia.
  assert (M : U E (SAlu ALU_XOR (SAluw ALU_SLL (SLit 18446744073709551615) (SOff nb 0)) (SLit (-1))) = 2 ^ b - 1).
  { rewrite YP0e.U_SAlu. cbn [zalu_raw]. rewrite YP0e.U_SLit.
    rewrite (YP0e.U_of_S E (SAluw _ _ _)), YP0e.S_SAluw. cbn [zalu_raw]. rewrite YP0e.U_SLit.
    rewrite (YI04.U_atom E nb b Hb) by lia.
    assert (Bc : b = 0 \/ b = 1 \/ b = 2 \/ b = 3 \/ b = 4 \/ b = 5) by lia.
    destruct Bc as [-> | [-> | [-> | [-> | [-> | ->]]]]]; vm_compute; reflexivity. }
  rewrite YP0e.U_SAlu. cbn [zalu_raw]. rewrite M, (YI04.U_atom E na acc Ha Hacc).
  assert (O : 2 ^ b - 1 = Z.ones b) by (rewrite Z.ones_equiv; lia).
  rewrite O, Z.land_ones by lia.
  assert (P : 0 < 2 ^ b) by (apply Z.pow_pos_nonneg; lia).
  assert (P5 : 2 ^ b <= 2 ^ 5) by (apply Z.pow_le_mono_r; lia). change (2 ^ 5) with 32 in P5.
  pose proof (Z.mod_pos_bound acc (2 ^ b) P).
  rewrite (YP0m.zcanon_small (acc mod 2 ^ b)) by lia. reflexivity.
Qed.
(* the accumulator after memchr returned r = g_b64 + v: (r - s3)_w | (s6 <<w 6), s6 = atom 22 *)
Definition decLO_acc_e : sv :=
  SAlu ALU_OR (SAluw ALU_SUB (SOff 10 0) (SOff 19 0)) (SAluw ALU_SLL (SOff 22 0) (SLit 6)).
Lemma decLO_acc : forall E acc v, ew E 10 = Z_to_bv 64 (G_B64 + v) -> 0 <= v < 64 -> ew E 19 = Z_to_bv 64 G_B64 ->
  ew E 22 = Z_to_bv 64 acc -> 0 <= acc < 2 ^ 64 ->
  U E decLO_acc_e mod 4096 = (acc mod 64) * 64 + v.
Proof.
  intros E acc v H10 Hv H19 H22 Hacc. unfold decLO_acc_e.
  assert (UA : U E (SAluw ALU_SUB (SOff 10 0) (SOff 19 0)) = v).
  { rewrite (YP0e.U_of_S E (SAluw _ _ _)), YP0e.S_SAluw. cbn [zalu_raw].
    rewrite (YI04.U_atom E 10 (G_B64 + v) H10) by (unfold G_B64; lia).
    rewrite (YI04.U_atom E 19 G_B64 H19) by (unfold G_B64; lia).
    rewrite (Z.mod_small (G_B64 + v) (2 ^ 32)) by (unfold G_B64; lia).
    rewrite (Z.mod_small G_B64 (2 ^ 32)) by (unfold G_B64; lia).
    replace (G_B64 + v - G_B64) with v by ring.
    unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31).
    change (bv_modulus 32) with (2 ^ 32). change (bv_modulus 64) with (2 ^ 64).
    rewrite (Z.mod_small (v + 2 ^ 31) (2 ^ 32)) by lia.
    replace (v + 2 ^ 31 - 2 ^ 31) with v by ring. apply Z.mod_small. lia. }
  assert (HS : 0 <= U E (SAluw ALU_SLL (SOff 22 0) (SLit 6)) < 2 ^ 64 /\
    U E (SAluw ALU_SLL (SOff 22 0) (SLit 6)) mod 64 = 0 /\
    U E (SAluw ALU_SLL (SOff 22 0) (SLit 6)) mod 4096 = (acc mod 64) * 64).
  { rewrite (YP0e.U_of_S E (SAluw _ _ _)), YP0e.S_SAluw. cbn [zalu_raw].
    rewrite (YI04.U_atom E 22 acc H22 Hacc), YP0e.U_SLit.
    change (Z.land (zcanon 6 mod 2 ^ 32) 31) with 6. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 6) with 64.
    unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31).
    change (bv_modulus 32) with (2 ^ 32). change (bv_modulus 64) with (2 ^ 64).
    split; [|split]; Z.div_mod_to_equations; lia. }
  destruct HS as (HS1 & HS2 & HS3).
  rewrite YP0e.U_SAlu. cbn [zalu_raw]. rewrite UA.
  remember (U E (SAluw ALU_SLL (SOff 22 0) (SLit 6))) as US eqn:HUS.
  rewrite decLA_lor_add64 by lia.
  assert (HS4 : US <= 2 ^ 64 - 64) by (Z.div_mod_to_equations; lia).
  rewrite (YP0m.zcanon_small (v + US)) by lia.
  Z.div_mod_to_equations; lia.
Qed.
(* the stored byte: srlw (acc', bits - 2), bits = atom 23 *)
Lemma decLA_byte : forall E e b, ew E 23 = Z_to_bv 64 b -> 2 <= b <= 6 ->
  U E (SAluw ALU_SRL e (SOff 23 (-2))) mod 256 = Z.shiftr (U E e mod 4096) (b - 2) mod 256.
Proof.
  intros E e b H23 Hb. rewrite (YP0e.U_of_S E (SAluw _ _ _)), YP0e.S_SAluw. cbn [zalu_raw].
  rewrite (YI04.U_atom_off E 23 b (-2) H23) by lia.
  rewrite (Z.mod_small (b + -2) (2 ^ 32)) by lia.
  replace (Z.land (b + -2) 31) with (b - 2).
  2:{ change 31 with (Z.ones 5). rewrite Z.land_ones by lia. rewrite Z.mod_small by lia. lia. }
  rewrite decLA_sw32_mod256. change 256 with (2 ^ 8).
  rewrite (decLA_shr_low (U E e) (b - 2) 32) by lia.
  change 4096 with (2 ^ 12). rewrite (decLA_shr_low (U E e) (b - 2) 12) by lia. reflexivity.
Qed.
Lemma decLA_skipn : forall (tb : list Z) (i : nat), (i < length tb)%nat -> skipn i tb = nth i tb 0 :: skipn (S i) tb.
Proof.
  induction tb as [|x tb IH]; intros i Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i]; [reflexivity|].
  cbn [skipn nth]. apply IH. lia.
Qed.
Lemma decLA_skipn_end : forall (tb : list Z), skipn (length tb) tb = [].
Proof. induction tb as [|x tb IH]; [reflexivity|]. cbn [length skipn]. exact IH. Qed.
Lemma decLA_out_nil : forall pad six,
  decLA_out pad six [] = if (pad <=? 2) && WriterSpec.six_tail_ok six then Some (WriterSpec.six_bytes six) else None.
Proof. intros pad six. reflexivity. Qed.
Lemma decLA_out_ws : forall c pad six rest, WriterSpec.b64_ws c = true -> decLA_out pad six (c :: rest) = decLA_out pad six rest.
Proof. intros c pad six rest H. unfold decLA_out. cbn [WriterSpec.b64_scan]. rewrite H. reflexivity. Qed.
Lemma decLA_out_61 : forall pad six rest, decLA_out pad six (61 :: rest) = decLA_out (pad + 1) six rest.
Proof. intros pad six rest. reflexivity. Qed.
Lemma decLA_out_bad : forall c pad six rest, WriterSpec.b64_ws c = false -> c <> 61 -> WriterSpec.b64v c = None ->
  decLA_out pad six (c :: rest) = None.
Proof.
  intros c pad six rest H1 H2 H3. unfold decLA_out. cbn [WriterSpec.b64_scan].
  rewrite H1, (proj2 (Z.eqb_neq c 61) H2), H3. reflexivity.
Qed.
Lemma decLA_out_padbad : forall c v pad six rest, WriterSpec.b64_ws c = false -> c <> 61 -> WriterSpec.b64v c = Some v ->
  pad <> 0 -> decLA_out pad six (c :: rest) = None.
Proof.
  intros c v pad six rest H1 H2 H3 H4. unfold decLA_out. cbn [WriterSpec.b64_scan].
  rewrite H1, (proj2 (Z.eqb_neq c 61) H2), H3, (proj2 (Z.eqb_neq pad 0) H4). reflexivity.
Qed.
Lemma decLA_out_val : forall c v six rest, WriterSpec.b64_ws c = false -> c <> 61 -> WriterSpec.b64v c = Some v ->
  decLA_out 0 six (c :: rest) = decLA_out 0 (six ++ [v]) rest.
Proof.
  intros c v six rest H1 H2 H3. unfold decLA_out. cbn [WriterSpec.b64_scan].
  rewrite H1, (proj2 (Z.eqb_neq c 61) H2), H3. reflexivity.
Qed.
Lemma decLA_ws_vals : forall c, WriterSpec.b64_ws c = true -> c = 9 \/ c = 10 \/ c = 13 \/ c = 32.
Proof.
  intros c H. unfold WriterSpec.b64_ws in H.
  destruct (Z.eqb_spec c 32), (Z.eqb_spec c 9), (Z.eqb_spec c 10), (Z.eqb_spec c 13); cbn in H;
    try discriminate; lia.
Qed.
Lemma decLA_b64v_range : forall c v, WriterSpec.b64v c = Some v -> 0 <= v < 64.
Proof. exact WriterSpecFacts.b64v_range. Qed.
Definition decLA_zchk (c : Z) : bool :=
  match zfind c WriterSpec.b64_table with
  | None => match WriterSpec.b64v c with None => true | Some _ => false end
  | Some j => match WriterSpec.b64v c with Some v => v =? Z.of_nat j | None => false end
  end.
Lemma decLA_zfind : forall c, 1 <= c <= 255 ->
  match zfind c WriterSpec.b64_table with
  | None => WriterSpec.b64v c = None
  | Some j => WriterSpec.b64v c = Some (Z.of_nat j)
  end.
Proof.
  intros c Hc.
  assert (A : decLA_zchk c = true) by (apply (decLA_fin decLA_zchk 1 255); [vm_compute; reflexivity | lia]).
  unfold decLA_zchk in A.
  destruct (zfind c WriterSpec.b64_table) as [j|]; destruct (WriterSpec.b64v c) as [v|]; try discriminate.
  - apply Z.eqb_eq in A. subst v. reflexivity.
  - reflexivity.
Qed.
Lemma decLA_tail : forall six W, W mod 64 = last six 0 ->
  WriterSpec.six_tail_ok six =
  (6 * Z.of_nat (length six) mod 8 <=? 5) && (W mod 2 ^ (6 * Z.of_nat (length six) mod 8) =? 0).
Proof.
  intros six W HW. unfold WriterSpec.six_tail_ok. cbv zeta. rewrite <- HW.
  replace ((W mod 64) mod 16) with (W mod 16) by (Z.div_mod_to_equations; lia).
  replace ((W mod 64) mod 4) with (W mod 4) by (Z.div_mod_to_equations; lia).
  remember (Z.of_nat (length six)) as k eqn:Hk.
  assert (H4 : k mod 4 = 0 \/ k mod 4 = 1 \/ k mod 4 = 2 \/ k mod 4 = 3) by (Z.div_mod_to_equations; lia).
  destruct H4 as [H|[H|[H|H]]]; rewrite H.
  - replace (6 * k mod 8) with 0 by (Z.div_mod_to_equations; lia). change (2 ^ 0) with 1. rewrite Z.mod_1_r.
    destruct (W mod 16 =? 0), (W mod 4 =? 0); reflexivity.
  - replace (6 * k mod 8) with 6 by (Z.div_mod_to_equations; lia).
    destruct (W mod 16 =? 0), (W mod 4 =? 0); reflexivity.
  - replace (6 * k mod 8) with 4 by (Z.div_mod_to_equations; lia). change (2 ^ 4) with 16.
    destruct (W mod 16 =? 0), (W mod 4 =? 0); reflexivity.
  - replace (6 * k mod 8) with 2 by (Z.div_mod_to_equations; lia). change (2 ^ 2) with 4.
    destruct (W mod 16 =? 0), (W mod 4 =? 0); reflexivity.
Qed.
Lemma decLA_snoc0 : forall six v, 6 * Z.of_nat (length six) mod 8 = 0 ->
  WriterSpec.six_bytes (six ++ [v]) = WriterSpec.six_bytes six.
Proof.
  intros six v H. rewrite decLA_six_bytes_snoc. unfold decLA_snoc_byte.
  replace (Z.of_nat (length six) mod 4) with 0 by (Z.div_mod_to_equations; lia).
  cbn [Z.eqb]. apply app_nil_r.
Qed.
Lemma decLA_snoc : forall six v, Forall (fun x => 0 <= x < 64) six -> 0 <= v < 64 -> 2 <= 6 * Z.of_nat (length six) mod 8 ->
  WriterSpec.six_bytes (six ++ [v]) =
  WriterSpec.six_bytes six ++ [Z.shiftr (last six 0 * 64 + v) (6 * Z.of_nat (length six) mod 8 - 2) mod 256].
Proof.
  intros six v Hs Hv Hb. rewrite decLA_six_bytes_snoc.
  rewrite decLA_snoc_code; [reflexivity | lia | exact (decLA_last_range six Hs) | exact Hv | exact Hb].
Qed.
Lemma decLA_bits : forall k, 0 <= k ->
  6 * (k + 1) mod 8 = (if 6 * k mod 8 =? 0 then 6 else 6 * k mod 8 - 2).
Proof.
  intros k Hk.
  assert (H4 : k mod 4 = 0 \/ k mod 4 = 1 \/ k mod 4 = 2 \/ k mod 4 = 3) by (Z.div_mod_to_equations; lia).
  destruct H4 as [H|[H|[H|H]]].
  - replace (6 * k mod 8) with 0 by (Z.div_mod_to_equations; lia). cbn [Z.eqb].
    Z.div_mod_to_equations; lia.
  - replace (6 * k mod 8) with 6 by (Z.div_mod_to_equations; lia). cbn [Z.eqb Pos.eqb].
    Z.div_mod_to_equations; lia.
  - replace (6 * k mod 8) with 4 by (Z.div_mod_to_equations; lia). cbn [Z.eqb Pos.eqb].
    Z.div_mod_to_equations; lia.
  - replace (6 * k mod 8) with 2 by (Z.div_mod_to_equations; lia). cbn [Z.eqb Pos.eqb].
    Z.div_mod_to_equations; lia.
Qed.
Lemma decLA_bits_cases : forall k, 0 <= k ->
  6 * k mod 8 = 0 \/ 6 * k mod 8 = 2 \/ 6 * k mod 8 = 4 \/ 6 * k mod 8 = 6.
Proof.
  intros k Hk.
  assert (H4 : k mod 4 = 0 \/ k mod 4 = 1 \/ k mod 4 = 2 \/ k mod 4 = 3) by (Z.div_mod_to_equations; lia).
  destruct H4 as [H|[H|[H|H]]]; Z.div_mod_to_equations; lia.
Qed.
Lemma decLA_nbytes : forall six (tb : list Z), (length six <= length tb)%nat ->
  Z.of_nat (length (WriterSpec.six_bytes six)) < dec_size tb.
Proof.
  intros six tb H. rewrite WriterSpecFacts.six_bytes_length. unfold dec_size.
  assert (L : Z.of_nat (length six) <= Z.of_nat (length tb)) by lia.
  assert (L0 : 0 <= Z.of_nat (length six)) by lia.
  Z.div_mod_to_equations; lia.
Qed.

(* ---- image facts (lib/A/FSW_dec_L3.v head; B's PT_LOADs cover the same page-rounded ranges) ---- *)
Lemma decLB_in_img : forall a, 0x10000 <= a < 0x5fd000 -> in_img tfibsegs a.
Proof.
intros a Ha.
assert (HC : forall lo hi,
  existsb (fun s => (Z.of_N (seg_base s) <=? lo) && (hi <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) tfibsegs = true ->
  lo <= a < hi -> in_img tfibsegs a).
{ intros lo hi Hb Hr. apply existsb_exists in Hb as (sg & Hin & Hc). apply andb_prop in Hc as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. exists sg. split; [exact Hin | lia]. }
destruct (Z.lt_ge_cases a 0x30000); [apply (HC 0x10000 0x30000); [vm_compute; reflexivity | lia]|].
destruct (Z.lt_ge_cases a 0x9f000); [apply (HC 0x30000 0x9f000); [vm_compute; reflexivity | lia]|].
destruct (Z.lt_ge_cases a 0xa1000); [apply (HC 0x9f000 0xa1000); [vm_compute; reflexivity | lia]|].
apply (HC 0xa1000 0x5fd000); [vm_compute; reflexivity | lia].
Qed.
Lemma decLB_cell_apart : forall c a, 0x10000 <= c -> c + 8 <= 0x5fd000 -> ~ in_img tfibsegs a ->
  a + 1 <= c \/ c + 8 <= a.
Proof.
intros c a H1 H2 Hn. destruct (Z.lt_ge_cases a c); [left; lia|].
destruct (Z.lt_ge_cases a (c + 8)); [|right; lia]. exfalso. apply Hn. apply decLB_in_img. lia.
Qed.
Lemma decLB_ro_img : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> in_img tfibsegs a.
Proof.
intros a [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr]|].
apply decLB_in_img. unfold FS_RLO, FS_RHI in Hr. lia.
Qed.
Lemma decLB_ro_strs : forall s l, In (s, l) FS_RO_STRS -> 0x20000 <= s /\ s + Z.of_nat (length l) + 8 <= 0x22000.
Proof.
intros s l H.
assert (Hb : forallb (fun r => (0x20000 <=? fst r) && (fst r + Z.of_nat (length (snd r)) + 8 <=? 0x22000)) FS_RO_STRS
  = true) by (vm_compute; reflexivity).
pose proof (proj1 (forallb_forall _ _) Hb (s, l) H) as X. cbn [fst snd] in X.
apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2. lia.
Qed.
Lemma decLB_val_mem : forall (H : word -> bool) (m1 m2 : word -> option byte) a (n : nat) v,
  (forall k, (k < n)%nat -> aview tfibsegs H m2 (a + Z.of_nat k) = aview tfibsegs H m1 (a + Z.of_nat k)) ->
  val_mem tfibsegs (mrestrict H m1) a n v -> val_mem tfibsegs (mrestrict H m2) a n v.
Proof.
intros H m1 m2 a n v HA Hv k Hk. rewrite (mbyte_of_aview tfibsegs H H m1 m2 _ (HA k Hk)). exact (Hv k Hk).
Qed.
Lemma decLB_wr_eq : forall (H : word -> bool) (m1 m2 : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ in_img tfibsegs a -> aview tfibsegs H m2 a = aview tfibsegs H m1 a ->
  (writable_at tfibsegs (mrestrict H m1) a <-> writable_at tfibsegs (mrestrict H m2) a).
Proof.
intros H m1 m2 a Ha Hn X.
assert (EQ : mrestrict H m2 (Z_to_bv 64 a) = mrestrict H m1 (Z_to_bv 64 a)).
{ unfold aview, mbyte in X. rewrite (seg_rom_none tfibsegs a Ha Hn) in X.
  destruct (mrestrict H m2 (Z_to_bv 64 a)) as [b2|], (mrestrict H m1 (Z_to_bv 64 a)) as [b1|]; cbn in X;
    try discriminate X; [|reflexivity].
  injection X as X. f_equal. apply bv_eq. exact X. }
unfold writable_at, wview. rewrite EQ. reflexivity.
Qed.

Lemma decL_dn_pos : forall d, 0 <= d_n d.
Proof.
intros d. unfold d_n, dec_size.
pose proof (Z.div_pos (Z.of_nat (length (d_tb d))) 4 ltac:(lia) ltac:(lia)). lia.
Qed.

Section LOOP. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis HSS : FsShadowSyms B.
Hypothesis HIMG : fs_img_facts tfibsegs B.
Hypothesis HMEMCHR : amemchr_realizesU tfibsegs B PC_memchr.

(* ---- L0: the memory facts of a cut, the cut's own journal, the frame chunks, the builder ---- *)
Definition decL_memf (d : DE) (q : Z) (six : list Z) (Wc : world tfibsegs) (lyc : alayout) (Sc : astate)
    (memc : word -> option byte) : Prop :=
  fs_rblock tfibsegs B lyc Sc Wc memc q (d_n d) /\
  range_addressable (aview tfibsegs (w_H Wc) memc) SHADOW_OFF q (d_n d) /\
  fs_glob tfibsegs Wc memc (d_live d + d_n d) (Z.max (d_peak d) (d_live d + d_n d)) (d_cnt d + 1) (d_fail d) /\
  dec_kept B d Wc memc /\ zbytes_at tfibsegs Wc memc q (WriterSpec.six_bytes six).

Lemma decL_self_journal : forall d lyc Sc Wc Uc memc mdc k,
  dec_entry_ok B d -> dec_J B d lyc Sc Wc Uc memc mdc k -> ARU tfibsegs B lyc Sc Uc Wc memc mdc ->
  ajournal tfibsegs B DEC_F (d_sp d) [] lyc Sc Wc (unpoison Uc memc) mdc [] lyc Sc Wc (unpoison Uc memc) mdc 0.
Proof.
intros d lyc Sc Wc Uc memc mdc k HE HJ HARU.
assert (HSTK : 128 + STK_RT_STR <= STK_preset_base64_decode) by (vm_compute; discriminate).
assert (HSTR : 0 <= STK_RT_STR) by (vm_compute; discriminate).
destruct HE as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPL).
pose proof (fsw_sp B _ _ _ _ _ _ _ _ _ (proj1 HPRE)) as (Hsp16 & _ & _ & _).
assert (Hspot : d_sp d <= d_ot d) by (unfold d_sp; destruct HPL as (_ & H1 & H2 & _); lia).
unfold dec_J, d_STKJ in HJ.
destruct HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hk & Hhi & Hblk & Himg & Hfr & Hrem & Hpres & Hstk & Hext
  & HQT).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
split; [exact HAR|]. split; [apply layout_le_refl|]. split; [lia|]. split; [apply wle_refl|].
split; [apply aos_step_refl|]. split; [reflexivity|]. split; [lia|]. split; [lia|].
split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
split; [intros; reflexivity|]. split; [intros p n i H1 H2; exfalso; exact (H2 H1)|].
split.
{ intros a Ha. apply Hpres. unfold DEC_F in Ha. lia. }
split.
{ unfold astk_ok, ly_bot, DEC_F in *. rewrite Etop, Eslo, Eshi.
  split; [exact Hsp16|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [lia|]. split; lia. }
split; [intros; reflexivity | exact HQT].
Qed.

Ltac decL_cs1 HF j :=
  let r := eval vm_compute in (nth j dec_saved 0%bv) in
  lazymatch goal with |- YP09.chunk_ok _ (decL_E ?d _ _ _) _ _ _ =>
  apply (chunk_ok_val tfibsegs _ _ _ _ 8 _ (bv_unsigned (getr (d_regs d) r))) end;
  [ rewrite fsw_SOff0;
    lazymatch goal with |- ew _ ?n = _ =>
      let m := eval vm_compute in (n - 32)%nat in
      replace n with (32 + m)%nat by reflexivity end;
    unfold decL_E; rewrite ew_Ereg_extra; cbn; rewrite Z_to_bv_bv_unsigned; reflexivity
  | cbn [Z.of_N]; apply u64_range | cbn [Z.of_N]; lia
  | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add];
    lazymatch goal with |- val_mem _ _ (?b + ?o) _ _ =>
      replace (b + o) with (b + 24 + 8 * Z.of_nat j) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) end;
    exact (HF j%nat r eq_refl) ].
Lemma decL_cs_ok : forall d q regs ex (W : world tfibsegs) mem,
  dec_frame_ok W mem (d_sp d - DEC_F) (d_regs d) -> dec_lenp_slot W mem (d_sp d - DEC_F) (d_lenp d) ->
  dec_nq_slot W mem (d_sp d - DEC_F) q ->
  0 <= d_lenp d < 2 ^ 64 -> 0 <= q < 2 ^ 64 ->
  Forall (YP09.chunk_ok tfibsegs (decL_E d q regs ex) (mrestrict (w_H W) mem) (d_sp d - DEC_F)) decL_cs.
Proof.
intros d q regs ex W mem HF HL HN Hl Hq.
unfold decL_cs.
constructor.
{ apply (chunk_ok_val tfibsegs _ _ _ 8 8 (SOff 33 0) (d_lenp d));
    [rewrite fsw_SOff0, decL_E_lenp; reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia | exact HL]. }
constructor.
{ apply (chunk_ok_val tfibsegs _ _ _ 16 8 (SOff 34 0) (DEC_M1 - q));
    [rewrite fsw_SOff0, decL_E_nq; reflexivity | cbn [Z.of_N]; unfold DEC_M1; lia | cbn [Z.of_N]; lia | exact HN]. }
constructor; [decL_cs1 HF 0%nat|]. constructor; [decL_cs1 HF 1%nat|]. constructor; [decL_cs1 HF 2%nat|].
constructor; [decL_cs1 HF 3%nat|]. constructor; [decL_cs1 HF 4%nat|]. constructor; [decL_cs1 HF 5%nat|].
constructor; [decL_cs1 HF 6%nat|]. constructor; [decL_cs1 HF 7%nat|]. constructor; [decL_cs1 HF 8%nat|].
constructor; [decL_cs1 HF 9%nat|]. constructor; [decL_cs1 HF 10%nat|]. constructor; [decL_cs1 HF 11%nat|].
constructor; [decL_cs1 HF 12%nat|]. constructor.
Qed.

Lemma decL_lenp_range : forall d, dec_entry_ok B d ->
  4096 <= d_lenp d /\ d_lenp d + 8 <= 2 ^ 47 /\
  d_FP d = FS_PSTAT_FP /\ d_sp d <= d_lenp d /\ d_lenp d + 8 <= d_ot d.
Proof.
intros d HE.
pose proof asan_consts as (C1 & _ & _ & _).
destruct HE as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPL).
pose proof (fsw_sp B _ _ _ _ _ _ _ _ _ (proj1 HPRE)) as (_ & Hsp1 & Hsp2 & _).
pose proof (proj1 HPRE) as ((_ & _ & _ & _ & _ & Hstk & _) & _).
pose proof Hstk as (_ & _ & _ & _ & _ & H47 & _ & _ & Htop).
destruct HPL as (HFP & H1 & H2 & H3 & H4 & _).
assert (HSTK : 128 <= STK_preset_base64_decode) by (vm_compute; discriminate).
unfold d_sp. split; [lia|]. split; [lia|]. split; [exact HFP | lia].
Qed.

Lemma decL_build : forall d q Wc lyc Sc Uc regsc memc mdc k ex pc rs gf,
  dec_entry_ok B d -> dec_J B d lyc Sc Wc Uc memc mdc k -> ARU tfibsegs B lyc Sc Uc Wc memc mdc ->
  spZ regsc = d_sp d - DEC_F ->
  dec_frame_ok Wc memc (d_sp d - DEC_F) (d_regs d) -> dec_lenp_slot Wc memc (d_sp d - DEC_F) (d_lenp d) ->
  dec_nq_slot Wc memc (d_sp d - DEC_F) q -> 0 <= q < 2 ^ 64 ->
  regions_wf (fsT_ret_regions DEC_F decL_cs rs) = true ->
  Forall (region_ok tfibsegs (decL_E d q regsc ex) (mrestrict (w_H Wc) memc)) rs ->
  pairwise_disjoint (decL_E d q regsc ex) (fsT_ret_regions DEC_F decL_cs rs) ->
  atoms_ok (decL_E d q regsc ex) gf ->
  st_ok tfibsegs (decL_E d q regsc ex) (fss_retT pc DEC_F decL_cs rs gf)
    (restrict (w_H Wc) (YK11.mkst regsc (Z_to_bv 64 pc) memc (YK11.seg_rom tfibsegs))).
Proof.
intros d q Wc lyc Sc Uc regsc memc mdc k ex pc rs gf HE HJ HARU Hsp HF HL HN Hq Hwf Hrs Hpd Hgf.
pose proof (decL_lenp_range d HE) as (L1 & L2 & _).
unfold decL_E in *.
apply (fsw_resume_after_rtU_args_chunks B DEC_F (d_sp d) [] lyc Sc Wc (unpoison Uc memc) mdc [] lyc Sc Uc Wc memc mdc 0
  regsc DEC_F (decL_xs d q ++ ex) decL_cs rs gf pc (proj1 HSS) (proj2 HSS)).
- exact (decL_self_journal d lyc Sc Wc Uc memc mdc k HE HJ HARU).
- exact HARU.
- exact Hsp.
- unfold DEC_F; lia.
- lia.
- reflexivity.
- exact Hwf.
- exact (decL_cs_ok d q regsc ex Wc memc HF HL HN ltac:(lia) Hq).
- exact Hrs.
- exact Hpd.
- exact Hgf.
Qed.

Lemma decL_frame_back : forall d q regs0 ex (W : world tfibsegs) ms Ex ss,
  st_ok tfibsegs Ex ss (restrict (w_H W) ms) ->
  nth_error (ss_mem ss) 0 = Some (fstk_ret DEC_F decL_cs) ->
  bv_unsigned (ew Ex 2) = d_sp d - DEC_F ->
  (forall n, (33 <= n < 48)%nat -> ew Ex n = ew (decL_E d q regs0 ex) n) ->
  0 <= d_lenp d < 2 ^ 64 -> 0 <= q < 2 ^ 64 ->
  dec_frame_ok W (ms_mem ms) (d_sp d - DEC_F) (d_regs d) /\ dec_lenp_slot W (ms_mem ms) (d_sp d - DEC_F) (d_lenp d) /\
  dec_nq_slot W (ms_mem ms) (d_sp d - DEC_F) q.
Proof.
intros d q regs0 ex W ms Ex ss HS Hnth E2 HEx Hl Hq.
pose proof (fsw_region_nth Ex ss (restrict (w_H W) ms) 0 _ HS Hnth) as HR.
cbn [ms_mem restrict] in HR. unfold fstk_ret in HR.
split; [|split].
- intros j r Hj.
  unfold dec_saved in Hj.
  do 13 (destruct j as [|j]; [cbn [nth_error] in Hj; inversion Hj; subst r; clear Hj;
    lazymatch goal with |- val_mem _ _ (?b + 24 + 8 * Z.of_nat ?jj) _ _ =>
      let off := eval vm_compute in (24 + 8 * Z.of_nat jj) in
      let n := eval vm_compute in (35 + jj)%nat in
      replace (b + 24 + 8 * Z.of_nat jj) with (b + off) by (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia);
      apply (fsw_field Ex _ 2 b decL_cs 0 DEC_F 0 DEC_F off 8 (SOff n 0) _ HR E2);
      [ cbv [decL_cs In]; tauto
      | rewrite fsw_SOff0, (HEx n ltac:(lia)); unfold decL_E;
        replace n with (32 + (n - 32))%nat by reflexivity; rewrite ew_Ereg_extra; cbn;
        rewrite Z_to_bv_bv_unsigned; reflexivity
      | apply u64_range | cbn; lia ]
    end|]).
  destruct j; cbn [nth_error] in Hj; discriminate Hj.
- unfold dec_lenp_slot.
  apply (fsw_field Ex _ 2 (d_sp d - DEC_F) decL_cs 0 DEC_F 0 DEC_F 8 8 (SOff 33 0) _ HR E2);
    [ cbv [decL_cs In]; tauto
    | rewrite fsw_SOff0, (HEx 33%nat ltac:(lia)), decL_E_lenp; reflexivity
    | exact Hl | cbn; lia ].
- unfold dec_nq_slot.
  apply (fsw_field Ex _ 2 (d_sp d - DEC_F) decL_cs 0 DEC_F 0 DEC_F 16 8 (SOff 34 0) _ HR E2);
    [ cbv [decL_cs In]; tauto
    | rewrite fsw_SOff0, (HEx 34%nat ltac:(lia)), decL_E_nq; reflexivity
    | unfold DEC_M1; lia | cbn; lia ].
Qed.

Lemma decL_mk_head : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k i' six' pad' acc' regs' mem' md',
  dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  dec_J B d lyc Sc Wc Uc mem' md' k -> ARU tfibsegs B lyc Sc Uc Wc mem' md' ->
  decL_memf d q six' Wc lyc Sc mem' ->
  dec_frame_ok Wc mem' (d_sp d - DEC_F) (d_regs d) -> dec_lenp_slot Wc mem' (d_sp d - DEC_F) (d_lenp d) ->
  dec_nq_slot Wc mem' (d_sp d - DEC_F) q ->
  spZ regs' = d_sp d - DEC_F -> getr regs' 3 = getr (d_regs d) 3 -> getr regs' 4 = getr (d_regs d) 4 ->
  getr regs' 8 = w64 DEC_M1 -> getr regs' 9 = w64 q ->
  getr regs' 18 = w64 (d_text d + Z.of_nat i') -> getr regs' 19 = w64 G_B64 -> getr regs' 20 = w64 SHADOW_OFF ->
  getr regs' 21 = w64 (Z.of_nat (length (WriterSpec.six_bytes six'))) -> getr regs' 22 = w64 acc' -> 0 <= acc' < 2 ^ 64 ->
  getr regs' 23 = w64 (6 * Z.of_nat (length six') mod 8) -> getr regs' 24 = w64 pad' ->
  getr regs' 25 = w64 (d_text d + Z.of_nat i' - 1) -> getr regs' 26 = w64 61 -> getr regs' 27 = w64 DEC_WSMASK ->
  (i' <= length (d_tb d))%nat -> 0 <= pad' <= Z.of_nat i' -> (length six' <= i')%nat ->
  Forall (fun x => 0 <= x < 64) six' -> acc' mod 64 = last six' 0 ->
  WriterSpec.b64_dec (d_tb d) =
    match WriterSpec.b64_scan pad' six' (skipn i' (d_tb d)) with
    | Some (six'', pad'') => if (pad'' <=? 2) && WriterSpec.six_tail_ok six'' then Some (WriterSpec.six_bytes six'') else None
    | None => None
    end ->
  dec_head B d q i' six' pad' acc' Wc lyc Sc Uc regs' mem' md' k.
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k i' six' pad' acc' regs' mem' md'
  HH HJ HARU (Hrb & Hra & Hglob & HKe & HZb) HFr HLs HNq Hsp R3 R4 R8 R9 R18 R19 R20 R21 R22 Hacc R23 R24 R25 R26 R27
  Hi Hpad Hsix Hsix64 Hlast Hscan.
unfold dec_head in HH |- *. cbv zeta in HH |- *.
destruct HH as (_ & _ & Hk & HUc & Hheads & Hbl & Hq & _ & _ & Hcf & _).
repeat (split; [assumption|]). exact Hscan.
Qed.

Lemma decL_free : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k Ex ss ms md',
  dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  (forall W3 ly3 S3 U3 regs3 mem3 md3 k3, dec_at_free B d q W3 ly3 S3 U3 regs3 mem3 md3 k3 ->
     SRr tfibsegs W3 (cfg_at tfibsegs A_fuzz_free regs3 mem3 md3) (dec_post B d)) ->
  st_ok tfibsegs Ex ss (restrict (w_H Wc) ms) -> ss_resv ss = None -> ss_pc ss = A_fuzz_free ->
  dec_J B d lyc Sc Wc Uc (ms_mem ms) md' k -> ARU tfibsegs B lyc Sc Uc Wc (ms_mem ms) md' ->
  decL_memf d q six Wc lyc Sc (ms_mem ms) ->
  dec_frame_ok Wc (ms_mem ms) (d_sp d - DEC_F) (d_regs d) -> dec_lenp_slot Wc (ms_mem ms) (d_sp d - DEC_F) (d_lenp d) ->
  getr (ms_regs ms) 10 = w64 q -> getr (ms_regs ms) 1 = w64 DEC_RA_FREE -> spZ (ms_regs ms) = d_sp d - DEC_F ->
  getr (ms_regs ms) 3 = getr (d_regs d) 3 -> getr (ms_regs ms) 4 = getr (d_regs d) 4 ->
  getr (ms_regs ms) 8 = w64 DEC_M1 ->
  WriterSpec.b64_dec (d_tb d) = None ->
  SRr tfibsegs Wc (mkCfg ms md') (dec_post B d).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k Ex ss ms md' HH HFREE HS Hrv Hpc HJ HARU
  (Hrb & Hra & Hglob & HKe & HZb) HFr HLs R10 R1 Hsp R3 R4 R8 Hdec.
rewrite (st_ok_restrict_mkst tfibsegs (w_H Wc) Ex ss ms HS Hrv), Hpc.
apply (HFREE Wc lyc Sc Uc (ms_regs ms) (ms_mem ms) md' k).
unfold dec_head in HH. cbv zeta in HH.
destruct HH as (_ & _ & Hk & HUc & Hheads & Hbl & Hq & _ & _ & Hcf & _).
unfold dec_at_free.
repeat (split; [assumption|]). exact HKe.
Qed.

Ltac decL_unhead HH :=
  unfold dec_head in HH; cbv zeta in HH;
  destruct HH as (HJ & HARU & Hk & HUc & Hheads & Hbl & Hq & Hrb & Hra & Hcf & Hglob & Hsp & R3 & R4 & R8 & R9 &
    R18 & R19 & R20 & R21 & R22 & Hacc & R23 & R24 & R25 & R26 & R27 & HFr & HLs & HNq & HKe & HZb & Hi & Hpad & Hsix &
    Hsix64 & Hlast & Hscan).

(* ---- L3: the memory lemmas at the cuts ---- *)
Lemma decLB_cstr_agree : forall (W : world tfibsegs) m1 m2 p l,
  (forall a, p <= a < p + Z.of_nat (length l) - (p + Z.of_nat (length l)) mod 8 + 8 ->
     aview tfibsegs (w_H W) m2 a = aview tfibsegs (w_H W) m1 a) ->
  (forall a, SHADOW_OFF <= a < kHighMemBeg -> aview tfibsegs (w_H W) m2 a = aview tfibsegs (w_H W) m1 a) ->
  cstr_ok tfibsegs W m1 p l -> cstr_ok tfibsegs W m2 p l.
Proof.
intros W m1 m2 p l AD AS H.
pose proof asan_consts as (C1 & _).
pose proof (Z.mod_pos_bound (p + Z.of_nat (length l)) 8 ltac:(lia)) as Hm.
unfold cstr_ok, cstr in H |- *.
destruct H as ((Hg & Hnz) & H4 & Hc & H32 & Ham & Hra & Hhv & Htl).
split; [split; [|exact Hnz]|].
{ apply (garr8_frame tfibsegs _ _ p _ Hg). intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
  apply (mbyte_of_aview tfibsegs). apply AD. lia. }
split; [exact H4|]. split; [exact Hc|]. split; [exact H32|]. split; [exact Ham|].
split.
{ intros x Hx. destruct (Hra x Hx) as (s & Hs1 & Hs2). exists s. split; [|exact Hs2].
  rewrite AS; [exact Hs1|]. unfold shadow_of_addr, SHADOW_OFF, kHighMemBeg. lia. }
split.
{ intros s Hs. rewrite AS; [exact (Hhv s Hs)|]. unfold shadow_addr, SHADOW_OFF, kHighMemBeg in *. lia. }
intros a Ha. rewrite AD; [exact (Htl a Ha)|]. lia.
Qed.
Lemma decLB_unp : forall ly S U (W : world tfibsegs) mem md a,
  ARU tfibsegs B ly S U W mem md -> 0 <= a < 2 ^ 64 -> (a < SHADOW_OFF \/ kHighMemBeg <= a) ->
  unpoison U mem (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Proof.
intros ly S U W mem md a H Ha Hb. apply unpoison_out. rewrite (wz a Ha).
destruct (in_ush U a) eqn:E; [|reflexivity]. exfalso.
pose proof (ush_facts tfibsegs B ly S U W mem md a H E) as (_ & U1 & U2). lia.
Qed.
Lemma decLB_aview_unp : forall ly S U (W : world tfibsegs) mem md a,
  ARU tfibsegs B ly S U W mem md -> 0 <= a < 2 ^ 64 -> (a < SHADOW_OFF \/ kHighMemBeg <= a) ->
  aview tfibsegs (w_H W) (unpoison U mem) a = aview tfibsegs (w_H W) mem a.
Proof.
intros ly S U W mem md a H Ha Hb. apply (aview_at tfibsegs). exact (decLB_unp ly S U W mem md a H Ha Hb).
Qed.
Lemma decLB_ush : forall ly S U (W : world tfibsegs) mem md x,
  AR tfibsegs B ly S W (unpoison U mem) md -> upoison_ok B ly S U -> 0 <= x ->
  (in_img tfibsegs x \/ alloc_ceiling <= x) -> in_ush U (shadow_of_addr SHADOW_OFF x) = false.
Proof.
intros ly S U W mem md x HAR HOK Hx0 Hx.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct (in_ush U (shadow_of_addr SHADOW_OFF x)) eqn:EU; [exfalso|reflexivity].
destruct (ush_granule B ly S U _ HOK EU) as (g & p & m & Hblk & Hg8 & Hgs & Hgpb & Hgn).
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md p m HAR Hblk) as (_ & _ & Hpceil & _ & _ & _ & HmM).
pose proof (req_size_pos m ltac:(lia)) as (RQ1 & RQ2).
pose proof (Z.mul_div_le (req_size m) 8 ltac:(lia)) as RQ3.
unfold shadow_addr, shadow_of_addr in Hgs.
assert (Hdiv : g / 8 = x / 8) by lia.
pose proof (Z.div_mod g 8 ltac:(lia)). pose proof (Z.mod_pos_bound g 8 ltac:(lia)).
pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
destruct Hx as [Hi | Hc].
- apply (blk_img tfibsegs B LAWS ly S W (unpoison U mem) md p m x HAR Hblk); [lia | exact Hi].
- lia.
Qed.
Lemma decLB_sp : forall d, dec_entry_ok B d ->
  alloc_ceiling + 128 <= d_sp d /\ d_sp d <= d_ot d /\ d_ot d <= 2 ^ 47.
Proof.
intros d HE.
assert (HSTK : 128 <= STK_preset_base64_decode) by (vm_compute; discriminate).
destruct HE as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPL).
pose proof (fsw_sp B _ _ _ _ _ _ _ _ _ (proj1 HPRE)) as (_ & Hsp1 & Hsp2 & _).
pose proof (proj1 HPRE) as ((_ & _ & _ & _ & _ & Hstk & _) & _).
pose proof Hstk as (_ & _ & _ & _ & _ & H47 & _ & _ & Htop2).
unfold d_sp. destruct HPL as (_ & H1 & H2 & _ & H4 & _). lia.
Qed.
Lemma decLB_blk : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k,
  dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  In (q - HEAD, d_n d + HEAD) (ablocks B lyc Sc) /\ req_size (d_n d + HEAD) = d_n d + HEAD /\
  q mod 16 = 0 /\ 4096 + HEAD <= q /\ 0 < d_n d /\ q + d_n d <= alloc_ceiling /\
  (q + d_n d <= kLowShadowBeg \/ kHighMemBeg <= q - HEAD) /\
  (forall a, q - HEAD <= a < q + d_n d -> ~ in_img tfibsegs a) /\
  ~ In (q - HEAD, d_n d + HEAD) (ablocks B (d_ly d) (d_S d)).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HH.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct HH as (_ & HARU & _ & _ & _ & Hab & Hq & Hrb & _).
destruct HARU as (HARc & _ & _).
destruct Hrb as (Hin & Hq16 & Hn & _).
assert (RQ : req_size (d_n d + HEAD) = d_n d + HEAD)
  by (unfold req_size, HEAD; destruct (Z.eqb_spec (d_n d + 16) 0); lia).
destruct (al_blocks _ _ LAWS lyc Sc Wc (unpoison Uc memc) mdc (q - HEAD) (d_n d + HEAD) HARc Hin)
  as (_ & _ & Hceil & Happ & _ & Hpw & _).
rewrite RQ in Hceil, Happ. unfold in_app in Happ.
split; [exact Hin|]. split; [exact RQ|]. split; [exact Hq16|]. split; [exact Hq|]. split; [exact Hn|].
split; [unfold HEAD in *; lia|].
split; [destruct Happ as (_ & [X | (X & _)]); [left | right]; unfold HEAD in *; lia|].
split.
{ intros a Ha. apply (blk_img tfibsegs B LAWS lyc Sc Wc (unpoison Uc memc) mdc (q - HEAD) (d_n d + HEAD) a HARc Hin).
  rewrite RQ. unfold HEAD in *. lia. }
intros X. apply in_split in X as (l1 & l2 & E).
assert (E2 : map (fun b : Z * Z => (fst b, req_size (snd b))) (ablocks B lyc Sc) =
  map (fun b : Z * Z => (fst b, req_size (snd b))) l1 ++ (q - HEAD, req_size (d_n d + HEAD)) ::
  map (fun b : Z * Z => (fst b, req_size (snd b))) l2 ++ (q - HEAD, req_size (d_n d + HEAD)) :: []).
{ rewrite Hab, E, <- app_assoc, !map_app. reflexivity. }
pose proof (YCbq.pairwise_In2 zdisjoint _ _ _ _ _ _ Hpw E2) as Z. unfold zdisjoint in Z. cbn [fst snd] in Z.
rewrite RQ in Z. unfold HEAD in *. lia.
Qed.
Lemma decLB_q : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  q mod 16 = 0 /\ 4096 + HEAD <= q /\ q + d_n d <= alloc_ceiling /\ 1 <= d_n d /\
  (q + d_n d <= SHADOW_OFF \/ kHighMemBeg <= q) /\
  ~ In (q - HEAD, d_n d + HEAD) (ablocks B (d_ly d) (d_S d)) /\
  (forall a, q <= a < q + d_n d ->
     ~ YG0d.in_img tfibsegs a /\ in_tmp_block (ablocks B (d_ly d) (d_S d)) (ablocks B lyc Sc) a /\
     (a + 1 <= tfib_D_GOT_asan_shadow_memory_dynamic_address \/ tfib_D_GOT_asan_shadow_memory_dynamic_address + 8 <= a) /\
     (a + 1 <= tfib_D_asan_shadow_memory_dynamic_address \/ tfib_D_asan_shadow_memory_dynamic_address + 8 <= a)).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH.
destruct (decLB_blk d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HH)
  as (Hin & RQ & Hq16 & Hq & Hn & Hqc & Happ & NI & NIN).
split; [exact Hq16|]. split; [exact Hq|]. split; [exact Hqc|]. split; [lia|].
split; [unfold kLowShadowBeg, SHADOW_OFF, HEAD in *; lia|].
split; [exact NIN|].
intros a Ha.
assert (Hni : ~ in_img tfibsegs a) by (apply NI; unfold HEAD; lia).
split; [exact Hni|].
split; [exists (q - HEAD), (d_n d + HEAD); split; [exact Hin|]; split; [exact NIN|]; rewrite RQ; unfold HEAD; lia|].
split; apply decLB_cell_apart; try exact Hni;
  unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address; lia.
Qed.
Lemma decLB_qw : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k memc2 mdc2,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  ARU tfibsegs B lyc Sc Uc Wc memc2 mdc2 ->
  forall a, q <= a < q + d_n d -> writable_at tfibsegs (mrestrict (w_H Wc) memc2) a.
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k memc2 mdc2 HE HH HARU2 a Ha.
pose proof (AR_laws_ok tfibsegs B) as LAWS. pose proof asan_consts as (C1 & _).
destruct (decLB_blk d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HH)
  as (Hin & RQ & Hq16 & Hq & Hn & Hqc & Happ & NI & NIN).
pose proof HARU2 as (HAR2 & _ & _).
destruct (al_blocks _ _ LAWS lyc Sc Wc (unpoison Uc memc2) mdc2 (q - HEAD) (d_n d + HEAD) HAR2 Hin)
  as (_ & _ & _ & _ & Hpr & _ & _).
rewrite RQ in Hpr.
destruct (Hpr a ltac:(unfold HEAD; lia)) as (Hp & _).
apply (apresent_writable tfibsegs).
destruct Hp as (Hh & b & Hb). split; [exact Hh|]. exists b.
assert (Happ' : a < SHADOW_OFF \/ kHighMemBeg <= a) by (unfold kLowShadowBeg, SHADOW_OFF, HEAD in *; lia).
rewrite <- (decLB_unp lyc Sc Uc Wc memc2 mdc2 a HARU2 ltac:(unfold HEAD in *; lia) Happ'). exact Hb.
Qed.
Lemma decLB_tsite : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  forall a, d_text d <= a < d_text d + Z.of_nat (length (d_tb d)) - (d_text d + Z.of_nat (length (d_tb d))) mod 8 + 8 ->
    ~ (q - HEAD <= a < q + d_n d) /\
    (a <= d_text d + Z.of_nat (length (d_tb d)) ->
       (a + 1 <= kLowShadowBeg \/ kHighMemBeg <= a) /\ (~ in_img tfibsegs a \/ a < 0x22000)).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH a Ha.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct (decLB_blk d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HH)
  as (Hin & RQ & Hq16 & Hq & Hn & Hqc & Happq & NIq & NIN).
pose proof HH as (_ & HARU & _ & _ & _ & Hab & _). destruct HARU as (HARc & _ & _).
destruct HE as (_ & _ & _ & _ & _ & Hcs & Hws & _).
pose proof Hcs as (_ & Ht4096 & Htc & _).
pose proof (Z.mod_pos_bound (d_text d + Z.of_nat (length (d_tb d))) 8 ltac:(lia)) as Hm.
pose proof (Z.div_mod (d_text d + Z.of_nat (length (d_tb d))) 8 ltac:(lia)) as Hdm.
pose proof (Z.div_mod q 16 ltac:(lia)) as Hqdm.
assert (BLK : forall b m, In (b, m) (ablocks B (d_ly d) (d_S d)) -> b <= d_text d ->
  d_text d + Z.of_nat (length (d_tb d)) + 1 <= b + m ->
  ~ (q - HEAD <= a < q + d_n d) /\
  (a <= d_text d + Z.of_nat (length (d_tb d)) ->
     (a + 1 <= kLowShadowBeg \/ kHighMemBeg <= a) /\ (~ in_img tfibsegs a \/ a < 0x22000))).
{ intros b m Hbm Hb1 Hb2.
  assert (Hbmc : In (b, m) (ablocks B lyc Sc)) by (rewrite Hab; apply in_or_app; left; exact Hbm).
  assert (Hne : (b, m) <> (q - HEAD, d_n d + HEAD)) by (intros X; rewrite X in Hbm; exact (NIN Hbm)).
  pose proof (sep_blocks tfibsegs B LAWS lyc Sc Wc (unpoison Uc memc) mdc b m (q - HEAD) (d_n d + HEAD)
    HARc Hbmc Hin Hne) as Hsep.
  unfold zdisjoint in Hsep. cbn [fst snd] in Hsep. rewrite RQ in Hsep.
  destruct (al_blocks _ _ LAWS lyc Sc Wc (unpoison Uc memc) mdc b m HARc Hbmc)
    as (Hb16 & Hb4096 & Hbc & Happ & _ & _ & HmM).
  pose proof (req_size_pos m ltac:(lia)) as (RQ1 & RQ2).
  unfold in_app in Happ.
  split; [unfold HEAD in *; lia|].
  intros Hat. split; [unfold kLowShadowBeg, kHighMemBeg in *; lia|]. left.
  apply (blk_img tfibsegs B LAWS lyc Sc Wc (unpoison Uc memc) mdc b m a HARc Hbmc). lia. }
destruct Hws as [(Hnil & _) | [(p & kk & Hp0 & Hrb' & Hpt & Htp) | [(p & kk & Hpne & Hinp & Hpt & Htp & _) | (l & Hinl & Hll)]]].
- exfalso. apply app_eq_nil in Hnil as [_ X]. discriminate X.
- destruct Hrb' as (Hinp & Hp16 & Hkk & _). rewrite length_app in Htp. cbn [length] in Htp.
  apply (BLK (p - HEAD) (kk + HEAD) Hinp); unfold HEAD; lia.
- rewrite length_app in Htp. cbn [length] in Htp. apply (BLK p kk Hinp); lia.
- rewrite length_app in Hll. cbn [length] in Hll. change (Nat.succ (length l)) with (S (length l)) in Hll.
  destruct (decLB_ro_strs (d_text d) l Hinl) as (R1 & R2).
  split.
  + intros X. apply (NIq a X). apply decLB_in_img. lia.
  + intros Hat. split; [unfold kLowShadowBeg; lia | right; lia].
Qed.
Lemma decLB_text : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  4096 <= d_text d /\ d_text d + Z.of_nat (length (d_tb d)) + 1 <= alloc_ceiling /\
  (forall a, d_text d <= a <= d_text d + Z.of_nat (length (d_tb d)) ->
     ~ (SHADOW_OFF <= a < SHADOW_OFF + 17592186044416) /\
     ~ (q - HEAD <= a < q - HEAD + req_size (d_n d + HEAD)) /\
     (a + 1 <= tfib_D_GOT_asan_shadow_memory_dynamic_address \/ tfib_D_GOT_asan_shadow_memory_dynamic_address + 8 <= a) /\
     (a + 1 <= tfib_D_asan_shadow_memory_dynamic_address \/ tfib_D_asan_shadow_memory_dynamic_address + 8 <= a)).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH.
pose proof HE as (_ & _ & _ & _ & _ & Hcs & _). pose proof Hcs as (_ & Ht4096 & Htc & _).
split; [exact Ht4096|]. split; [exact Htc|].
intros a Ha.
pose proof (Z.mod_pos_bound (d_text d + Z.of_nat (length (d_tb d))) 8 ltac:(lia)) as Hm.
destruct (decLB_tsite d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH a ltac:(lia)) as (T1 & T2).
destruct (T2 ltac:(lia)) as (T3 & T4).
destruct (decLB_blk d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HH) as (_ & RQ & _).
split; [unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; lia|].
split; [rewrite RQ; unfold HEAD in *; lia|].
destruct T4 as [Hni | Hlow].
- split; apply decLB_cell_apart; try exact Hni;
    unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address; lia.
- split; left; unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address; lia.
Qed.
Lemma decLB_lsite : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  4096 <= d_lenp d /\ d_lenp d + 8 <= 2 ^ 47 /\
  (forall a, d_lenp d <= a < d_lenp d + 8 -> (d_sp d <= a \/ a < alloc_ceiling) /\ ~ (q - HEAD <= a < q + d_n d)).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH.
pose proof (decL_lenp_range d HE) as (L1 & L2 & _ & L4 & _).
pose proof (decLB_sp d HE) as (S1 & S2 & S3).
destruct (decLB_blk d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HH)
  as (Hin & RQ & Hq16 & Hq & Hn & Hqc & _).
split; [exact L1|]. split; [exact L2|].
intros a Ha. split; [left; lia|]. unfold HEAD. lia.
Qed.
Lemma decLB_tr : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k m1 m2,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  decL_memf d q six Wc lyc Sc m1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (alloc_ceiling <= a < d_sp d) ->
     ~ (q + Z.of_nat (length (WriterSpec.six_bytes six)) <= a < q + d_n d) ->
     aview tfibsegs (w_H Wc) m2 a = aview tfibsegs (w_H Wc) m1 a) ->
  decL_memf d q six Wc lyc Sc m2.
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k m1 m2 HE HH HM HA.
pose proof asan_consts as (C1 & _).
destruct (decLB_blk d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HH)
  as (Hin & RQ & Hq16 & Hq & Hn & Hqc & Happq & NIq & NIN).
pose proof (decLB_sp d HE) as (S1 & S2 & S3).
destruct (decLB_lsite d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH) as (L1 & L2 & LS).
pose proof (decLB_tsite d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH) as TS.
unfold HEAD in Hq, Happq, NIq, LS, TS.
pose proof HH as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & _ & _ & _ & _ & _ & _ & _ & Hi & _ & Hlsix & _).
assert (HNB : Z.of_nat (length (WriterSpec.six_bytes six)) < d_n d)
  by (unfold d_n; apply decLA_nbytes; lia).
pose proof HE as (_ & _ & _ & _ & _ & Hcs & _). pose proof Hcs as (_ & Ht4096 & Htc & _).
set (L := Z.of_nat (length (WriterSpec.six_bytes six))) in *.
assert (A1 : forall a, 0 <= a < alloc_ceiling -> ~ (q + L <= a < q + d_n d) ->
  aview tfibsegs (w_H Wc) m2 a = aview tfibsegs (w_H Wc) m1 a) by (intros a Ha Hb; apply HA; lia).
assert (A2 : forall a, d_sp d <= a < 2 ^ 64 -> aview tfibsegs (w_H Wc) m2 a = aview tfibsegs (w_H Wc) m1 a)
  by (intros a Ha; apply HA; lia).
assert (ASH : forall a, SHADOW_OFF <= a < kHighMemBeg -> aview tfibsegs (w_H Wc) m2 a = aview tfibsegs (w_H Wc) m1 a).
{ intros a Ha. apply A1; unfold SHADOW_OFF, kHighMemBeg, kLowShadowBeg, HEAD in *; lia. }
assert (AIMG : forall a, in_img tfibsegs a -> aview tfibsegs (w_H Wc) m2 a = aview tfibsegs (w_H Wc) m1 a).
{ intros a Hia. pose proof (fs_segs_img a Hia) as Hl. unfold FS_IMG_END in Hl.
  apply A1; [lia|]. intros X. apply (NIq a); [unfold HEAD; lia | exact Hia]. }
destruct HM as (Hrb1 & Hra1 & Hgl1 & Hkept1 & Hzb1).
split.
{ destruct Hrb1 as (Hin1 & H16 & Hn1 & Hv1). split; [exact Hin1|]. split; [exact H16|]. split; [exact Hn1|].
  apply (decLB_val_mem _ m1 m2 _ _ _); [|exact Hv1]. intros kk Hk. apply A1; unfold HEAD in *; lia. }
split.
{ apply (range_addressable_agree (aview tfibsegs (w_H Wc) m1) (aview tfibsegs (w_H Wc) m2) SHADOW_OFF q (d_n d));
    [|exact Hra1].
  intros x Hx. apply ASH. unfold shadow_of_addr, SHADOW_OFF, kHighMemBeg. lia. }
split.
{ unfold fs_glob, fs_glob_at in *. destruct Hgl1 as (V1 & V2 & V3 & V4 & R).
  assert (VB : forall g v, 0x10000 <= g -> g + 8 <= 0x5fd000 ->
    val_mem tfibsegs (mrestrict (w_H Wc) m1) g 8 v -> val_mem tfibsegs (mrestrict (w_H Wc) m2) g 8 v).
  { intros g v Hg1 Hg2 Hv. apply (decLB_val_mem _ m1 m2 _ _ _); [|exact Hv].
    intros kk Hk. apply AIMG. apply decLB_in_img. lia. }
  unfold G_LIVE, G_PEAK, G_COUNT, G_FAIL in *.
  split; [apply VB; [lia | lia | exact V1]|]. split; [apply VB; [lia | lia | exact V2]|].
  split; [apply VB; [lia | lia | exact V3]|]. split; [apply VB; [lia | lia | exact V4]|]. exact R. }
split.
{ destruct Hkept1 as (Kv & Kw & Kc & Kr).
  split.
  { apply (decLB_val_mem _ m1 m2 _ _ _); [|exact Kv]. intros kk Hk.
    destruct (LS (d_lenp d + Z.of_nat kk) ltac:(lia)) as ([Hs | Hc] & Hnq); [apply A2; lia | apply A1; lia]. }
  split.
  { intros a Ha Hno. destruct (Kw a Ha Hno) as [E1 E2]. split.
    - rewrite <- E1. apply (mbyte_of_aview tfibsegs). apply A2. lia.
    - etransitivity; [exact E2|]. apply decLB_wr_eq; [lia | | apply A2; lia].
      intros X. pose proof (fs_segs_img a X) as Hl. unfold FS_IMG_END in Hl. lia. }
  split.
  { apply (decLB_cstr_agree Wc m1 m2 (d_text d) (d_tb d)); [| exact ASH | exact Kc].
    intros a Ha. pose proof (Z.mod_pos_bound (d_text d + Z.of_nat (length (d_tb d))) 8 ltac:(lia)) as Hm.
    pose proof (Z.div_mod (d_text d + Z.of_nat (length (d_tb d))) 8 ltac:(lia)) as Hdm.
    pose proof (Z.div_mod alloc_ceiling 4096 ltac:(lia)) as Hda.
    pose proof (proj2 YM05.alloc_ceiling_value) as Hac.
    destruct (TS a Ha) as (T1 & _). apply A1; [lia|]. unfold HEAD in *. lia. }
  intros a Hro Ho He. rewrite (AIMG a (decLB_ro_img a Hro)). exact (Kr a Hro Ho He). }
unfold zbytes_at in *. apply (garr8_frame tfibsegs _ _ q _ Hzb1). intros a Ha. fold L in Ha.
apply (mbyte_of_aview tfibsegs). apply A1; unfold HEAD in *; lia.
Qed.
Lemma decLB_memf : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k,
  dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k -> decL_memf d q six Wc lyc Sc memc.
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HH.
destruct HH as (_ & _ & _ & _ & _ & _ & _ & Hrb & Hra & _ & Hgl & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & _ & _ & _ & _ & _ & Hkept & Hzb & _).
exact (conj Hrb (conj Hra (conj Hgl (conj Hkept Hzb)))).
Qed.
Lemma decLB_keep : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k memc1 memc2 lo hi,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  decL_memf d q six Wc lyc Sc memc1 -> alloc_ceiling <= lo -> hi <= d_sp d ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview tfibsegs (w_H Wc) memc2 a = aview tfibsegs (w_H Wc) memc1 a) ->
  decL_memf d q six Wc lyc Sc memc2.
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k memc1 memc2 lo hi HE HH HM Hlo Hhi HA.
apply (decLB_tr d q i six pad acc Wc lyc Sc Uc regsc memc mdc k memc1 memc2 HE HH HM).
intros a Ha H1 H2. apply HA; [exact Ha | lia].
Qed.
Lemma decLB_store : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k memc1 memc2 lo hi six' b,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  decL_memf d q six Wc lyc Sc memc1 -> alloc_ceiling <= lo -> hi <= d_sp d ->
  Z.of_nat (length (WriterSpec.six_bytes six)) < d_n d ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> a <> q + Z.of_nat (length (WriterSpec.six_bytes six)) ->
     aview tfibsegs (w_H Wc) memc2 a = aview tfibsegs (w_H Wc) memc1 a) ->
  aview tfibsegs (w_H Wc) memc2 (q + Z.of_nat (length (WriterSpec.six_bytes six))) = Some b -> 0 <= b < 256 ->
  WriterSpec.six_bytes six' = WriterSpec.six_bytes six ++ [b] ->
  decL_memf d q six' Wc lyc Sc memc2.
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k memc1 memc2 lo hi six' b
  HE HH HM Hlo Hhi Hlen HA Hb Hbr Hsix.
assert (HM2 : decL_memf d q six Wc lyc Sc memc2).
{ apply (decLB_tr d q i six pad acc Wc lyc Sc Uc regsc memc mdc k memc1 memc2 HE HH HM).
  intros a Ha H1 H2. apply HA; [exact Ha | lia | lia]. }
destruct HM2 as (R1 & R2 & R3 & R4 & R5).
split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|].
unfold zbytes_at in *. rewrite Hsix.
destruct (aview_byte tfibsegs (w_H Wc) memc2 _ b Hb) as (w & Ew & Ebw & _).
apply (garr8_app1 tfibsegs _ _ q _ b R5); [| exact Hbr | intros a _; reflexivity].
intros [|kk] Hk; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r. rewrite Ew. f_equal.
unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. rewrite !Z.mod_small by lia. subst b. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma decLB_g64 : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k memc1 lo hi,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  alloc_ceiling <= lo -> hi <= d_sp d ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview tfibsegs (w_H Wc) memc1 a = aview tfibsegs (w_H Wc) memc a) ->
  rom_view tfibsegs Wc memc1 /\ zbytes_at tfibsegs Wc memc1 G_B64 WriterSpec.b64_table /\
  range_addressable (aview tfibsegs (w_H Wc) memc1) SHADOW_OFF G_B64 65 /\
  shadow_hull_vis (aview tfibsegs (w_H Wc) memc1) G_B64 65.
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k memc1 lo hi HE HH Hlo Hhi HA.
pose proof asan_consts as (C1 & _).
pose proof HH as (_ & HARU & _).
pose proof HARU as (HARc & HUOKc & HUPOc).
pose proof (decLB_memf d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HH) as (_ & _ & _ & (_ & _ & _ & Kr) & _).
assert (A1 : forall a, 0 <= a < alloc_ceiling -> aview tfibsegs (w_H Wc) memc1 a = aview tfibsegs (w_H Wc) memc a)
  by (intros a Ha; apply HA; lia).
assert (AU : forall a, in_img tfibsegs a ->
  aview tfibsegs (w_H Wc) memc1 a = aview tfibsegs (w_H Wc) (unpoison Uc memc) a).
{ intros a Hia. pose proof (fs_segs_img a Hia) as Hl. unfold FS_IMG_END in Hl.
  rewrite A1 by lia. symmetry. apply (decLB_aview_unp lyc Sc Uc Wc memc mdc a HARU); [lia | left; unfold SHADOW_OFF; lia]. }
assert (Kr' : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H Wc) (unpoison Uc memc))).
{ intros a Hro Ho He. pose proof (decLB_ro_img a Hro) as Hia. pose proof (fs_segs_img a Hia) as Hl.
  unfold FS_IMG_END in Hl.
  rewrite (decLB_aview_unp lyc Sc Uc Wc memc mdc a HARU); [exact (Kr a Hro Ho He) | lia | left; unfold SHADOW_OFF; lia]. }
pose proof HIMG as (_ & HIM2).
destruct (HIM2 lyc Sc Wc (unpoison Uc memc) mdc HARc Kr') as (Hrom & _ & Hstrs & _).
assert (HinG : In (G_B64, map WriterSpec.b64c (map Z.of_nat (seq 0 64))) FS_RO_STRS)
  by (unfold FS_RO_STRS; repeat (first [left; reflexivity | right])).
pose proof (proj1 (Forall_forall _ _) Hstrs _ HinG) as (Hcs & _). cbn [fst snd] in Hcs.
assert (HL : length (map WriterSpec.b64c (map Z.of_nat (seq 0 64))) = 64%nat) by reflexivity.
destruct Hcs as ((Hg & _) & _ & _ & _ & _ & Hra & Hhv & _).
rewrite HL in Hra, Hhv. change (Z.of_nat 64 + 1) with 65 in Hra, Hhv.
split.
{ intros a Ha. pose proof Ha as (sg & Hsg & _ & Hr).
  assert (Hia : in_img tfibsegs a) by (exists sg; split; [exact Hsg | exact Hr]).
  rewrite (AU a Hia). exact (Hrom a Ha). }
split.
{ unfold zbytes_at, WriterSpec.b64_table. apply (garr8_frame tfibsegs _ _ G_B64 _ Hg). intros a Ha.
  rewrite length_app, HL in Ha. cbn [length] in Ha.
  apply (mbyte_of_aview tfibsegs). apply AU. apply decLB_in_img. unfold G_B64 in *. lia. }
split.
{ apply (range_addressable_agree (aview tfibsegs (w_H Wc) (unpoison Uc memc)) (aview tfibsegs (w_H Wc) memc1)
    SHADOW_OFF G_B64 65); [|exact Hra].
  intros x Hx. rewrite A1 by (unfold shadow_of_addr, SHADOW_OFF, G_B64 in *; lia).
  symmetry. apply (aview_unpoison_out tfibsegs). rewrite wz by (unfold shadow_of_addr, SHADOW_OFF, G_B64 in *; lia).
  apply (decLB_ush lyc Sc Uc Wc memc mdc x HARc HUOKc); [unfold G_B64 in *; lia|]. left.
  apply decLB_in_img. unfold G_B64 in *. lia. }
intros s Hs.
assert (Hs0 : 0 <= s < alloc_ceiling) by (unfold shadow_addr, SHADOW_OFF, G_B64 in *; lia).
rewrite A1 by exact Hs0.
destruct (in_ush Uc (bv_unsigned (Z_to_bv 64 s))) eqn:EU.
- rewrite wz in EU by lia. rewrite (HUPOc s EU). discriminate.
- rewrite <- (aview_unpoison_out tfibsegs (w_H Wc) Uc memc s EU). exact (Hhv s Hs).
Qed.
Lemma decLB_lenp : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  d_sp d <= d_lenp d /\ d_lenp d + 8 <= d_ot d /\ d_lenp d mod 8 = 0 /\ 2 ^ 46 <= d_lenp d /\
  kHighMemBeg <= d_lenp d /\ d_lenp d + 8 <= 2 ^ 47 /\
  range_addressable (aview tfibsegs (w_H Wc) memc) SHADOW_OFF (d_lenp d) 8 /\
  (forall a, d_lenp d <= a < d_lenp d + 8 -> writable_at tfibsegs (mrestrict (w_H Wc) memc) a).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & _).
pose proof (decLB_sp d HE) as (S1 & S2 & S3).
destruct HE as (HPRE & _ & _ & _ & _ & _ & _ & _ & _ & Hl8 & _ & _ & _ & _ & _ & _ & _ & _ & HPL).
destruct HPL as (_ & Hsplp & Hlpot & _ & Hottop & _).
pose proof (proj1 HPRE) as ((_ & _ & _ & _ & _ & Hstk & _) & _).
pose proof Hstk as (_ & HSTK0 & Hceil & Hslo & Hshi & H47 & _ & _ & Htop2).
unfold d_sp in *.
pose proof HH as (HJ & HARU & _).
pose proof HARU as (HARc & HUOKc & _).
unfold dec_J, d_STKJ in HJ.
destruct HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpresc & _).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
unfold d_sp in Hpresc.
split; [exact Hsplp|]. split; [exact Hlpot|]. split; [exact Hl8|]. split; [lia|].
split; [unfold kHighMemBeg; lia|]. split; [lia|].
split.
{ assert (HLO : layout_ok lyc) by exact (am_layout _ _ _ _ (proj1 HARc)).
  pose proof (lo_top lyc HLO) as LTOP.
  assert (Hlo8 : ly_stk_lo lyc mod 8 = 0).
  { destruct LTOP as (_ & _ & _ & _ & L5 & _). unfold page_aligned in L5.
    apply Z.mod_divide; [lia|]. apply (Z.divide_trans 8 4096);
      [exists 512; reflexivity | apply Z.mod_divide; [lia | exact L5]]. }
  assert (Hhi8 : ly_stk_hi lyc mod 8 = 0).
  { destruct LTOP as (_ & _ & _ & _ & _ & L6 & _). unfold page_aligned in L6.
    apply Z.mod_divide; [lia|]. apply (Z.divide_trans 8 4096);
      [exists 512; reflexivity | apply Z.mod_divide; [lia | exact L6]]. }
  assert (HZS : zero_shadow (aview tfibsegs (w_H Wc) (unpoison Uc memc)) SHADOW_OFF
                  (ly_stk_lo lyc) (ly_stk_hi lyc - ly_stk_lo lyc)).
  { exact (al_zshadow _ _ LAWS lyc Sc Wc (unpoison Uc memc) mdc
             (ly_stk_lo lyc, ly_stk_hi lyc - ly_stk_lo lyc) HARc (or_introl eq_refl)). }
  assert (HRAU : range_addressable (aview tfibsegs (w_H Wc) (unpoison Uc memc)) SHADOW_OFF (d_lenp d) 8).
  { eapply range_addressable_sub;
      [ apply (zero_shadow_range (aview tfibsegs (w_H Wc) (unpoison Uc memc)) SHADOW_OFF
                 (ly_stk_lo lyc) (ly_stk_hi lyc - ly_stk_lo lyc) Hlo8
                 ltac:(rewrite Zminus_mod, Hlo8, Hhi8; reflexivity) HZS)
      | lia | lia]. }
  eapply range_addressable_agree; [|exact HRAU].
  intros x Hx. apply aview_at. symmetry. apply unpoison_out.
  rewrite (wz (shadow_of_addr SHADOW_OFF x)) by (unfold shadow_of_addr, SHADOW_OFF; lia).
  apply (decLB_ush lyc Sc Uc Wc memc mdc x HARc HUOKc); [lia | right; lia]. }
intros a Ha.
apply (apresent_writable tfibsegs).
apply (fsw_apresent_unpoison B lyc Sc Uc Wc memc mdc a HARU); [unfold kHighMemBeg; lia|].
apply Hpresc. lia.
Qed.

(* ---- L1: the head state and its shadow entry ---- *)
Lemma decL_text_byte : forall d (W : world tfibsegs) mem (i : nat),
  cstr_ok tfibsegs W mem (d_text d) (d_tb d) -> (i <= length (d_tb d))%nat ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (d_text d + Z.of_nat i) 1 (nth i (d_tb d ++ [0]) 0) /\
  0 <= nth i (d_tb d ++ [0]) 0 < 256.
Proof.
intros d W mem i ((HG & _) & _) Hi. apply HG. rewrite length_app. cbn [length]. lia.
Qed.

(* the atom facts of the s-registers at a cut, from the registers' values *)
Lemma decL_sgf_ok : forall (E : env) q tx n acc bits pad plo phi blo bhi,
  ew E 8 = w64 DEC_M1 -> ew E 9 = w64 q -> ew E 18 = w64 tx -> ew E 19 = w64 G_B64 -> ew E 20 = w64 SHADOW_OFF ->
  ew E 21 = w64 n -> ew E 22 = w64 acc -> ew E 23 = w64 bits -> ew E 24 = w64 pad -> ew E 25 = w64 (tx - 1) ->
  ew E 26 = w64 61 -> ew E 27 = w64 DEC_WSMASK -> ew E 34 = w64 (DEC_M1 - q) ->
  4096 + HEAD <= q -> q mod 16 = 0 -> q <= DEC_CEIL -> 0 <= n <= 2 ^ 30 ->
  4096 <= tx <= DEC_CEIL -> 0 <= acc < 2 ^ 64 -> blo <= bits <= bhi -> 0 <= bits <= 6 -> bits mod 2 = 0 ->
  plo <= pad <= phi -> 0 <= pad <= 2 ^ 28 ->
  atoms_ok E (decL_sgf plo phi blo bhi).
Proof.
intros E q tx n acc bits pad plo phi blo bhi E8 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27 E34
  Hq Hq16 Hqc Hn Htx Hacc Hb1 Hb2 Hb3 Hp1 Hp2.
unfold DEC_CEIL, HEAD in *.
unfold decL_sgf. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E8, E9, E18, E19, E20, E21, E22, E23, E24, E25, E26, E27, E34.
rewrite (decL_w64u DEC_M1) by (unfold DEC_M1; lia).
rewrite (decL_w64u (DEC_M1 - q)) by (unfold DEC_M1; lia).
rewrite (decL_w64u DEC_WSMASK) by (unfold DEC_WSMASK; lia).
rewrite (decL_w64u q), (decL_w64u tx), (decL_w64u (tx - 1)), (decL_w64u n), (decL_w64u acc), (decL_w64u bits),
  (decL_w64u pad) by lia.
rewrite (decL_w64u G_B64) by (unfold G_B64; lia).
rewrite (decL_w64u SHADOW_OFF) by (unfold SHADOW_OFF; lia).
rewrite (decL_w64u 61) by lia.
change (2 ^ 0) with 1. change (2 ^ 4) with 16. change (2 ^ 1) with 2. rewrite !Z.mod_1_r.
unfold DEC_M1, DEC_WSMASK, G_B64, SHADOW_OFF, DEC_CEIL, HEAD.
repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

(* the registers a cut keeps from the head (callee-saved, so also across memchr) *)
Definition decLO_kregs : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Ltac decLO_in := cbv [decLO_kregs In]; repeat (first [left; reflexivity | right]).

(* the atom facts of a cut, from the head's registers (any register map keeping the head's callee-saved ones) *)
Lemma decL_atoms_k : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs0 ex plo phi blo bhi,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  (forall r, In r decLO_kregs -> getr regs0 r = getr regsc r) ->
  plo <= pad <= phi -> blo <= 6 * Z.of_nat (length six) mod 8 <= bhi ->
  atoms_ok (decL_E d q regs0 ex) (decL_sgf plo phi blo bhi).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs0 ex plo phi blo bhi HE HH RK Hp Hb.
pose proof asan_consts as (C1 & _ & _ & _).
pose proof (decLB_q d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH) as (Q16 & Q1 & Q2 & _).
pose proof (decLB_text d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH) as (T1 & T2 & _).
pose proof HE as (_ & _ & _ & _ & _ & _ & _ & _ & Htb & _).
pose proof (WriterSpecFacts.six_bytes_length six) as Hnb.
pose proof HH as HH0. decL_unhead HH0.
assert (Hbits : 0 <= 6 * Z.of_nat (length six) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
assert (Hbits2 : (6 * Z.of_nat (length six) mod 8) mod 2 = 0) by (Z.div_mod_to_equations; lia).
assert (Hnb2 : 6 * Z.of_nat (length six) / 8 <= 2 ^ 30) by (Z.div_mod_to_equations; lia).
assert (Hbits6 : 6 * Z.of_nat (length six) mod 8 <= 6)
  by (destruct (decLA_bits_cases (Z.of_nat (length six)) ltac:(lia)) as [X|[X|[X|X]]]; lia).
assert (EK : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> In r decLO_kregs ->
  ew (decL_E d q regs0 ex) n = getr regsc r)
  by (intros n r Hn Hr; rewrite (decL_E_reg d q regs0 ex n r Hn); exact (RK r Hr)).
apply (decL_sgf_ok _ q (d_text d + Z.of_nat i) (Z.of_nat (length (WriterSpec.six_bytes six))) acc
  (6 * Z.of_nat (length six) mod 8) pad).
- rewrite (EK 8%nat 8%bv eq_refl ltac:(decLO_in)). exact R8.
- rewrite (EK 9%nat 9%bv eq_refl ltac:(decLO_in)). exact R9.
- rewrite (EK 18%nat 18%bv eq_refl ltac:(decLO_in)). exact R18.
- rewrite (EK 19%nat 19%bv eq_refl ltac:(decLO_in)). exact R19.
- rewrite (EK 20%nat 20%bv eq_refl ltac:(decLO_in)). exact R20.
- rewrite (EK 21%nat 21%bv eq_refl ltac:(decLO_in)). exact R21.
- rewrite (EK 22%nat 22%bv eq_refl ltac:(decLO_in)). exact R22.
- rewrite (EK 23%nat 23%bv eq_refl ltac:(decLO_in)). exact R23.
- rewrite (EK 24%nat 24%bv eq_refl ltac:(decLO_in)). exact R24.
- rewrite (EK 25%nat 25%bv eq_refl ltac:(decLO_in)). exact R25.
- rewrite (EK 26%nat 26%bv eq_refl ltac:(decLO_in)). exact R26.
- rewrite (EK 27%nat 27%bv eq_refl ltac:(decLO_in)). exact R27.
- rewrite decL_E_nq. reflexivity.
- unfold HEAD in *; lia.
- exact Q16.
- assert (Hdn : 0 <= d_n d)
    by (unfold d_n, dec_size; pose proof (Z.div_pos (Z.of_nat (length (d_tb d))) 4 ltac:(lia) ltac:(lia)); lia).
  unfold DEC_CEIL, HEAD in *; lia.
- lia.
- unfold DEC_CEIL in *; lia.
- exact Hacc.
- exact Hb.
- lia.
- exact Hbits2.
- exact Hp.
- lia.
Qed.

Lemma decL_head_st : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  let c := nth i (d_tb d ++ [0]) 0 in
  st_ok tfibsegs (decL_E d q regsc [Z_to_bv 64 c]) decL_hss
    (restrict (w_H Wc) (YK11.mkst regsc (Z_to_bv 64 DEC_HEAD) memc (YK11.seg_rom tfibsegs))) /\
  sh_ok tfibsegs decL_Bx decL_hSH (decL_E d q regsc [Z_to_bv 64 c]) (mrestrict (w_H Wc) memc).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH c.
pose proof asan_consts as (C1 & _ & _ & _).
pose proof (decLB_text d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH) as (T1 & T2 & T3).
pose proof (decLB_q d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH) as (Q16 & Q1 & Q2 & _).
pose proof (decL_lenp_range d HE) as (L1 & L2 & _).
pose proof HH as HH0. decL_unhead HH.
pose proof HKe as (_ & _ & HCS & _).
pose proof HCS as ((_ & _) & _ & _ & Hlen32 & _ & HRA & _).
destruct (decL_text_byte d Wc memc i HCS Hi) as (Vc & Rc). fold c in Vc, Rc.
pose proof (fsw_sp B _ _ _ _ _ _ _ _ _ (proj1 (proj1 HE))) as (Hsp16 & Hsp1 & Hsp2 & _).
assert (HSTK : 128 <= STK_preset_base64_decode) by (vm_compute; discriminate).
set (E := decL_E d q regsc [Z_to_bv 64 c]).
assert (E18 : bv_unsigned (ew E 18) = d_text d + Z.of_nat i).
{ unfold E. rewrite (decL_E_reg d q regsc _ 18 18%bv eq_refl), R18. apply decL_w64u. lia. }
assert (E25 : bv_unsigned (ew E 25) = d_text d + Z.of_nat i - 1).
{ unfold E. rewrite (decL_E_reg d q regsc _ 25 25%bv eq_refl), R25. apply decL_w64u. lia. }
assert (E48 : ew E 48 = Z_to_bv 64 c) by (unfold E; exact (decL_E_ex d q regsc _ 0)).
assert (E2 : bv_unsigned (ew E 2) = d_sp d - DEC_F)
  by (unfold E; rewrite (decL_E_reg d q regsc _ 2 2%bv eq_refl); exact Hsp).
split.
- apply (decL_build d q Wc lyc Sc Uc regsc memc mdc k [Z_to_bv 64 c] DEC_HEAD [decL_txr] decL_hgf HE HJ HARU
    Hsp HFr HLs HNq ltac:(pose proof (decL_dn_pos d); unfold HEAD in *; lia)).
  + vm_compute. reflexivity.
  + fold E. constructor; [|constructor].
    unfold decL_txr, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E25. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs E _ _ 1 1 (SOff 48 0) c);
      [rewrite fsw_SOff0, E48; reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
      | replace (d_text d + Z.of_nat i - 1 + 1) with (d_text d + Z.of_nat i) by lia; exact Vc].
  + fold E. apply pairwise_disjoint_of_extents.
    unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, decL_txr, extent_of_region.
    cbn [map app YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite E2, E25.
    destruct (T3 (d_text d + Z.of_nat i) ltac:(lia)) as (_ & _ & G1 & G2).
    unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, DEC_F, d_sp in *.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    destruct G1 as [G1|G1]; destruct G2 as [G2|G2];
    repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia].
  + fold E. unfold decL_hgf. cbn [atoms_ok]. split.
    * unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E48, (wz c) by lia. rewrite Z.pow_0_r, Z.mod_1_r. lia.
    * apply (decL_atoms_k d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regsc [Z_to_bv 64 c] 0 (2 ^ 28) 0 6 HE HH0
        (fun r _ => eq_refl));
        [pose proof HE as (_ & _ & _ & _ & _ & _ & _ & _ & HLEN & _); lia
        | destruct (decLA_bits_cases (Z.of_nat (length six)) ltac:(lia)) as [X|[X|[X|X]]]; lia].
- unfold sh_ok, decL_hSH. constructor; [|constructor].
  apply (shent_ok_of_range tfibsegs (w_H Wc) memc E decL_Bx 18%nat (d_text d) (Z.of_nat (length (d_tb d)) + 1)
           (d_text d + Z.of_nat i) 0 1 HRA).
  + unfold decL_Bx. apply (U_atom E 20 SHADOW_OFF);
      [unfold E; rewrite (decL_E_reg d q regsc _ 20 20%bv eq_refl), R20; reflexivity | unfold SHADOW_OFF; lia].
  + apply (U_atom E 18 (d_text d + Z.of_nat i));
      [unfold E; rewrite (decL_E_reg d q regsc _ 18 18%bv eq_refl), R18; reflexivity | lia].
  + lia.
  + lia.
  + intros x Hx. cbn in Hx. destruct (T3 x ltac:(lia)) as (A1 & _). exact A1.
Qed.

(* ---- the skip arms: whitespace and '=' (port of lib/A/FSW_dec_L.v) ---- *)
Definition decL_hcfg (regsc : bvmap 5 word) (memc : word -> option byte) (mdc : Model) : config :=
  mkCfg (YK11.mkst regsc (Z_to_bv 64 DEC_HEAD) memc (YK11.seg_rom tfibsegs)) mdc.

Lemma decL_fr_agree : forall Ex rs (H : word -> bool) m1 m2 lo hi,
  frame_of Ex rs (mrestrict H m1) (mrestrict H m2) ->
  (forall x, in_wrange Ex rs x -> lo <= x < hi) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview tfibsegs H m2 a = aview tfibsegs H m1 a.
Proof.
intros Ex rs H m1 m2 lo hi HF Hw a Ha Hna. unfold aview, mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite (wz a Ha). intros Hin. exact (Hna (Hw a Hin)).
Qed.
Lemma decL_agree_trans : forall (H : word -> bool) m1 m2 m3 lo hi,
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview tfibsegs H m2 a = aview tfibsegs H m1 a) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview tfibsegs H m3 a = aview tfibsegs H m2 a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview tfibsegs H m3 a = aview tfibsegs H m1 a.
Proof. intros H m1 m2 m3 lo hi H1 H2 a Ha Hna. rewrite (H2 a Ha Hna). exact (H1 a Ha Hna). Qed.
Definition decL_wchk (r : YP09.region) : bool :=
  match YP09.r_base r with
  | Some 2%nat => (YP09.r_wlo r =? 0) && (YP09.r_whi r =? 128)
  | _ => YP09.r_whi r <=? YP09.r_wlo r
  end.
Lemma decL_inw : forall Ex rs x b, forallb decL_wchk rs = true -> bv_unsigned (ew Ex 2) = b ->
  in_wrange Ex rs x -> b <= x < b + 128.
Proof.
intros Ex rs x b Hc Hb (r & Hin & Hx). pose proof (proj1 (forallb_forall _ _) Hc r Hin) as Hr.
unfold decL_wchk in Hr. destruct (YP09.r_base r) as [[|[|[|n]]]|] eqn:Eb;
  try (apply Z.leb_le in Hr; lia).
apply andb_prop in Hr as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2.
cbn [base_val] in Hx. try rewrite Eb in Hx. cbn [base_val] in Hx. rewrite Hb, H1, H2 in Hx. lia.
Qed.

Ltac decL_awr dd E2 Hspot HSTK :=
  cbn [add_cond ss_mem]; try (cbv [decL_hss fss_retT fsT_ret_regions app ss_mem]);
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := d_sp dd - DEC_F - d_ot dd);
  [ reflexivity
  | rewrite ?ew_ewset_other by lia; rewrite E2; lia
  | cbn; unfold d_STKJ, DEC_F in *; lia | cbn; unfold DEC_F in *; lia | ];
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
Ltac decL_agree E2 lo hi :=
  repeat match goal with
  | HF : frame_of ?Ex ?rs (mrestrict ?H ?m1) (mrestrict ?H ?m2) |- _ =>
      let A := fresh "AG" in
      assert (A : forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview tfibsegs H m2 a = aview tfibsegs H m1 a);
      [ apply (decL_fr_agree Ex rs H m1 m2 lo hi HF);
        let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
        let Hw := fresh "Hw" in
        assert (Hw : lo <= x < lo + 128)
          by (apply (decL_inw Ex rs x lo); [vm_compute; reflexivity | rewrite ?ew_ewset_other by lia; rewrite E2; reflexivity
              | exact Hx]);
        unfold DEC_F in *; lia
      | clear HF ]
  end;
  repeat match goal with
  | A1 : forall a, _ -> _ -> aview tfibsegs ?H ?m2 a = aview tfibsegs ?H ?m1 a,
    A2 : forall a, _ -> _ -> aview tfibsegs ?H ?m3 a = aview tfibsegs ?H ?m2 a |- _ =>
      let A := fresh "AG" in pose proof (decL_agree_trans H m1 m2 m3 lo hi A1 A2) as A; clear A1 A2
  end.
Ltac decL_rkeep E HSF n r Rn :=
  eapply (decL_reg _ _ _ _ r (SOff n 0));
  [ exact HSF | vm_compute; reflexivity
  | rewrite fsw_SOff0, ?ew_ewset_other by lia; unfold E; rewrite (decL_E_reg _ _ _ _ n r eq_refl); exact Rn ].
Ltac decL_rplus E HSF n z r Rn :=
  eapply (decL_reg _ _ _ _ r (SOff n z));
  [ exact HSF | vm_compute; reflexivity
  | apply decL_soff;
    [ rewrite ?ew_ewset_other by lia; unfold E; rewrite (decL_E_reg _ _ _ _ n r eq_refl); exact Rn | lia | lia ] ].

Definition decL_kept_regs : list (bv 5) := [2; 3; 4; 8; 9; 19; 20; 26; 27]%bv.
Lemma decL_next : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs0 Ex SS ms md' six' pad' acc' ex,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  (forall six' pad' acc' Wc' lyc' Sc' Uc' regsc' memc' mdc' k',
     dec_head B d q (S i) six' pad' acc' Wc' lyc' Sc' Uc' regsc' memc' mdc' k' ->
     SRr tfibsegs Wc' (decL_hcfg regsc' memc' mdc') (dec_post B d)) ->
  (forall r, In r decL_kept_regs -> getr regs0 r = getr regsc r) ->
  st_ok tfibsegs Ex SS (restrict (w_H Wc) ms) -> ss_resv SS = None -> ss_pc SS = DEC_HEAD ->
  nth_error (ss_mem SS) 0 = Some (fstk_ret DEC_F decL_cs) ->
  (forall n, (n < 48)%nat -> ew Ex n = ew (decL_E d q regs0 ex) n) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs SS) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) decL_kept_regs = true ->
  dec_J B d lyc Sc Wc Uc (ms_mem ms) md' k -> ARU tfibsegs B lyc Sc Uc Wc (ms_mem ms) md' ->
  decL_memf d q six' Wc lyc Sc (ms_mem ms) ->
  getr (ms_regs ms) 18 = w64 (d_text d + Z.of_nat (S i)) ->
  getr (ms_regs ms) 25 = w64 (d_text d + Z.of_nat (S i) - 1) ->
  getr (ms_regs ms) 21 = w64 (Z.of_nat (length (WriterSpec.six_bytes six'))) ->
  getr (ms_regs ms) 22 = w64 acc' -> 0 <= acc' < 2 ^ 64 ->
  getr (ms_regs ms) 23 = w64 (6 * Z.of_nat (length six') mod 8) -> getr (ms_regs ms) 24 = w64 pad' ->
  (S i <= length (d_tb d))%nat -> 0 <= pad' <= Z.of_nat (S i) -> (length six' <= S i)%nat ->
  Forall (fun x => 0 <= x < 64) six' -> acc' mod 64 = last six' 0 ->
  WriterSpec.b64_dec (d_tb d) = decLA_out pad' six' (skipn (S i) (d_tb d)) ->
  SRr tfibsegs Wc (mkCfg ms md') (dec_post B d).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs0 Ex SS ms md' six' pad' acc' ex HE HH HIH RK0 HS Hrv Hpc
  Hnth HEx Hkept HJ' HARU' HM' R18' R25' R21' R22' Hacc' R23' R24' Hi' Hpad' Hsix' Hsix64' Hlast' Hscan'.
pose proof (decL_lenp_range d HE) as (L1 & L2 & _).
pose proof (decLB_q d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH) as (_ & Q1 & Q2 & _).
pose proof asan_consts as (C1 & _).
pose proof HH as HH0. decL_unhead HH.
assert (KR : forall r : bv 5, In r decL_kept_regs -> getr (ms_regs ms) r = getr regsc r).
{ intros r Hr. pose proof (proj1 (forallb_forall _ _) Hkept r Hr) as Hqq. apply sv_eqb_eq in Hqq.
  rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) Ex SS ms r HS), Hqq, fsw_SOff0.
  rewrite HEx by (cbv [decL_kept_regs In] in Hr;
    repeat (destruct Hr as [<-|Hr]; [vm_compute; lia|]); destruct Hr).
  unfold decL_E. rewrite <- (RK0 r Hr). apply ew_Ereg_nat. pose proof (u5_range r). rewrite Z2Nat.id by lia. reflexivity. }
assert (E2 : bv_unsigned (ew Ex 2) = d_sp d - DEC_F).
{ rewrite (HEx 2%nat ltac:(lia)). unfold decL_E. rewrite (ew_Ereg_nat regs0 _ 2 2%bv eq_refl).
  rewrite (RK0 2%bv ltac:(cbv; tauto)). exact Hsp. }
destruct (decL_frame_back d q regs0 ex Wc ms Ex SS HS Hnth E2
  ltac:(intros n Hn; apply HEx; lia) ltac:(lia) ltac:(pose proof (decL_dn_pos d); unfold HEAD in *; lia))
  as (HFr' & HLs' & HNq').
rewrite (st_ok_restrict_mkst tfibsegs (w_H Wc) Ex SS ms HS Hrv), Hpc.
apply (HIH six' pad' acc' Wc lyc Sc Uc (ms_regs ms) (ms_mem ms) md' k).
apply (decL_mk_head d q i six pad acc Wc lyc Sc Uc regsc memc mdc k (S i) six' pad' acc' (ms_regs ms) (ms_mem ms) md'
  HH0 HJ' HARU' HM' HFr' HLs' HNq').
- unfold spZ. rewrite (KR 2%bv ltac:(cbv; tauto)). exact Hsp.
- rewrite (KR 3%bv ltac:(cbv; tauto)). exact R3.
- rewrite (KR 4%bv ltac:(cbv; tauto)). exact R4.
- rewrite (KR 8%bv ltac:(cbv; tauto)). exact R8.
- rewrite (KR 9%bv ltac:(cbv; tauto)). exact R9.
- exact R18'.
- rewrite (KR 19%bv ltac:(cbv; tauto)). exact R19.
- rewrite (KR 20%bv ltac:(cbv; tauto)). exact R20.
- exact R21'.
- exact R22'.
- exact Hacc'.
- exact R23'.
- exact R24'.
- exact R25'.
- rewrite (KR 26%bv ltac:(cbv; tauto)). exact R26.
- rewrite (KR 27%bv ltac:(cbv; tauto)). exact R27.
- exact Hi'.
- exact Hpad'.
- exact Hsix'.
- exact Hsix64'.
- exact Hlast'.
- exact Hscan'.
Qed.

Lemma decL_arm_skip : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  (forall six' pad' acc' Wc' lyc' Sc' Uc' regsc' memc' mdc' k',
     dec_head B d q (S i) six' pad' acc' Wc' lyc' Sc' Uc' regsc' memc' mdc' k' ->
     SRr tfibsegs Wc' (decL_hcfg regsc' memc' mdc') (dec_post B d)) ->
  (i < length (d_tb d))%nat ->
  WriterSpec.b64_ws (nth i (d_tb d) 0) = true \/ nth i (d_tb d) 0 = 61 ->
  SRr tfibsegs Wc (decL_hcfg regsc memc mdc) (dec_post B d).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH HIH Hlt Hcase.
destruct (decL_head_st d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH) as [HS SHOK].
pose proof HH as HH0. decL_unhead HH. unfold dec_J in HJ.
assert (HSTK : 128 <= STK_preset_base64_decode) by (vm_compute; discriminate).
pose proof (decLB_sp d HE) as (SP1 & Hspot & SP3).
pose proof (decLB_text d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH0) as (T1 & T2 & _).
pose proof asan_consts as (C1 & _ & _ & _).
assert (Hc : nth i (d_tb d ++ [0]) 0 = nth i (d_tb d) 0) by (rewrite app_nth1 by exact Hlt; reflexivity).
set (c := nth i (d_tb d ++ [0]) 0) in *.
assert (Hc61 : c <= 61).
{ rewrite Hc. destruct Hcase as [Hw | ->]; [|lia].
  destruct (decLA_ws_vals _ Hw) as [ -> | [ -> | [ -> | -> ]]]; lia. }
set (E := decL_E d q regsc [Z_to_bv 64 c]) in *.
assert (E48 : ew E 48 = Z_to_bv 64 c) by (unfold E; exact (decL_E_ex d q regsc _ 0)).
assert (E26 : ew E 26 = Z_to_bv 64 61) by (unfold E; rewrite (decL_E_reg d q regsc _ 26 26%bv eq_refl), R26; reflexivity).
assert (E27 : ew E 27 = Z_to_bv 64 DEC_WSMASK)
  by (unfold E; rewrite (decL_E_reg d q regsc _ 27 27%bv eq_refl), R27; reflexivity).
pose proof (decL_text_byte d Wc memc i (proj1 (proj2 (proj2 HKe))) Hi) as (_ & Rc). fold c in Rc.
assert (E2 : bv_unsigned (ew E 2) = d_sp d - DEC_F)
  by (unfold E; rewrite (decL_E_reg d q regsc _ 2 2%bv eq_refl); exact Hsp).
assert (Hlo : alloc_ceiling <= d_sp d - DEC_F) by (unfold DEC_F; lia).
assert (HM0 : decL_memf d q six Wc lyc Sc memc) by exact (decLB_memf d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HH0).
pose proof HE as (_ & _ & _ & _ & _ & _ & _ & _ & Htb & _).
assert (Hscan0 : WriterSpec.b64_dec (d_tb d) = decLA_out pad six (nth i (d_tb d) 0 :: skipn (S i) (d_tb d)))
  by (rewrite <- (decLA_skipn (d_tb d) i Hlt); exact Hscan).
unfold decL_hcfg.
fsw_aj_run_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan.
{ decL_awr d E2 Hspot HSTK. }
(* 0x84d0c: bltu s10, c -- not taken, c <= 61 *)
eapply SRr_sym_branch with (c := BC_LTU) (a := SOff 26 0) (b := SOff 48 0); [exact HS | intros Hb0 _ | intros Hb0 HS2].
{ exfalso. rewrite (decLA_br_ltu _ 26 48 61 c) in Hb0;
    [apply Z.ltb_lt in Hb0; lia | rewrite ?ew_ewset_other by lia; exact E26
    | rewrite ?ew_ewset_other by lia; exact E48 | lia | lia]. }
clear HS Hb0.
fsw_aj_run_tokU fsw_wr_tbl_ok HS2 HJ HARU SHOK fs_Bspan.
{ decL_awr d E2 Hspot HSTK. }
(* 0x84d18: beqz ((mask >> c) & 1), taken iff c is no whitespace *)
eapply SRr_sym_branch with (c := BC_EQ) (a := SAlu ALU_AND (SAlu ALU_SRL (SOff 27 0) (SOff 48 0)) (SLit 1)) (b := SLit 0);
  [exact HS2 | intros Hb HS3 | intros Hb HS3];
  rewrite (decLA_br_ws_eq _ 27 48 c) in Hb by (rewrite ?ew_ewset_other by lia; first [exact E27 | exact E48 | lia]);
  clear HS2.
- (* not whitespace: c = 61 *)
  assert (Hc61' : c = 61).
  { destruct Hcase as [Hw | H61]; [rewrite <- Hc in Hw; rewrite Hw in Hb; discriminate Hb | rewrite Hc; exact H61]. }
  fsw_aj_run_tokU fsw_wr_tbl_ok HS3 HJ HARU SHOK fs_Bspan.
  { decL_awr d E2 Hspot HSTK. }
  eapply SRr_sym_branch with (c := BC_NE) (a := SOff 48 0) (b := SOff 26 0); [exact HS3 | intros Hb2 _ | intros Hb2 HS4].
  { exfalso. rewrite (decLA_br_ne _ 48 26 c 61) in Hb2
      by (rewrite ?ew_ewset_other by lia; first [exact E48 | exact E26 | lia]).
    rewrite Hc61', Z.eqb_refl in Hb2. discriminate Hb2. }
  clear HS3.
  fsw_aj_run_to_tokU fsw_wr_tbl_ok HS4 HJ HARU SHOK fs_Bspan DEC_HEAD.
  { decL_awr d E2 Hspot HSTK. }
  decL_agree E2 (d_sp d - DEC_F) (d_sp d).
  match goal with AG : forall a, _ -> _ -> aview _ _ ?mF a = aview _ _ memc a |- _ =>
    pose proof (decLB_keep d q i six pad acc Wc lyc Sc Uc regsc memc mdc k memc mF (d_sp d - DEC_F) (d_sp d) HE HH0 HM0
      Hlo ltac:(lia) AG) as HMF end.
  eapply (decL_next d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regsc _ _ _ _ six (pad + 1) acc [Z_to_bv 64 c]
    HE HH0 HIH (fun r _ => eq_refl) HS4);
    [ reflexivity | reflexivity | vm_compute; reflexivity
    | intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity | vm_compute; reflexivity
    | exact HJ | exact HARU | exact HMF | .. ].
  + rewrite Nat2Z.inj_succ, Z.add_succ_r, <- Z.add_1_r. decL_rplus E HS4 18%nat 1 (18%bv : bv 5) R18.
  + replace (d_text d + Z.of_nat (S i) - 1) with (d_text d + Z.of_nat i - 1 + 1) by lia.
    decL_rplus E HS4 25%nat 1 (25%bv : bv 5) R25.
  + decL_rkeep E HS4 21%nat (21%bv : bv 5) R21.
  + decL_rkeep E HS4 22%nat (22%bv : bv 5) R22.
  + exact Hacc.
  + decL_rkeep E HS4 23%nat (23%bv : bv 5) R23.
  + decL_rplus E HS4 24%nat 1 (24%bv : bv 5) R24.
  + lia.
  + lia.
  + lia.
  + exact Hsix64.
  + exact Hlast.
  + rewrite Hscan0. rewrite <- Hc, Hc61'. apply decLA_out_61.
- (* whitespace: the next byte *)
  apply Bool.negb_false_iff in Hb.
  fsw_aj_run_to_tokU fsw_wr_tbl_ok HS3 HJ HARU SHOK fs_Bspan DEC_HEAD.
  { decL_awr d E2 Hspot HSTK. }
  decL_agree E2 (d_sp d - DEC_F) (d_sp d).
  match goal with AG : forall a, _ -> _ -> aview _ _ ?mF a = aview _ _ memc a |- _ =>
    pose proof (decLB_keep d q i six pad acc Wc lyc Sc Uc regsc memc mdc k memc mF (d_sp d - DEC_F) (d_sp d) HE HH0 HM0
      Hlo ltac:(lia) AG) as HMF end.
  eapply (decL_next d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regsc _ _ _ _ six pad acc [Z_to_bv 64 c]
    HE HH0 HIH (fun r _ => eq_refl) HS3);
    [ reflexivity | reflexivity | vm_compute; reflexivity
    | intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity | vm_compute; reflexivity
    | exact HJ | exact HARU | exact HMF | .. ].
  + rewrite Nat2Z.inj_succ, Z.add_succ_r, <- Z.add_1_r. decL_rplus E HS3 18%nat 1 (18%bv : bv 5) R18.
  + replace (d_text d + Z.of_nat (S i) - 1) with (d_text d + Z.of_nat i - 1 + 1) by lia.
    decL_rplus E HS3 25%nat 1 (25%bv : bv 5) R25.
  + decL_rkeep E HS3 21%nat (21%bv : bv 5) R21.
  + decL_rkeep E HS3 22%nat (22%bv : bv 5) R22.
  + exact Hacc.
  + decL_rkeep E HS3 23%nat (23%bv : bv 5) R23.
  + decL_rkeep E HS3 24%nat (24%bv : bv 5) R24.
  + lia.
  + lia.
  + lia.
  + exact Hsix64.
  + exact Hlast.
  + rewrite Hscan0. rewrite <- Hc. apply decLA_out_ws. exact Hb.
Qed.

(* ---- the memchr arm (port of lib/A/FSW_dec_L4.v) ---- *)
(* at PC_memchr: ra = 0x84d50, a0 = s3, a1 = c, a2 = 65 *)
Definition decLO_cregs : list sv :=
  [SLit 0; SLit 544080; SOff 2 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 7 0; SOff 8 0; SOff 9 0;
   SOff 19 0; SOff 48 0; SLit 65; SOff 13 0; SOff 14 0; SOff 15 0; SOff 16 0; SOff 17 0;
   SOff 18 0; SOff 19 0; SOff 20 0; SOff 21 0; SOff 22 0; SOff 23 0; SOff 24 0; SOff 25 0; SOff 26 0; SOff 27 0;
   SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
Definition decLO_str2 : YP09.region :=
  YP09.mkRegion (Some 48%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SAluw ALU_SRL decLO_acc_e (SOff 23 (-2))))].
Ltac decLO_cs := unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?q] =>
    let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end; lia.

Lemma decLO_byteW : forall w : word, bv_unsigned (byte_of_word w 0) = bv_unsigned w mod 256.
Proof.
  intros w. unfold byte_of_word. rewrite Z.mul_0_r, Z.shiftr_0_r, Z_to_bv_unsigned.
  unfold bv_wrap. reflexivity.
Qed.
Lemma decLO_cbyte0 : forall E a e, YP09.cbyte tfibsegs E a (CVal 1 e) 0 = Some (byte_of_word (sv_denot E e) 0).
Proof. reflexivity. Qed.
Lemma decLO_str2_aview : forall E (H : word -> bool) (m : word -> option byte),
  region_ok tfibsegs E (mrestrict H m) decLO_str2 ->
  aview tfibsegs H m (bv_unsigned (ew E 48))
    = Some (U E (SAluw ALU_SRL decLO_acc_e (SOff 23 (-2))) mod 256).
Proof.
  intros E H m (_ & _ & _ & HC).
  cbv [decLO_str2 YP09.r_chunks YP09.r_base base_val] in HC.
  pose proof (Forall_inv HC) as Hck.
  destruct (Hck 0 ltac:(cbn; lia)) as (bb & Hcb & Hmb).
  cbv [YP09.c_off YP09.c_val] in Hcb, Hmb.
  rewrite !Z.add_0_r in Hmb.
  unfold aview. rewrite Hmb. cbv [option_map]. f_equal.
  rewrite decLO_cbyte0 in Hcb. injection Hcb as <-.
  rewrite decLO_byteW. reflexivity.
Qed.
Lemma decLO_mchr : forall c, 0 <= c < 256 -> 1 <= mchr_len c WriterSpec.b64_table <= 65.
Proof.
  intros c Hc.
  pose proof (decLA_fin (fun c => (1 <=? mchr_len c WriterSpec.b64_table) && (mchr_len c WriterSpec.b64_table <=? 65))
    0 256 ltac:(vm_compute; reflexivity) c ltac:(lia)) as A.
  cbv beta in A. apply andb_prop in A as [A1 A2]. apply Z.leb_le in A1, A2. lia.
Qed.
Lemma decLO_hull_sub : forall rd x n m, 1 <= m <= n -> shadow_hull_vis rd x n -> shadow_hull_vis rd x m.
Proof.
  intros rd x n m Hm H s Hs. apply H. unfold shadow_addr in *.
  assert (A1 : (x + m - 1) / 8 <= (x + n - 1) / 8) by (apply Z.div_le_mono; lia).
  assert (A2 : (SHADOW_OFF + (x + m - 1) / 8) / 8 <= (SHADOW_OFF + (x + n - 1) / 8) / 8) by (apply Z.div_le_mono; lia).
  lia.
Qed.
Lemma decLO_awr_h : forall Ex d rs FP bl0 blc ly own fr0,
  bv_unsigned (ew Ex 2) = d_sp d - DEC_F -> d_sp d <= d_ot d ->
  rs = fsT_ret_regions DEC_F decL_cs [decL_txr] ->
  awr_ok tfibsegs B Ex rs (d_STKJ d) (d_ot d) FP bl0 blc ly own fr0.
Proof.
  intros Ex d rs FP bl0 blc ly own fr0 E2 Hot ->.
  assert (FS : STK_preset_base64_decode = ltac:(let v := eval vm_compute in STK_preset_base64_decode in exact v)) by reflexivity.
  unfold fsT_ret_regions. cbn [app].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := d_sp d - DEC_F - d_ot d);
    [reflexivity | rewrite E2; lia | cbv [fstk_ret YP09.r_wlo]; unfold d_STKJ, DEC_F; rewrite FS; lia
    | cbv [fstk_ret YP09.r_whi]; unfold DEC_F; lia |].
  apply awr_ok_cons_ro; [cbv [fs_got_region YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_cons_ro; [cbv [fs_bcell_region YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_cons_ro; [cbv [decL_txr YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_nil.
Qed.
Lemma decLO_awr_m : forall Ex d rs p FP bl0 blc ly own fr0,
  bv_unsigned (ew Ex 2) = d_sp d - DEC_F -> bv_unsigned (ew Ex 48) = p -> d_sp d <= d_ot d ->
  in_tmp_block bl0 blc p ->
  rs = fsT_ret_regions DEC_F decL_cs [decL_str] ->
  awr_ok tfibsegs B Ex rs (d_STKJ d) (d_ot d) FP bl0 blc ly own fr0.
Proof.
  intros Ex d rs p FP bl0 blc ly own fr0 E2 E48 Hot Htmp ->.
  assert (FS : STK_preset_base64_decode = ltac:(let v := eval vm_compute in STK_preset_base64_decode in exact v)) by reflexivity.
  unfold fsT_ret_regions. cbn [app].
  eapply awr_ok_cons_stack_off with (n := 2%nat) (d := d_sp d - DEC_F - d_ot d);
    [reflexivity | rewrite E2; lia | cbv [fstk_ret YP09.r_wlo]; unfold d_STKJ, DEC_F; rewrite FS; lia
    | cbv [fstk_ret YP09.r_whi]; unfold DEC_F; lia |].
  apply awr_ok_cons_ro; [cbv [fs_got_region YP09.r_wlo YP09.r_whi]; lia|].
  apply awr_ok_cons_ro; [cbv [fs_bcell_region YP09.r_wlo YP09.r_whi]; lia|].
  eapply awr_ok_cons_gen with (k := 48%nat) (b := p); [reflexivity | exact E48 | | apply awr_ok_nil].
  intros a Ha. cbv [decL_str YP09.r_wlo YP09.r_whi] in Ha. replace a with p by lia.
  left. right. right. left. exact Htmp.
Qed.
Lemma decLO_meq_h : forall Ex d rs (m0 m1 m2 : word -> option byte),
  frame_of Ex rs m1 m2 -> bv_unsigned (ew Ex 2) = d_sp d - DEC_F ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp d - DEC_F <= a < d_sp d) -> m1 (Z_to_bv 64 a) = m0 (Z_to_bv 64 a)) ->
  rs = fsT_ret_regions DEC_F decL_cs [decL_txr] ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp d - DEC_F <= a < d_sp d) -> m2 (Z_to_bv 64 a) = m0 (Z_to_bv 64 a)).
Proof.
  intros Ex d rs m0 m1 m2 HF E2 M01 -> a Ha Hn. rewrite <- (M01 a Ha Hn). apply HF. rewrite (wz a Ha).
  intros (r & Hin & Hr). cbv [fsT_ret_regions app In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
    cbv [fstk_ret fs_got_region fs_bcell_region decL_txr YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    try rewrite E2 in Hr; unfold DEC_F in *; lia.
Qed.
Lemma decLO_meq_m : forall Ex d rs p (m0 m1 m2 : word -> option byte),
  bv_unsigned (ew Ex 2) = d_sp d - DEC_F -> bv_unsigned (ew Ex 48) = p -> frame_of Ex rs m1 m2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp d - DEC_F <= a < d_sp d) -> a <> p ->
     m1 (Z_to_bv 64 a) = m0 (Z_to_bv 64 a)) ->
  rs = fsT_ret_regions DEC_F decL_cs [decL_str] ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp d - DEC_F <= a < d_sp d) -> a <> p ->
     m2 (Z_to_bv 64 a) = m0 (Z_to_bv 64 a)).
Proof.
  intros Ex d rs p m0 m1 m2 E2 E48 HF M01 -> a Ha Hn Hp. rewrite <- (M01 a Ha Hn Hp). apply HF. rewrite (wz a Ha).
  intros (r & Hin & Hr). cbv [fsT_ret_regions app In] in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
    cbv [fstk_ret fs_got_region fs_bcell_region decL_str YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    try rewrite E2 in Hr; try rewrite E48 in Hr; unfold DEC_F in *; lia.
Qed.
Lemma decLO_add_atom : forall E ss ms n f, st_ok tfibsegs E ss ms -> afact_ok E n f ->
  st_ok tfibsegs E (set_facts ss (mkFacts ((n, f) :: f_atoms (ss_facts ss)) (f_conds (ss_facts ss))
    (f_alias (ss_facts ss)))) ms.
Proof.
  intros E ss ms n f HS Hf. apply st_ok_set_facts; [exact HS|].
  apply facts_ok_add_atom; [exact (st_ok_facts_ok tfibsegs E ss ms HS) | exact Hf].
Qed.
Lemma decLO_c : forall d i, dec_entry_ok B d -> (i < length (d_tb d))%nat -> 1 <= nth i (d_tb d) 0 <= 255.
Proof.
  intros d i HE Hi.
  pose proof HE as (_ & _ & _ & _ & _ & ((_ & HNZ) & _) & _ & HBO & _).
  assert (Hin : In (nth i (d_tb d) 0) (d_tb d)) by (apply nth_In; exact Hi).
  rewrite Forall_forall in HNZ. unfold WriterSpec.bytes_ok in HBO. rewrite Forall_forall in HBO.
  pose proof (HNZ _ Hin). pose proof (HBO _ Hin). lia.
Qed.
Lemma decLO_bits : forall L, 0 <= L -> 0 <= 6 * L mod 8 <= 6 /\ (6 * L mod 8) mod 2 = 0.
Proof. intros L HL. destruct (decLA_bits_cases L HL) as [E|[E|[E|E]]]; rewrite E; split; first [lia | reflexivity]. Qed.

(* the call of fuzz_free on a refused text, from the engine's state at A_fuzz_free after memchr *)
Lemma decLO_free : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 Ex ss ms md',
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  (forall W3 ly3 S3 U3 regs3 mem3 md3 k3, dec_at_free B d q W3 ly3 S3 U3 regs3 mem3 md3 k3 ->
     SRr tfibsegs W3 (cfg_at tfibsegs A_fuzz_free regs3 mem3 md3) (dec_post B d)) ->
  decL_memf d q six Wc lyc Sc mem2 ->
  (forall r, In r decLO_kregs -> getr regs2 r = getr regsc r) ->
  st_ok tfibsegs Ex ss (restrict (w_H Wc) ms) ->
  (forall n, (n < 49)%nat ->
     ew Ex n = ew (decL_E d q regs2 [Z_to_bv 64 (q + Z.of_nat (length (WriterSpec.six_bytes six)))]) n) ->
  ss_pc ss = A_fuzz_free -> ss_resv ss = None ->
  sr_get (ss_regs ss) 10 = SOff 9 0 -> sr_get (ss_regs ss) 1 = SLit DEC_RA_FREE ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) [2; 3; 4; 8]%bv = true ->
  nth_error (ss_mem ss) 0 = Some (fstk_ret DEC_F decL_cs) ->
  dec_J B d lyc Sc Wc Uc (ms_mem ms) md' k -> ARU tfibsegs B lyc Sc Uc Wc (ms_mem ms) md' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp d - DEC_F <= a < d_sp d) ->
     a <> q + Z.of_nat (length (WriterSpec.six_bytes six)) -> ms_mem ms (Z_to_bv 64 a) = mem2 (Z_to_bv 64 a)) ->
  WriterSpec.b64_dec (d_tb d) = None ->
  SRr tfibsegs Wc (mkCfg ms md') (dec_post B d).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 Ex ss ms md' HE HH HFREE HM2 RK HS HEx Hpc Hrv
  S10 S1 Hk4 Hnth HJ3 HARU3 MEQ Hdec.
pose proof HH as HH0. decL_unhead HH.
pose proof asan_consts as (C1 & _).
pose proof (decL_lenp_range d HE) as (L1 & L2 & _).
pose proof (decLB_q d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH0) as (Q16 & Q1 & Q2 & Qn & _).
pose proof (decL_dn_pos d) as Hdn.
pose proof (decLB_sp d HE) as (SP1 & SP2 & SP3).
assert (Hnb : Z.of_nat (length (WriterSpec.six_bytes six)) < d_n d) by (unfold d_n; apply decLA_nbytes; lia).
assert (EK : forall (m : nat) (r : bv 5), (m < 49)%nat -> Z.of_nat m = bv_unsigned r -> In r decLO_kregs ->
  ew Ex m = getr regsc r)
  by (intros m r Hm Hr Hkin; rewrite (HEx m Hm), (decL_E_reg d q regs2 _ m r Hr); exact (RK r Hkin)).
assert (GK : forall (r : bv 5) (m : nat), In r [2; 3; 4; 8]%bv -> (m < 49)%nat -> Z.of_nat m = bv_unsigned r ->
  In r decLO_kregs -> getr (ms_regs ms) r = getr regsc r).
{ intros r m Hin Hm Hr Hkin. pose proof (proj1 (forallb_forall _ _) Hk4 r Hin) as Hqq. apply sv_eqb_eq in Hqq.
  rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) Ex ss ms r HS), Hqq, fsw_SOff0.
  replace (Z.to_nat (bv_unsigned r)) with m by lia. exact (EK m r Hm Hr Hkin). }
assert (E2 : bv_unsigned (ew Ex 2) = d_sp d - DEC_F) by (rewrite (EK 2%nat 2%bv ltac:(lia) eq_refl ltac:(decLO_in)); exact Hsp).
destruct (decL_frame_back d q regs2 [Z_to_bv 64 (q + Z.of_nat (length (WriterSpec.six_bytes six)))] Wc ms Ex ss HS
  Hnth E2 (fun m Hm => HEx m ltac:(lia)) ltac:(lia) ltac:(unfold HEAD in *; lia)) as (HFr3 & HLs3 & _).
apply (decL_free d q i six pad acc Wc lyc Sc Uc regsc memc mdc k Ex ss ms md' HH0 HFREE HS Hrv Hpc HJ3 HARU3).
- apply (decLB_tr d q i six pad acc Wc lyc Sc Uc regsc memc mdc k mem2 (ms_mem ms) HE HH0 HM2).
  intros a Ha H1 H2. apply aview_at. apply MEQ; [exact Ha | unfold DEC_F in *; lia | lia].
- exact HFr3.
- exact HLs3.
- apply (decL_reg (w_H Wc) Ex ss ms 10%bv (SOff 9 0)); [exact HS | exact S10 |].
  rewrite fsw_SOff0, (EK 9%nat 9%bv ltac:(lia) eq_refl ltac:(decLO_in)). exact R9.
- exact (fsw_reg_lit (w_H Wc) Ex ss ms 1%bv DEC_RA_FREE HS S1 ltac:(unfold DEC_RA_FREE; lia)).
- unfold spZ. rewrite (GK 2%bv 2%nat ltac:(cbv; tauto) ltac:(lia) eq_refl ltac:(decLO_in)). exact Hsp.
- rewrite (GK 3%bv 3%nat ltac:(cbv; tauto) ltac:(lia) eq_refl ltac:(decLO_in)). exact R3.
- rewrite (GK 4%bv 4%nat ltac:(cbv; tauto) ltac:(lia) eq_refl ltac:(decLO_in)). exact R4.
- rewrite (GK 8%bv 8%nat ltac:(cbv; tauto) ltac:(lia) eq_refl ltac:(decLO_in)). exact R8.
- exact Hdec.
Qed.

Lemma decLO_hd : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k,
  dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  spZ regsc = d_sp d - DEC_F /\ (length six <= i)%nat /\ 0 <= pad <= Z.of_nat i /\
  getr regsc 23 = w64 (6 * Z.of_nat (length six) mod 8) /\ getr regsc 24 = w64 pad /\ getr regsc 20 = w64 SHADOW_OFF /\
  WriterSpec.b64_dec (d_tb d) = decLA_out pad six (skipn i (d_tb d)).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HH. decL_unhead HH.
exact (conj Hsp (conj Hsix (conj Hpad (conj R23 (conj R24 (conj R20 Hscan)))))).
Qed.

Lemma decLO_mfacts : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  (i < length (d_tb d))%nat -> (forall r, In r decLO_kregs -> getr regs2 r = getr regsc r) ->
  bv_unsigned (ew (decL_E d q regs2 [Z_to_bv 64 (q + Z.of_nat (length (WriterSpec.six_bytes six)))]) 2) = d_sp d - DEC_F /\
  bv_unsigned (ew (decL_E d q regs2 [Z_to_bv 64 (q + Z.of_nat (length (WriterSpec.six_bytes six)))]) 48) =
    q + Z.of_nat (length (WriterSpec.six_bytes six)) /\
  d_sp d <= d_ot d /\
  in_tmp_block (ablocks B (d_ly d) (d_S d)) (ablocks B lyc Sc) (q + Z.of_nat (length (WriterSpec.six_bytes six))) /\
  Z.of_nat (length (WriterSpec.six_bytes six)) < d_n d /\
  WriterSpec.b64_dec (d_tb d) = decLA_out pad six (nth i (d_tb d) 0 :: skipn (S i) (d_tb d)).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 HE HH Hilt RK.
pose proof asan_consts as ((C1 & C2) & _).
pose proof (decLB_q d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH) as (_ & Q1 & Q2 & _ & _ & _ & Qa).
unfold HEAD in Q1.
pose proof (decLB_sp d HE) as (_ & SP2 & _).
destruct (decLO_hd d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HH) as (Hsp & Hsix & _ & _ & _ & _ & Hscan).
assert (Hnb : Z.of_nat (length (WriterSpec.six_bytes six)) < d_n d)
  by (unfold d_n; apply decLA_nbytes; lia).
assert (E48 : ew (decL_E d q regs2 [Z_to_bv 64 (q + Z.of_nat (length (WriterSpec.six_bytes six)))]) 48 =
  Z_to_bv 64 (q + Z.of_nat (length (WriterSpec.six_bytes six)))) by exact (decL_E_ex d q regs2 _ 0).
destruct (Qa (q + Z.of_nat (length (WriterSpec.six_bytes six))) ltac:(lia)) as (_ & Htmp & _ & _).
split; [rewrite (decL_E_reg d q regs2 _ 2 2%bv eq_refl), (RK 2%bv ltac:(decLO_in)); exact Hsp|].
split; [rewrite E48; apply wz; lia|].
split; [exact SP2|]. split; [exact Htmp|]. split; [exact Hnb|].
rewrite <- (decLA_skipn (d_tb d) i Hilt). exact Hscan.
Qed.

Lemma decLO_str_ok : forall (E : env) (H : word -> bool) (m : word -> option byte) p,
  bv_unsigned (ew E 48) = p -> 0 <= p -> p + 1 <= 2 ^ 64 -> writable_at tfibsegs (mrestrict H m) p ->
  Forall (region_ok tfibsegs E (mrestrict H m)) [decL_str].
Proof.
intros E H m p E48 H0 H1 Hw. constructor; [|constructor].
unfold decL_str, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite E48. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. replace (p + o) with p by lia. exact Hw.
Qed.
Lemma decLO_mpd : forall (E : env) b p,
  bv_unsigned (ew E 2) = b -> bv_unsigned (ew E 48) = p -> p + 1 <= b -> alloc_ceiling <= b ->
  (p + 1 <= tfib_D_GOT_asan_shadow_memory_dynamic_address \/ tfib_D_GOT_asan_shadow_memory_dynamic_address + 8 <= p) ->
  (p + 1 <= tfib_D_asan_shadow_memory_dynamic_address \/ tfib_D_asan_shadow_memory_dynamic_address + 8 <= p) ->
  pairwise_disjoint E (fsT_ret_regions DEC_F decL_cs [decL_str]).
Proof.
intros E b p E2 E48 Hpb Hb G1 G2. pose proof asan_consts as ((C1 & _) & _).
apply pairwise_disjoint_of_extents.
unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, decL_str, extent_of_region.
cbn [map app YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, E48.
unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, DEC_F in *.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Lemma decLO_mss_ok : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 md2,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  (i < length (d_tb d))%nat ->
  dec_J B d lyc Sc Wc Uc mem2 md2 k -> ARU tfibsegs B lyc Sc Uc Wc mem2 md2 ->
  dec_frame_ok Wc mem2 (d_sp d - DEC_F) (d_regs d) -> dec_lenp_slot Wc mem2 (d_sp d - DEC_F) (d_lenp d) ->
  dec_nq_slot Wc mem2 (d_sp d - DEC_F) q ->
  (forall r, In r decLO_kregs -> getr regs2 r = getr regsc r) ->
  st_ok tfibsegs (decL_E d q regs2 [Z_to_bv 64 (q + Z.of_nat (length (WriterSpec.six_bytes six)))]) decL_mss
    (restrict (w_H Wc) (YK11.mkst regs2 (Z_to_bv 64 DEC_RA_MEMCHR) mem2 (YK11.seg_rom tfibsegs))).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 md2 HE HH Hilt HJ2 HARU2 HFr2 HLs2 HNq2 RK.
pose proof asan_consts as ((C1 & C2) & _).
destruct (decLO_mfacts d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 HE HH Hilt RK)
  as (E2 & E48u & _ & _ & Hnb & _).
pose proof (decLB_q d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH) as (Q16 & Q1 & Q2 & _ & _ & _ & Qa).
pose proof (decLB_sp d HE) as (SP1 & _ & _).
pose proof (decLB_qw d q i six pad acc Wc lyc Sc Uc regsc memc mdc k mem2 md2 HE HH HARU2) as HQW.
destruct (Qa (q + Z.of_nat (length (WriterSpec.six_bytes six))) ltac:(lia)) as (_ & _ & G1 & G2).
clear Qa.
pose proof HH as HH0. decL_unhead HH0.
set (n := Z.of_nat (length (WriterSpec.six_bytes six))) in *.
set (Em := decL_E d q regs2 [Z_to_bv 64 (q + n)]) in *.
assert (E9 : ew Em 9 = Z_to_bv 64 q)
  by (unfold Em; rewrite (decL_E_reg d q regs2 _ 9 9%bv eq_refl), (RK 9%bv ltac:(decLO_in)); exact R9).
assert (E21 : ew Em 21 = Z_to_bv 64 n)
  by (unfold Em; rewrite (decL_E_reg d q regs2 _ 21 21%bv eq_refl), (RK 21%bv ltac:(decLO_in)); exact R21).
assert (E48 : ew Em 48 = Z_to_bv 64 (q + n)) by exact (decL_E_ex d q regs2 _ 0).
assert (Hq0 : 4096 <= q) by (unfold HEAD in Q1; lia).
assert (HSm0 : st_ok tfibsegs Em decL_mss0
  (restrict (w_H Wc) (YK11.mkst regs2 (Z_to_bv 64 DEC_RA_MEMCHR) mem2 (YK11.seg_rom tfibsegs)))).
{ apply (decL_build d q Wc lyc Sc Uc regs2 mem2 md2 k [Z_to_bv 64 (q + n)] DEC_RA_MEMCHR [decL_str] decL_mgf
    HE HJ2 HARU2).
  - unfold spZ. rewrite (RK 2%bv ltac:(decLO_in)). exact Hsp.
  - exact HFr2.
  - exact HLs2.
  - exact HNq2.
  - lia.
  - vm_compute. reflexivity.
  - apply (decLO_str_ok Em (w_H Wc) mem2 (q + n) E48u); [lia | lia | apply HQW; lia].
  - apply (decLO_mpd Em (d_sp d - DEC_F) (q + n) E2 E48u); [unfold DEC_F; lia | unfold DEC_F; lia | exact G1 | exact G2].
  - unfold decL_mgf. cbn [atoms_ok]. split.
    + fold n Em. unfold afact_ok. cbn [af_lo af_hi af_al2].
      first [rewrite E48u | rewrite E48, (wz (q + n)) by (unfold DEC_CEIL in *; lia)].
      rewrite Z.pow_0_r, Z.mod_1_r. unfold DEC_CEIL in *. lia.
    + apply (decL_atoms_k d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 _ 0 (2 ^ 28) 0 6 HE HH RK);
        [pose proof HE as (_ & _ & _ & _ & _ & _ & _ & _ & HLEN & _); lia
        | pose proof (Z.mod_pos_bound (6 * Z.of_nat (length six)) 8 ltac:(lia));
          destruct (decLA_bits_cases (Z.of_nat (length six)) ltac:(lia)) as [X|[X|[X|X]]]; lia]. }
unfold decL_mss. refine (st_ok_facts tfibsegs Em decL_mss0 _ _ HSm0 _).
apply (facts_ok_add_alias Em (ss_facts decL_mss0)); [exact (st_ok_facts_ok tfibsegs _ _ _ HSm0)|].
rewrite (denot_lit_U Em (SAlu _ _ _)), (denot_lit_U Em (SOff 48 0)). f_equal.
rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom Em 9 q E9) by lia. rewrite (U_atom Em 21 n E21) by lia.
rewrite (U_atom Em 48 (q + n) E48) by lia.
apply zcanon_small. lia.
Qed.

Lemma decLO_msh_ok : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  (i < length (d_tb d))%nat -> decL_memf d q six Wc lyc Sc mem2 ->
  (forall r, In r decLO_kregs -> getr regs2 r = getr regsc r) ->
  sh_ok tfibsegs decL_Bx decL_mSH (decL_E d q regs2 [Z_to_bv 64 (q + Z.of_nat (length (WriterSpec.six_bytes six)))])
    (mrestrict (w_H Wc) mem2).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 HE HH Hilt HM2 RK.
pose proof asan_consts as ((C1 & C2) & _ & C4 & _).
destruct (decLO_mfacts d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 HE HH Hilt RK)
  as (_ & _ & _ & _ & Hnb & _).
pose proof (decLB_q d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH) as (_ & Q1 & Q2 & _ & Qband & _).
destruct (decLO_hd d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HH) as (_ & _ & _ & _ & _ & R20 & _).
assert (E20 : ew (decL_E d q regs2 [Z_to_bv 64 (q + Z.of_nat (length (WriterSpec.six_bytes six)))]) 20 =
  Z_to_bv 64 SHADOW_OFF)
  by (rewrite (decL_E_reg d q regs2 _ 20 20%bv eq_refl), (RK 20%bv ltac:(decLO_in)); exact R20).
assert (E48 : ew (decL_E d q regs2 [Z_to_bv 64 (q + Z.of_nat (length (WriterSpec.six_bytes six)))]) 48 =
  Z_to_bv 64 (q + Z.of_nat (length (WriterSpec.six_bytes six)))) by exact (decL_E_ex d q regs2 _ 0).
unfold HEAD in Q1.
unfold sh_ok, decL_mSH. constructor; [|constructor].
pose proof HM2 as (_ & HRA2 & _).
apply (shent_ok_of_range tfibsegs (w_H Wc) mem2 _ decL_Bx 48%nat q (d_n d)
  (q + Z.of_nat (length (WriterSpec.six_bytes six))) 0 1 HRA2).
- unfold decL_Bx. apply (U_atom _ 20 SHADOW_OFF E20). unfold SHADOW_OFF; lia.
- apply (U_atom _ 48 _ E48). lia.
- lia.
- lia.
- intros x Hx. rewrite C4 in Qband. unfold SHADOW_OFF in *. lia.
Qed.

Lemma decLT_none : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 md2,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  (forall W3 ly3 S3 U3 regs3 mem3 md3 k3, dec_at_free B d q W3 ly3 S3 U3 regs3 mem3 md3 k3 ->
     SRr tfibsegs W3 (cfg_at tfibsegs A_fuzz_free regs3 mem3 md3) (dec_post B d)) ->
  (i < length (d_tb d))%nat ->
  WriterSpec.b64_ws (nth i (d_tb d) 0) = false -> nth i (d_tb d) 0 <> 61 -> WriterSpec.b64v (nth i (d_tb d) 0) = None ->
  dec_J B d lyc Sc Wc Uc mem2 md2 k -> ARU tfibsegs B lyc Sc Uc Wc mem2 md2 ->
  decL_memf d q six Wc lyc Sc mem2 ->
  (forall r, In r decLO_kregs -> getr regs2 r = getr regsc r) ->
  st_ok tfibsegs (decL_E d q regs2 [Z_to_bv 64 (q + Z.of_nat (length (WriterSpec.six_bytes six)))])
    (add_cond decL_mss (mkAC BC_EQ (SOff 10 0) (SLit 0)))
    (restrict (w_H Wc) (YK11.mkst regs2 (Z_to_bv 64 DEC_RA_MEMCHR) mem2 (YK11.seg_rom tfibsegs))) ->
  sh_ok tfibsegs decL_Bx decL_mSH (decL_E d q regs2 [Z_to_bv 64 (q + Z.of_nat (length (WriterSpec.six_bytes six)))])
    (mrestrict (w_H Wc) mem2) ->
  SRr tfibsegs Wc (mkCfg (YK11.mkst regs2 (Z_to_bv 64 DEC_RA_MEMCHR) mem2 (YK11.seg_rom tfibsegs)) md2) (dec_post B d).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 md2 HE HH HFREE Hilt Hws H61 Hv HJ2 HARU2 HM2 RK
  HS2 SHm.
destruct (decLO_mfacts d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 HE HH Hilt RK)
  as (E2 & E48u & SP2 & Htmp & _ & HD).
unfold dec_J in HJ2.
fsw_aj_run_to_tokU fsw_wr_tbl_ok HS2 HJ2 HARU2 SHm fs_Bspan A_fuzz_free.
{ eapply decLO_awr_m; [exact E2 | exact E48u | exact SP2 | exact Htmp | reflexivity]. }
apply (decLO_free d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 _ _ _ _ HE HH HFREE HM2 RK HS2
  ltac:(intros m Hm; rewrite ?ew_ewset_other by lia; reflexivity)).
- reflexivity.
- reflexivity.
- vm_compute; reflexivity.
- vm_compute; reflexivity.
- vm_compute; reflexivity.
- reflexivity.
- exact HJ2.
- exact HARU2.
- exact (decLO_meq_m _ d _ _ mem2 mem2 _ E2 E48u HF (fun a _ _ _ => eq_refl) eq_refl).
- rewrite HD. exact (decLA_out_bad _ pad six _ Hws H61 Hv).
Qed.

Lemma decLT_some : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 md2 v,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  (forall W3 ly3 S3 U3 regs3 mem3 md3 k3, dec_at_free B d q W3 ly3 S3 U3 regs3 mem3 md3 k3 ->
     SRr tfibsegs W3 (cfg_at tfibsegs A_fuzz_free regs3 mem3 md3) (dec_post B d)) ->
  (forall six' pad' acc' Wc' lyc' Sc' Uc' regsc' memc' mdc' k',
     dec_head B d q (S i) six' pad' acc' Wc' lyc' Sc' Uc' regsc' memc' mdc' k' ->
     SRr tfibsegs Wc' (decL_hcfg regsc' memc' mdc') (dec_post B d)) ->
  (i < length (d_tb d))%nat ->
  WriterSpec.b64_ws (nth i (d_tb d) 0) = false -> nth i (d_tb d) 0 <> 61 -> WriterSpec.b64v (nth i (d_tb d) 0) = Some v ->
  dec_J B d lyc Sc Wc Uc mem2 md2 k -> ARU tfibsegs B lyc Sc Uc Wc mem2 md2 ->
  decL_memf d q six Wc lyc Sc mem2 ->
  (forall r, In r decLO_kregs -> getr regs2 r = getr regsc r) -> getr regs2 10 = w64 (G_B64 + v) ->
  st_ok tfibsegs (decL_E d q regs2 [Z_to_bv 64 (q + Z.of_nat (length (WriterSpec.six_bytes six)))])
    (add_cond decL_mss (mkAC (neg_bc BC_EQ) (SOff 10 0) (SLit 0)))
    (restrict (w_H Wc) (YK11.mkst regs2 (Z_to_bv 64 DEC_RA_MEMCHR) mem2 (YK11.seg_rom tfibsegs))) ->
  sh_ok tfibsegs decL_Bx decL_mSH (decL_E d q regs2 [Z_to_bv 64 (q + Z.of_nat (length (WriterSpec.six_bytes six)))])
    (mrestrict (w_H Wc) mem2) ->
  SRr tfibsegs Wc (mkCfg (YK11.mkst regs2 (Z_to_bv 64 DEC_RA_MEMCHR) mem2 (YK11.seg_rom tfibsegs)) md2) (dec_post B d).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 md2 v HE HH HFREE HIH Hilt Hws H61 Hv HJ2 HARU2 HM2
  RK Rr HS2 SHm.
destruct (decLO_mfacts d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 HE HH Hilt RK)
  as (E2 & E48u & SP2 & Htmp & Hnb & HD).
pose proof HE as (_ & _ & _ & _ & _ & HCS & _ & _ & HLEN & _).
pose proof HCS as (_ & Ht4096 & Htc & _).
pose proof asan_consts as ((Cc1 & Cc2) & _).
pose proof (decLB_q d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH) as (Q16 & Q1 & Q2 & Qn & _).
pose proof (decL_dn_pos d) as Hdn.
pose proof (decLB_sp d HE) as (SPa & SPb & SPc).
pose proof (decLA_b64v_range _ v Hv) as Hv64.
pose proof HH as HH0. decL_unhead HH0.
pose proof (decLO_bits (Z.of_nat (length six)) ltac:(lia)) as (Hb1 & Hb2).
set (n := Z.of_nat (length (WriterSpec.six_bytes six))) in *.
assert (Hn0 : 0 <= n) by (unfold n; lia).
set (Em := decL_E d q regs2 [Z_to_bv 64 (q + n)]) in *.
assert (EK : forall (m : nat) (r : bv 5), Z.of_nat m = bv_unsigned r -> In r decLO_kregs -> ew Em m = getr regsc r)
  by (intros m r Hm Hr; unfold Em; rewrite (decL_E_reg d q regs2 _ m r Hm); exact (RK r Hr)).
assert (E10 : ew Em 10 = Z_to_bv 64 (G_B64 + v)) by (unfold Em; rewrite (decL_E_reg d q regs2 _ 10 10%bv eq_refl); exact Rr).
assert (E18 : ew Em 18 = w64 (d_text d + Z.of_nat i)) by (rewrite (EK 18%nat 18%bv eq_refl ltac:(decLO_in)); exact R18).
assert (E19 : ew Em 19 = Z_to_bv 64 G_B64) by (rewrite (EK 19%nat 19%bv eq_refl ltac:(decLO_in)); exact R19).
assert (E21 : ew Em 21 = w64 n) by (rewrite (EK 21%nat 21%bv eq_refl ltac:(decLO_in)); exact R21).
assert (E22 : ew Em 22 = Z_to_bv 64 acc) by (rewrite (EK 22%nat 22%bv eq_refl ltac:(decLO_in)); exact R22).
assert (E23 : ew Em 23 = w64 (6 * Z.of_nat (length six) mod 8)) by (rewrite (EK 23%nat 23%bv eq_refl ltac:(decLO_in)); exact R23).
assert (E24 : ew Em 24 = Z_to_bv 64 pad) by (rewrite (EK 24%nat 24%bv eq_refl ltac:(decLO_in)); exact R24).
assert (E25 : ew Em 25 = w64 (d_text d + Z.of_nat i - 1)) by (rewrite (EK 25%nat 25%bv eq_refl ltac:(decLO_in)); exact R25).
assert (Hp64 : 0 <= pad < 2 ^ 64) by lia.
assert (RK0 : forall r, In r decL_kept_regs -> getr regs2 r = getr regsc r).
{ intros r Hr. apply RK. cbv [decL_kept_regs In] in Hr.
  repeat (destruct Hr as [<-|Hr]; [decLO_in|]); destruct Hr. }
unfold dec_J in HJ2.
(* 0x84d50 -> 0x84d54 *)
fsw_aj_run_tokU fsw_wr_tbl_ok HS2 HJ2 HARU2 SHm fs_Bspan.
{ eapply decLO_awr_m; [exact E2 | exact E48u | exact SP2 | exact Htmp | reflexivity]. }
pose proof (decLO_meq_m _ d _ _ mem2 mem2 _ E2 E48u HF (fun a _ _ _ => eq_refl) eq_refl) as MEQ3.
clear HF HFr HG.
(* 0x84d54: bnez s8 (pad) *)
eapply SRr_sym_branch with (c := BC_NE) (a := SOff 24 0) (b := SLit 0); [exact HS2 | intros Hb' HS3 | intros Hb' HS3];
  rewrite (decLA_br_ne0 _ 24 pad) in Hb' by (rewrite ?ew_ewset_other by lia; first [exact E24 | lia]); clear HS2.
- (* pad <> 0: a letter after '=' *)
  apply Bool.negb_true_iff, Z.eqb_neq in Hb'.
  fsw_aj_run_to_tokU fsw_wr_tbl_ok HS3 HJ2 HARU2 SHm fs_Bspan A_fuzz_free.
  { eapply decLO_awr_m; [exact E2 | exact E48u | exact SP2 | exact Htmp | reflexivity]. }
  apply (decLO_free d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 _ _ _ _ HE HH HFREE HM2 RK HS3
    ltac:(intros m Hm; rewrite ?ew_ewset_other by lia; reflexivity)).
  + reflexivity.
  + reflexivity.
  + vm_compute; reflexivity.
  + vm_compute; reflexivity.
  + vm_compute; reflexivity.
  + reflexivity.
  + exact HJ2.
  + exact HARU2.
  + exact (decLO_meq_m _ d _ _ mem2 _ _ E2 E48u HF MEQ3 eq_refl).
  + rewrite HD. exact (decLA_out_padbad _ _ pad six _ Hws H61 Hv Hb').
- (* pad = 0: the sextet is taken *)
  apply Bool.negb_false_iff, Z.eqb_eq in Hb'. subst pad.
  assert (HSK : WriterSpec.b64_dec (d_tb d) = decLA_out 0 (six ++ [v]) (skipn (S i) (d_tb d)))
    by (rewrite HD; apply decLA_out_val; assumption).
  destruct (decLA_bits_cases (Z.of_nat (length six)) ltac:(lia)) as [B0 | B26'].
  + (* bits = 0: no byte yet *)
    pose proof (decLO_add_atom _ _ _ 23 (mkAF 0 0 1) HS3
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2];
            rewrite ?ew_ewset_other by lia; rewrite E23, decL_w64u by lia;
            change (2 ^ 1) with 2; lia)) as HS4.
    clear HS3.
    fsw_aj_run_to_tokU fsw_wr_tbl_ok HS4 HJ2 HARU2 SHm fs_Bspan DEC_HEAD.
    { eapply decLO_awr_m; [exact E2 | exact E48u | exact SP2 | exact Htmp | reflexivity]. }
    pose proof (decLO_meq_m _ d _ _ mem2 _ _ E2 E48u HF MEQ3 eq_refl) as MEQ4.
    lazymatch type of HS4 with st_ok _ ?X _ (restrict _ ?M) => set (Ex4 := X) in HS4; set (msN := M) in * end.
    assert (EX : forall m, (m < 49)%nat -> ew Ex4 m = ew Em m)
      by (intros m Hm; unfold Ex4; rewrite ?ew_ewset_other by lia; reflexivity).
    assert (HA : U Ex4 decLO_acc_e mod 4096 = (acc mod 64) * 64 + v)
      by (apply decLO_acc; [rewrite EX by lia; exact E10 | exact Hv64 | rewrite EX by lia; exact E19
                            | rewrite EX by lia; exact E22 | exact Hacc]).
    assert (Hsn : WriterSpec.six_bytes (six ++ [v]) = WriterSpec.six_bytes six) by (apply decLA_snoc0; exact B0).
    assert (HM3 : decL_memf d q (six ++ [v]) Wc lyc Sc (ms_mem msN)).
    { unfold decL_memf. rewrite Hsn.
      apply (decLB_tr d q i six 0 acc Wc lyc Sc Uc regsc memc mdc k mem2 (ms_mem msN) HE HH HM2).
      intros a Ha H1 H2. apply aview_at. apply MEQ4; [exact Ha | unfold DEC_F in *; lia | lia]. }
    eapply (decL_next d q i six 0 acc Wc lyc Sc Uc regsc memc mdc k regs2 Ex4 _ msN _ (six ++ [v]) 0 (U Ex4 decLO_acc_e)
      [Z_to_bv 64 (q + n)] HE HH HIH RK0 HS4);
      [ reflexivity | reflexivity | vm_compute; reflexivity
      | intros m Hm; apply EX; lia | vm_compute; reflexivity
      | exact HJ2 | exact HARU2 | exact HM3 | .. ].
    * eapply (decL_reg (w_H Wc) Ex4 _ msN 18%bv (SOff 18 1)); [exact HS4 | vm_compute; reflexivity |].
      rewrite (decL_soff _ 18 1 (d_text d + Z.of_nat i)); [f_equal; lia | rewrite EX by lia; exact E18 | lia | lia].
    * eapply (decL_reg (w_H Wc) Ex4 _ msN 25%bv (SOff 25 1)); [exact HS4 | vm_compute; reflexivity |].
      rewrite (decL_soff _ 25 1 (d_text d + Z.of_nat i - 1)); [f_equal; lia | rewrite EX by lia; exact E25 | lia | lia].
    * rewrite Hsn. eapply (decL_reg (w_H Wc) Ex4 _ msN 21%bv (SOff 21 0)); [exact HS4 | vm_compute; reflexivity |].
      rewrite fsw_SOff0, EX by lia. exact E21.
    * eapply (decL_reg (w_H Wc) Ex4 _ msN 22%bv decLO_acc_e); [exact HS4 | vm_compute; reflexivity |].
      unfold w64. apply denot_lit_U.
    * pose proof (U_range Ex4 decLO_acc_e) as X. unfold M64 in X. exact X.
    * eapply (decL_reg (w_H Wc) Ex4 _ msN 23%bv (SOff 23 6)); [exact HS4 | vm_compute; reflexivity |].
      rewrite (decL_soff _ 23 6 0); [| rewrite EX by lia; rewrite E23, B0; reflexivity | lia | lia].
      f_equal. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1.
      rewrite decLA_bits by lia. rewrite B0. reflexivity.
    * exact (fsw_reg_lit (w_H Wc) _ _ msN 24%bv 0 HS4 ltac:(vm_compute; reflexivity) ltac:(lia)).
    * lia.
    * lia.
    * rewrite length_app. cbn [length]. lia.
    * apply Forall_app. split; [exact Hsix64 | constructor; [lia | constructor]].
    * rewrite last_last.
      replace (U Ex4 decLO_acc_e mod 64) with ((U Ex4 decLO_acc_e mod 4096) mod 64) by (Z.div_mod_to_equations; lia).
      rewrite HA. pose proof (Z.mod_pos_bound acc 64 ltac:(lia)). Z.div_mod_to_equations; lia.
    * exact HSK.
  + (* bits in [2, 6]: the byte q + n is stored *)
    assert (B26 : 2 <= 6 * Z.of_nat (length six) mod 8) by lia.
    pose proof (decLO_add_atom _ _ _ 23 (mkAF 2 6 1) HS3
      ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2];
            rewrite ?ew_ewset_other by lia; rewrite E23, decL_w64u by lia;
            change (2 ^ 1) with 2; lia)) as HS4.
    clear HS3.
    fsw_aj_run_to_tokU fsw_wr_tbl_ok HS4 HJ2 HARU2 SHm fs_Bspan DEC_HEAD.
    { eapply decLO_awr_m; [exact E2 | exact E48u | exact SP2 | exact Htmp | reflexivity]. }
    pose proof (decLO_meq_m _ d _ _ mem2 _ _ E2 E48u HF MEQ3 eq_refl) as MEQ4.
    lazymatch type of HS4 with st_ok _ ?X _ (restrict _ ?M) => set (Ex4 := X) in HS4; set (msN := M) in * end.
    assert (EX : forall m, (m < 49)%nat -> ew Ex4 m = ew Em m)
      by (intros m Hm; unfold Ex4; rewrite ?ew_ewset_other by lia; reflexivity).
    assert (HA : U Ex4 decLO_acc_e mod 4096 = (acc mod 64) * 64 + v)
      by (apply decLO_acc; [rewrite EX by lia; exact E10 | exact Hv64 | rewrite EX by lia; exact E19
                            | rewrite EX by lia; exact E22 | exact Hacc]).
    set (b := Z.shiftr (last six 0 * 64 + v) (6 * Z.of_nat (length six) mod 8 - 2) mod 256).
    assert (Hsnoc : WriterSpec.six_bytes (six ++ [v]) = WriterSpec.six_bytes six ++ [b])
      by (unfold b; apply decLA_snoc; [exact Hsix64 | exact Hv64 | exact B26]).
    assert (X48u : bv_unsigned (ew Ex4 48) = q + n) by (rewrite EX by lia; exact E48u).
    assert (HAV : aview tfibsegs (w_H Wc) (ms_mem msN) (q + n) = Some b).
    { pose proof (fsw_region_nth Ex4 _ (restrict (w_H Wc) msN) 3 decLO_str2 HS4 eq_refl) as HR.
      cbn [ms_mem restrict] in HR.
      rewrite <- X48u. rewrite (decLO_str2_aview Ex4 (w_H Wc) (ms_mem msN) HR). f_equal.
      rewrite (decLA_byte Ex4 decLO_acc_e (6 * Z.of_nat (length six) mod 8)) by (try (rewrite EX by lia; exact E23); lia).
      rewrite HA, Hlast. reflexivity. }
    assert (HM3 : decL_memf d q (six ++ [v]) Wc lyc Sc (ms_mem msN)).
    { apply (decLB_store d q i six 0 acc Wc lyc Sc Uc regsc memc mdc k mem2 (ms_mem msN) (d_sp d - DEC_F) (d_sp d)
        (six ++ [v]) b HE HH HM2 ltac:(unfold DEC_F; lia) ltac:(lia) Hnb).
      - intros a Ha H1 H2. apply aview_at. exact (MEQ4 a Ha H1 H2).
      - exact HAV.
      - unfold b. apply Z.mod_pos_bound. lia.
      - exact Hsnoc. }
    eapply (decL_next d q i six 0 acc Wc lyc Sc Uc regsc memc mdc k regs2 Ex4 _ msN _ (six ++ [v]) 0 (U Ex4 decLO_acc_e)
      [Z_to_bv 64 (q + n)] HE HH HIH RK0 HS4);
      [ reflexivity | reflexivity | vm_compute; reflexivity
      | intros m Hm; apply EX; lia | vm_compute; reflexivity
      | exact HJ2 | exact HARU2 | exact HM3 | .. ].
    * eapply (decL_reg (w_H Wc) Ex4 _ msN 18%bv (SOff 18 1)); [exact HS4 | vm_compute; reflexivity |].
      rewrite (decL_soff _ 18 1 (d_text d + Z.of_nat i)); [f_equal; lia | rewrite EX by lia; exact E18 | lia | lia].
    * eapply (decL_reg (w_H Wc) Ex4 _ msN 25%bv (SOff 25 1)); [exact HS4 | vm_compute; reflexivity |].
      rewrite (decL_soff _ 25 1 (d_text d + Z.of_nat i - 1)); [f_equal; lia | rewrite EX by lia; exact E25 | lia | lia].
    * eapply (decL_reg (w_H Wc) Ex4 _ msN 21%bv (SOff 21 1)); [exact HS4 | vm_compute; reflexivity |].
      rewrite (decL_soff _ 21 1 n); [| rewrite EX by lia; exact E21 | unfold HEAD in *; lia | unfold HEAD in *; lia].
      f_equal. rewrite Hsnoc, length_app. cbn [length]. unfold n. lia.
    * eapply (decL_reg (w_H Wc) Ex4 _ msN 22%bv decLO_acc_e); [exact HS4 | vm_compute; reflexivity |].
      unfold w64. apply denot_lit_U.
    * pose proof (U_range Ex4 decLO_acc_e) as X. unfold M64 in X. exact X.
    * eapply (decL_reg (w_H Wc) Ex4 _ msN 23%bv (SOff 23 (-2))); [exact HS4 | vm_compute; reflexivity |].
      rewrite (decL_soff _ 23 (-2) (6 * Z.of_nat (length six) mod 8)); [| rewrite EX by lia; exact E23 | lia | lia].
      f_equal. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1.
      rewrite decLA_bits by lia. destruct (Z.eqb_spec (6 * Z.of_nat (length six) mod 8) 0); lia.
    * exact (fsw_reg_lit (w_H Wc) _ _ msN 24%bv 0 HS4 ltac:(vm_compute; reflexivity) ltac:(lia)).
    * lia.
    * lia.
    * rewrite length_app. cbn [length]. lia.
    * apply Forall_app. split; [exact Hsix64 | constructor; [lia | constructor]].
    * rewrite last_last.
      replace (U Ex4 decLO_acc_e mod 64) with ((U Ex4 decLO_acc_e mod 4096) mod 64) by (Z.div_mod_to_equations; lia).
      rewrite HA. pose proof (Z.mod_pos_bound acc 64 ltac:(lia)). Z.div_mod_to_equations; lia.
    * exact HSK.
Qed.

Lemma decLO_tail : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 md2 rv,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  (forall W3 ly3 S3 U3 regs3 mem3 md3 k3, dec_at_free B d q W3 ly3 S3 U3 regs3 mem3 md3 k3 ->
     SRr tfibsegs W3 (cfg_at tfibsegs A_fuzz_free regs3 mem3 md3) (dec_post B d)) ->
  (forall six' pad' acc' Wc' lyc' Sc' Uc' regsc' memc' mdc' k',
     dec_head B d q (S i) six' pad' acc' Wc' lyc' Sc' Uc' regsc' memc' mdc' k' ->
     SRr tfibsegs Wc' (decL_hcfg regsc' memc' mdc') (dec_post B d)) ->
  (i < length (d_tb d))%nat ->
  WriterSpec.b64_ws (nth i (d_tb d) 0) = false -> nth i (d_tb d) 0 <> 61 ->
  dec_J B d lyc Sc Wc Uc mem2 md2 k -> ARU tfibsegs B lyc Sc Uc Wc mem2 md2 ->
  decL_memf d q six Wc lyc Sc mem2 ->
  dec_frame_ok Wc mem2 (d_sp d - DEC_F) (d_regs d) -> dec_lenp_slot Wc mem2 (d_sp d - DEC_F) (d_lenp d) ->
  dec_nq_slot Wc mem2 (d_sp d - DEC_F) q ->
  (forall r, In r decLO_kregs -> getr regs2 r = getr regsc r) ->
  getr regs2 10 = w64 rv ->
  match zfind (nth i (d_tb d) 0) WriterSpec.b64_table with None => rv = 0 | Some j => rv = G_B64 + Z.of_nat j end ->
  SRr tfibsegs Wc (mkCfg (YK11.mkst regs2 (Z_to_bv 64 DEC_RA_MEMCHR) mem2 (YK11.seg_rom tfibsegs)) md2) (dec_post B d).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 md2 rv HE HH HFREE HIH Hilt Hws H61 HJ2 HARU2 HM2
  HFr2 HLs2 HNq2 RK Rr Hz.
pose proof (decLO_mss_ok d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 md2 HE HH Hilt HJ2 HARU2 HFr2 HLs2
  HNq2 RK) as HSm.
pose proof (decLO_msh_ok d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 HE HH Hilt HM2 RK) as SHm.
assert (E10 : ew (decL_E d q regs2 [Z_to_bv 64 (q + Z.of_nat (length (WriterSpec.six_bytes six)))]) 10 = Z_to_bv 64 rv)
  by (rewrite (decL_E_reg d q regs2 _ 10 10%bv eq_refl); exact Rr).
pose proof (decLA_zfind (nth i (d_tb d) 0) (decLO_c d i HE Hilt)) as Zf.
revert Hz Zf. destruct (zfind (nth i (d_tb d) 0) WriterSpec.b64_table) as [j|] eqn:Ez; intros Hz Zf; subst rv.
- pose proof (decLA_b64v_range _ _ Zf) as Hj.
  eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 10 0) (b := SLit 0); [exact HSm | intros Hb _ | intros _ HS2].
  + exfalso. rewrite (decLA_br_eq0 _ 10 (G_B64 + Z.of_nat j) E10 ltac:(unfold G_B64; lia)) in Hb.
    apply Z.eqb_eq in Hb. unfold G_B64 in Hb. lia.
  + exact (decLT_some d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 md2 (Z.of_nat j) HE HH HFREE HIH Hilt
      Hws H61 Zf HJ2 HARU2 HM2 RK Rr HS2 SHm).
- eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 10 0) (b := SLit 0); [exact HSm | intros _ HS2 | intros Hb _].
  + exact (decLT_none d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 md2 HE HH HFREE Hilt Hws H61 Zf
      HJ2 HARU2 HM2 RK HS2 SHm).
  + exfalso. rewrite (decLA_br_eq0 _ 10 0 E10 ltac:(lia)) in Hb. cbn in Hb. discriminate Hb.
Qed.

Lemma decLO_call : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k Ex ss ms md',
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  (forall W3 ly3 S3 U3 regs3 mem3 md3 k3, dec_at_free B d q W3 ly3 S3 U3 regs3 mem3 md3 k3 ->
     SRr tfibsegs W3 (cfg_at tfibsegs A_fuzz_free regs3 mem3 md3) (dec_post B d)) ->
  (forall six' pad' acc' Wc' lyc' Sc' Uc' regsc' memc' mdc' k',
     dec_head B d q (S i) six' pad' acc' Wc' lyc' Sc' Uc' regsc' memc' mdc' k' ->
     SRr tfibsegs Wc' (decL_hcfg regsc' memc' mdc') (dec_post B d)) ->
  (i < length (d_tb d))%nat ->
  WriterSpec.b64_ws (nth i (d_tb d) 0) = false -> nth i (d_tb d) 0 <> 61 ->
  st_ok tfibsegs Ex ss (restrict (w_H Wc) ms) ->
  (forall n, (n < 49)%nat -> ew Ex n = ew (decL_E d q regsc [Z_to_bv 64 (nth i (d_tb d ++ [0]) 0)]) n) ->
  ss_pc ss = PC_memchr -> ss_resv ss = None -> ss_regs ss = decLO_cregs ->
  ss_mem ss = fsT_ret_regions DEC_F decL_cs [decL_txr] ->
  dec_J B d lyc Sc Wc Uc (ms_mem ms) md' k -> ARU tfibsegs B lyc Sc Uc Wc (ms_mem ms) md' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp d - DEC_F <= a < d_sp d) -> ms_mem ms (Z_to_bv 64 a) = memc (Z_to_bv 64 a)) ->
  SRr tfibsegs Wc (mkCfg ms md') (dec_post B d).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k Ex ss ms md' HE HH HFREE HIH Hilt Hws H61 HS HEx Hpc Hrv Hregs
  Hmem HJm HARUm MEQ.
pose proof asan_consts as ((C1 & C2) & _ & _ & _ & C5).
assert (FR : STK_RT_STR = ltac:(let v := eval vm_compute in STK_RT_STR in exact v)) by reflexivity.
assert (FE : ESTACK = 4096) by reflexivity.
assert (FS : STK_preset_base64_decode = ltac:(let v := eval vm_compute in STK_preset_base64_decode in exact v)) by reflexivity.
assert (Hcn : nth i (d_tb d ++ [0]) 0 = nth i (d_tb d) 0) by (rewrite app_nth1 by exact Hilt; reflexivity).
rewrite Hcn in HEx.
pose proof (decLO_c d i HE Hilt) as Hc.
pose proof HH as HH0. decL_unhead HH0.
pose proof (fsw_sp B _ _ _ _ _ _ _ _ _ (proj1 (proj1 HE))) as (Hsp16 & Hspc & Hsp47 & _).
change (spZ (d_regs d)) with (d_sp d) in Hsp16, Hspc, Hsp47.
pose proof (decLB_sp d HE) as (SP1 & SP2 & SP3).
pose proof (decL_lenp_range d HE) as (L1 & L2 & _).
pose proof (decLB_q d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH) as (_ & Q1 & Q2 & _).
pose proof (decL_dn_pos d) as Hdn.
pose proof (proj1 (proj1 HE)) as HPREU. pose proof HPREU as (HAP & _ & _).
pose proof HAP as (_ & _ & _ & Hgp & Htp & _).
pose proof HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPL).
destruct HPL as (_ & _ & _ & Hot16 & _).
assert (GK : forall (r : bv 5) (m : nat), sr_get decLO_cregs r = SOff m 0 -> (m < 49)%nat -> Z.of_nat m = bv_unsigned r ->
  getr (ms_regs ms) r = getr regsc r).
{ intros r m H1 Hm Hr. apply (decL_reg (w_H Wc) Ex ss ms r (SOff m 0)); [exact HS | rewrite Hregs; exact H1 |].
  rewrite fsw_SOff0, (HEx m Hm). exact (decL_E_reg d q regsc _ m r Hr). }
assert (R1 : getr (ms_regs ms) 1 = Z_to_bv 64 544080)
  by exact (fsw_reg_lit (w_H Wc) Ex ss ms 1%bv 544080 HS ltac:(rewrite Hregs; reflexivity) ltac:(lia)).
assert (R12 : getr (ms_regs ms) 12 = Z_to_bv 64 65)
  by exact (fsw_reg_lit (w_H Wc) Ex ss ms 12%bv 65 HS ltac:(rewrite Hregs; reflexivity) ltac:(lia)).
assert (R10 : getr (ms_regs ms) 10 = w64 G_B64).
{ apply (decL_reg (w_H Wc) Ex ss ms 10%bv (SOff 19 0)); [exact HS | rewrite Hregs; reflexivity |].
  rewrite fsw_SOff0, (HEx 19%nat ltac:(lia)), (decL_E_reg d q regsc _ 19 19%bv eq_refl). exact R19. }
assert (R11 : getr (ms_regs ms) 11 = w64 (nth i (d_tb d) 0)).
{ apply (decL_reg (w_H Wc) Ex ss ms 11%bv (SOff 48 0)); [exact HS | rewrite Hregs; reflexivity |].
  rewrite fsw_SOff0, (HEx 48%nat ltac:(lia)). exact (decL_E_ex d q regsc _ 0). }
assert (R2 : getr (ms_regs ms) 2 = getr regsc 2) by (apply (GK 2%bv 2%nat); [vm_compute; reflexivity | lia | reflexivity]).
assert (R3m : getr (ms_regs ms) 3 = getr regsc 3) by (apply (GK 3%bv 3%nat); [vm_compute; reflexivity | lia | reflexivity]).
assert (R4m : getr (ms_regs ms) 4 = getr regsc 4) by (apply (GK 4%bv 4%nat); [vm_compute; reflexivity | lia | reflexivity]).
assert (Hspt : spZ (ms_regs ms) = d_sp d - DEC_F) by (unfold spZ at 1; rewrite R2; exact Hsp).
unfold dec_J in HJm.
assert (HPRE1 : ecall_preU_k tfibsegs B STK_RT_STR lyc Sc Uc Wc (ms_regs ms) (ms_mem ms) md').
{ apply (fsw_ecall_preU_k_at B (d_STKJ d) (d_ot d) (d_FP d) (d_ly d) (d_S d) (d_W d) (unpoison (d_U d) (d_mem d))
    (d_md d) [] lyc Sc Uc Wc (ms_mem ms) md' k (ms_regs ms) (d_sp d - DEC_F - d_ot d) STK_RT_STR HJm HARUm).
  - rewrite Hspt. lia.
  - unfold DEC_F. clear -Hsp16 Hot16. lia.
  - unfold DEC_F. lia.
  - rewrite FE. unfold d_STKJ, DEC_F. rewrite FS. lia.
  - rewrite FR. lia.
  - rewrite FR. unfold d_STKJ, DEC_F. rewrite FS. lia.
  - rewrite R1. apply ret_ok_even. rewrite unsigned_lit_small by lia. reflexivity.
  - rewrite R3m, R3. exact Hgp.
  - rewrite R4m, R4. exact Htp. }
assert (AGR : forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp d - DEC_F <= a < d_sp d) ->
  aview tfibsegs (w_H Wc) (ms_mem ms) a = aview tfibsegs (w_H Wc) memc a)
  by (intros a Ha Hn; apply aview_at; exact (MEQ a Ha Hn)).
destruct (decLB_g64 d q i six pad acc Wc lyc Sc Uc regsc memc mdc k (ms_mem ms) (d_sp d - DEC_F) (d_sp d)
  HE HH ltac:(unfold DEC_F in *; lia) ltac:(lia) AGR) as (HROM & HZB & HRA & HHV).
pose proof (decLO_mchr (nth i (d_tb d) 0) ltac:(lia)) as Hml.
assert (HRAm : range_addressable (aview tfibsegs (w_H Wc) (ms_mem ms)) SHADOW_OFF G_B64
  (mchr_len (nth i (d_tb d) 0) WriterSpec.b64_table)) by (intros x Hx; apply HRA; lia).
assert (HHVm : shadow_hull_vis (aview tfibsegs (w_H Wc) (ms_mem ms)) G_B64
  (mchr_len (nth i (d_tb d) 0) WriterSpec.b64_table)) by exact (decLO_hull_sub _ G_B64 65 _ Hml HHV).
assert (Hamem : amem_range G_B64 (65 + 8)) by (unfold amem_range; left; rewrite C5; unfold G_B64; lia).
assert (Hlen65 : Z.of_nat (length WriterSpec.b64_table) = 65) by (vm_compute; reflexivity).
pose proof HARUm as (_ & HUOK & _).
rewrite (st_ok_restrict_mkst tfibsegs (w_H Wc) Ex ss ms HS Hrv), Hpc.
eapply SRr_bind.
{ apply (fsw_intrin_atU B (d_STKJ d) (d_ot d) (d_FP d) (d_ly d) (d_S d) (d_W d) (unpoison (d_U d) (d_mem d)) (d_md d)
    [] lyc Sc Uc Wc (ms_mem ms) md' k Uc (fun a => spZ (ms_regs ms) - STK_RT_STR <= a < spZ (ms_regs ms))
    (Z_to_bv 64 DEC_RA_MEMCHR) _
    (fun regs2 mem2 md2 => aregs_preserved (ms_regs ms) regs2 /\
       (exists v, getr regs2 10 = w64 v /\
          match zfind (nth i (d_tb d) 0) WriterSpec.b64_table with None => v = 0 | Some j => v = G_B64 + Z.of_nat j end) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (ms_regs ms) - STK_RT_STR <= a < spZ (ms_regs ms)) ->
          aview tfibsegs (w_H Wc) mem2 a = aview tfibsegs (w_H Wc) (ms_mem ms) a)) HJm).
  - eapply SRr_mono;
      [exact (HMEMCHR lyc Sc Uc Wc (ms_regs ms) (ms_mem ms) md' G_B64 (nth i (d_tb d) 0) 65 WriterSpec.b64_table
         HPRE1 HROM R10 R11 ltac:(lia) R12 ltac:(lia) HZB Hlen65 ltac:(unfold G_B64; lia) ltac:(unfold G_B64; lia)
         Hamem HRAm (fun _ => HHVm))|].
    intros W2 c2 _ (EW & regs2 & mem2 & md2 & v0 & Ec & HAR2 & PO2 & HP2 & Hsame & H10v & Hv0 & HR & Hfr & Hgr).
    split; [exact EW|]. exists regs2, mem2, md2.
    split.
    { rewrite Ec. unfold cfg_at, raZ, w64. rewrite R1, unsigned_lit_small by lia. reflexivity. }
    split; [split; [exact HAR2 | split; [exact HUOK | exact PO2]]|].
    split; [exact Hsame|].
    split.
    { intros a Ha Hn. destruct (in_ush Uc (bv_unsigned (Z_to_bv 64 a))) eqn:Eu.
      - apply (aview_unpoison_in tfibsegs). exact Eu.
      - rewrite (aview_unpoison_out tfibsegs (w_H Wc) Uc mem2 a Eu),
          (aview_unpoison_out tfibsegs (w_H Wc) Uc (ms_mem ms) a Eu).
        exact (Hfr a Ha Hn). }
    split.
    { intros a (Hh & b & Hb). split; [exact Hh|]. unfold unpoison in Hb |- *.
      destruct (in_ush Uc (bv_unsigned (Z_to_bv 64 a))); [eexists; reflexivity|].
      destruct (Hgr a (conj Hh (ex_intro _ b Hb))) as (_ & b' & Hb'). exists b'. exact Hb'. }
    split; [exact HP2|]. split; [exists v0; split; [exact H10v | exact HR]|]. exact Hfr.
  - intros a Ha. left; left. rewrite Hspt, FR in Ha. unfold d_STKJ, DEC_F in *. rewrite FS. lia. }
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HARU2 & HP2 & (v & H10 & Hv) & Hfr2).
assert (HSTKR : 128 + STK_RT_STR <= STK_preset_base64_decode) by (rewrite FS, FR; lia).
assert (Hlo : alloc_ceiling <= d_sp d - DEC_F - STK_RT_STR) by (unfold DEC_F; lia).
assert (AG2 : forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp d - DEC_F - STK_RT_STR <= a < d_sp d) ->
  aview tfibsegs (w_H Wc) mem2 a = aview tfibsegs (w_H Wc) memc a).
{ intros a Ha Hn. rewrite (Hfr2 a Ha ltac:(rewrite Hspt; unfold DEC_F in *; lia)).
  apply AGR; [exact Ha | unfold DEC_F in *; lia]. }
pose proof (decLB_keep d q i six pad acc Wc lyc Sc Uc regsc memc mdc k memc mem2 (d_sp d - DEC_F - STK_RT_STR) (d_sp d)
  HE HH (decLB_memf d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HH) Hlo ltac:(lia) AG2) as HM2.
assert (E2x : bv_unsigned (ew Ex 2) = d_sp d - DEC_F)
  by (rewrite (HEx 2%nat ltac:(lia)), (decL_E_reg d q regsc _ 2 2%bv eq_refl); exact Hsp).
destruct (decL_frame_back d q regsc [Z_to_bv 64 (nth i (d_tb d) 0)] Wc ms Ex ss HS ltac:(rewrite Hmem; reflexivity) E2x
  (fun n Hn => HEx n ltac:(lia)) ltac:(lia) ltac:(unfold HEAD in *; lia)) as (HFr1 & HLs1 & HNq1).
assert (KF : forall a, d_sp d - DEC_F <= a < d_sp d ->
  aview tfibsegs (w_H Wc) mem2 a = aview tfibsegs (w_H Wc) (ms_mem ms) a)
  by (intros a Ha; apply Hfr2; [lia | rewrite Hspt; unfold DEC_F in *; lia]).
assert (HFr2 : dec_frame_ok Wc mem2 (d_sp d - DEC_F) (d_regs d)).
{ intros j r Hj. assert (Hj13 : (j < length dec_saved)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  cbv [dec_saved length] in Hj13.
  apply (decLB_val_mem (w_H Wc) (ms_mem ms) mem2 _ 8); [|exact (HFr1 j r Hj)].
  intros kk Hkk. apply KF. unfold DEC_F in *. lia. }
assert (HLs2 : dec_lenp_slot Wc mem2 (d_sp d - DEC_F) (d_lenp d)).
{ unfold dec_lenp_slot in *. apply (decLB_val_mem (w_H Wc) (ms_mem ms) mem2 _ 8); [|exact HLs1].
  intros kk Hkk. apply KF. unfold DEC_F in *. lia. }
assert (HNq2 : dec_nq_slot Wc mem2 (d_sp d - DEC_F) q).
{ unfold dec_nq_slot in *. apply (decLB_val_mem (w_H Wc) (ms_mem ms) mem2 _ 8); [|exact HNq1].
  intros kk Hkk. apply KF. unfold DEC_F in *. lia. }
assert (RK : forall r, In r decLO_kregs -> getr regs2 r = getr regsc r).
{ intros r Hr. cbv [decLO_kregs In] in Hr. repeat (destruct Hr as [<-|Hr]); [..|destruct Hr];
  rewrite (fsw_pres _ _ _ HP2) by decLO_cs;
  lazymatch goal with |- getr _ ?r = _ =>
    let n := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
    apply (GK r n); [vm_compute; reflexivity | lia | reflexivity] end. }
exact (decLO_tail d q i six pad acc Wc lyc Sc Uc regsc memc mdc k regs2 mem2 md2 v HE HH HFREE HIH Hilt Hws H61 HJ2
  HARU2 HM2 HFr2 HLs2 HNq2 RK H10 Hv).
Qed.

Lemma decL_arm_other : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  (forall W3 ly3 S3 U3 regs3 mem3 md3 k3, dec_at_free B d q W3 ly3 S3 U3 regs3 mem3 md3 k3 ->
     SRr tfibsegs W3 (cfg_at tfibsegs A_fuzz_free regs3 mem3 md3) (dec_post B d)) ->
  (forall six' pad' acc' Wc' lyc' Sc' Uc' regsc' memc' mdc' k',
     dec_head B d q (S i) six' pad' acc' Wc' lyc' Sc' Uc' regsc' memc' mdc' k' ->
     SRr tfibsegs Wc' (decL_hcfg regsc' memc' mdc') (dec_post B d)) ->
  (i < length (d_tb d))%nat ->
  WriterSpec.b64_ws (nth i (d_tb d) 0) = false -> nth i (d_tb d) 0 <> 61 ->
  SRr tfibsegs Wc (decL_hcfg regsc memc mdc) (dec_post B d).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH HFREE HIH Hilt Hws H61.
destruct (decL_head_st d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH) as [HS SHOK].
pose proof (decLO_c d i HE Hilt) as Hc.
pose proof HH as HH0. decL_unhead HH0.
pose proof (decLB_sp d HE) as (_ & SP2 & _).
assert (E2 : bv_unsigned (ew (decL_E d q regsc [Z_to_bv 64 (nth i (d_tb d ++ [0]) 0)]) 2) = d_sp d - DEC_F)
  by (rewrite (decL_E_reg d q regsc _ 2 2%bv eq_refl); exact Hsp).
assert (E27 : ew (decL_E d q regsc [Z_to_bv 64 (nth i (d_tb d ++ [0]) 0)]) 27 = Z_to_bv 64 DEC_WSMASK)
  by (rewrite (decL_E_reg d q regsc _ 27 27%bv eq_refl); exact R27).
assert (E26 : ew (decL_E d q regsc [Z_to_bv 64 (nth i (d_tb d ++ [0]) 0)]) 26 = Z_to_bv 64 61)
  by (rewrite (decL_E_reg d q regsc _ 26 26%bv eq_refl); exact R26).
assert (E48 : ew (decL_E d q regsc [Z_to_bv 64 (nth i (d_tb d ++ [0]) 0)]) 48 = Z_to_bv 64 (nth i (d_tb d) 0)).
{ rewrite <- (app_nth1 (d_tb d) [0] 0 Hilt). exact (decL_E_ex d q regsc _ 0). }
unfold dec_J in HJ. unfold decL_hcfg.
(* 0x84cf8 -> 0x84d0c *)
fsw_aj_run_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan.
{ eapply decLO_awr_h; [exact E2 | exact SP2 | reflexivity]. }
pose proof (decLO_meq_h _ d _ memc _ _ HF ltac:(rewrite ?ew_ewset_other by lia; exact E2) (fun a _ _ => eq_refl)
  eq_refl) as MEQ.
clear HF HFr HG.
(* 0x84d0c: bltu s10, c *)
eapply SRr_sym_branch with (c := BC_LTU) (a := SOff 26 0) (b := SOff 48 0); [exact HS | intros Hb HS2 | intros Hb HS2];
  rewrite (decLA_br_ltu _ 26 48 61 (nth i (d_tb d) 0)) in Hb
    by (rewrite ?ew_ewset_other by lia; first [exact E26 | exact E48 | lia]);
  clear HS.
- (* 61 < c: to PC_memchr *)
  fsw_aj_run_to_tokU fsw_wr_tbl_ok HS2 HJ HARU SHOK fs_Bspan PC_memchr.
  { eapply decLO_awr_h; [rewrite ?ew_ewset_other by lia; exact E2 | exact SP2 | reflexivity]. }
  apply (decLO_call d q i six pad acc Wc lyc Sc Uc regsc memc mdc k _ _ _ _ HE HH HFREE HIH Hilt Hws H61 HS2
    ltac:(intros m Hm; rewrite ?ew_ewset_other by lia; reflexivity) eq_refl eq_refl eq_refl eq_refl HJ HARU).
  exact (decLO_meq_h _ d _ memc _ _ HF ltac:(rewrite ?ew_ewset_other by lia; exact E2) MEQ eq_refl).
- (* c <= 61 *)
  apply Z.ltb_ge in Hb.
  fsw_aj_run_tokU fsw_wr_tbl_ok HS2 HJ HARU SHOK fs_Bspan.
  { eapply decLO_awr_h; [rewrite ?ew_ewset_other by lia; exact E2 | exact SP2 | reflexivity]. }
  pose proof (decLO_meq_h _ d _ memc _ _ HF ltac:(rewrite ?ew_ewset_other by lia; exact E2) MEQ eq_refl) as MEQ2.
  clear HF HFr HG MEQ.
  (* 0x84d18: beqz ((mask >> c) & 1), taken: c is no whitespace *)
  eapply SRr_sym_branch with (c := BC_EQ) (a := SAlu ALU_AND (SAlu ALU_SRL (SOff 27 0) (SOff 48 0)) (SLit 1))
    (b := SLit 0); [exact HS2 | intros Hb2 HS3 | intros Hb2 HS3];
    rewrite (decLA_br_ws_eq _ 27 48 (nth i (d_tb d) 0)) in Hb2
      by (rewrite ?ew_ewset_other by lia; first [exact E27 | exact E48 | lia]);
    clear HS2.
  + fsw_aj_run_tokU fsw_wr_tbl_ok HS3 HJ HARU SHOK fs_Bspan.
    { eapply decLO_awr_h; [rewrite ?ew_ewset_other by lia; exact E2 | exact SP2 | reflexivity]. }
    pose proof (decLO_meq_h _ d _ memc _ _ HF ltac:(rewrite ?ew_ewset_other by lia; exact E2) MEQ2 eq_refl) as MEQ3.
    clear HF HFr HG MEQ2.
    (* 0x84d2c: c <> 61, taken *)
    eapply SRr_sym_branch with (c := BC_NE) (a := SOff 48 0) (b := SOff 26 0); [exact HS3 | intros Hb3 HS4 | intros Hb3 HS4];
      rewrite (decLA_br_ne _ 48 26 (nth i (d_tb d) 0) 61) in Hb3
        by (rewrite ?ew_ewset_other by lia; first [exact E48 | exact E26 | lia]);
      clear HS3.
    * fsw_aj_run_tokU fsw_wr_tbl_ok HS4 HJ HARU SHOK fs_Bspan.
      { eapply decLO_awr_h; [rewrite ?ew_ewset_other by lia; exact E2 | exact SP2 | reflexivity]. }
      pose proof (decLO_meq_h _ d _ memc _ _ HF ltac:(rewrite ?ew_ewset_other by lia; exact E2) MEQ3 eq_refl) as MEQ4.
      clear HF HFr HG MEQ3.
      (* 0x84d40: c == 0, not taken *)
      eapply SRr_sym_branch with (c := BC_EQ) (a := SOff 48 0) (b := SLit 0); [exact HS4 | intros Hb4 HS5 | intros Hb4 HS5];
        rewrite (decLA_br_eq0 _ 48 (nth i (d_tb d) 0)) in Hb4
          by (rewrite ?ew_ewset_other by lia; first [exact E48 | lia]);
        clear HS4.
      -- exfalso. apply Z.eqb_eq in Hb4. lia.
      -- fsw_aj_run_to_tokU fsw_wr_tbl_ok HS5 HJ HARU SHOK fs_Bspan PC_memchr.
         { eapply decLO_awr_h; [rewrite ?ew_ewset_other by lia; exact E2 | exact SP2 | reflexivity]. }
         apply (decLO_call d q i six pad acc Wc lyc Sc Uc regsc memc mdc k _ _ _ _ HE HH HFREE HIH Hilt Hws H61 HS5
           ltac:(intros m Hm; rewrite ?ew_ewset_other by lia; reflexivity) eq_refl eq_refl eq_refl eq_refl HJ HARU).
         exact (decLO_meq_h _ d _ memc _ _ HF ltac:(rewrite ?ew_ewset_other by lia; exact E2) MEQ4 eq_refl).
    * exfalso. apply Bool.negb_false_iff, Z.eqb_eq in Hb3. exact (H61 Hb3).
  + exfalso. rewrite Hws in Hb2. discriminate Hb2.
Qed.

(* ---- the NUL arm (port of lib/A/FSW_dec_L5.v, decode_spec's placement) ---- *)
Definition decLN_addf (ss : sstate) (n : nat) (f : afact) : sstate :=
  mkSS (ss_pc ss) (ss_regs ss) (ss_mem ss) (ss_resv ss)
    (mkFacts ((n, f) :: f_atoms (ss_facts ss)) (f_conds (ss_facts ss)) (f_alias (ss_facts ss))).
Lemma decLN_add_atom : forall E ss ms n f,
  st_ok tfibsegs E ss ms -> afact_ok E n f -> st_ok tfibsegs E (decLN_addf ss n f) ms.
Proof.
intros E ss ms n f HS Hf. unfold decLN_addf. apply (st_ok_facts tfibsegs E ss ms); [exact HS|].
apply facts_ok_add_atom; [exact (st_ok_facts_ok tfibsegs E ss ms HS) | exact Hf].
Qed.
Lemma decLN_af : forall E n v lo hi, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi ->
  afact_ok E n (mkAF lo hi 0).
Proof.
intros E n v lo hi Hn Hv Hr. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Hn, (wz v Hv).
split; [exact Hr|]. rewrite Z.pow_0_r, Z.mod_1_r. split; [reflexivity | lia].
Qed.
Lemma decLN_af1 : forall E n v lo hi, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi -> v mod 2 = 0 ->
  afact_ok E n (mkAF lo hi 1).
Proof.
intros E n v lo hi Hn Hv Hr Hm. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite Hn, (wz v Hv).
split; [exact Hr|]. change (2 ^ 1) with 2. split; [exact Hm | lia].
Qed.
Lemma decLN_meq_step : forall E (rs : list YP09.region) (m0 m1 m2 : word -> option byte) lo hi,
  frame_of E rs m1 m2 ->
  (forall r a, In r rs ->
     base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r -> lo <= a < hi) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> m1 (Z_to_bv 64 a) = m0 (Z_to_bv 64 a)) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> m2 (Z_to_bv 64 a) = m0 (Z_to_bv 64 a).
Proof.
intros E rs m0 m1 m2 lo hi HF HP M01 a Ha Hn. rewrite <- (M01 a Ha Hn). apply HF.
intros (r & Hin & Hr). rewrite (wz a Ha) in Hr. exact (Hn (HP r a Hin Hr)).
Qed.
Lemma decLN_awr_ro : forall E rs STK sp0 FP bl0 blc ly own fr0,
  Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs -> awr_ok tfibsegs B E rs STK sp0 FP bl0 blc ly own fr0.
Proof.
intros E rs. induction rs as [|r rs IH]; intros STK sp0 FP bl0 blc ly own fr0 HF; [apply awr_ok_nil|].
inversion HF as [|? ? Hr Hrs]; subst. apply awr_ok_cons_ro; [exact Hr | exact (IH _ _ _ _ _ _ _ _ Hrs)].
Qed.
Lemma decLN_awr0 : forall E d rs bl0 blc ly fr0,
  bv_unsigned (ew E 2) = d_sp d - DEC_F -> d_sp d <= d_ot d ->
  awr_ok tfibsegs B E rs (d_STKJ d) (d_ot d) (d_FP d) bl0 blc ly [] fr0 ->
  awr_ok tfibsegs B E (fsT_ret_regions DEC_F decL_cs rs) (d_STKJ d) (d_ot d) (d_FP d) bl0 blc ly [] fr0.
Proof.
intros E d rs bl0 blc ly fr0 E2 Hspot Hrs.
assert (HSTK : 128 <= STK_preset_base64_decode) by (vm_compute; discriminate).
unfold fsT_ret_regions.
eapply awr_ok_cons_stack_off with (n := 2%nat) (d := d_sp d - DEC_F - d_ot d);
  [reflexivity | rewrite E2; lia
   | cbv [fstk_ret YP09.r_wlo]; unfold d_STKJ, DEC_F in *; lia
   | cbv [fstk_ret YP09.r_whi]; unfold DEC_F in *; lia |].
apply awr_ok_cons_ro; [cbv [fs_got_region YP09.r_wlo YP09.r_whi]; lia|].
apply awr_ok_cons_ro; [cbv [fs_bcell_region YP09.r_wlo YP09.r_whi]; lia|].
exact Hrs.
Qed.
(* the frame obligations of a run from a loop state: every write window is the frame [sp - 128, sp) *)
Ltac decLN_fo E2 :=
  let r := fresh "r" in let a := fresh "a" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros r a Hin Hr;
  cbv [decLN_addf decL_hss fss_retT fsT_ret_regions app add_cond ss_mem] in Hin;
  repeat (destruct Hin as [<-|Hin];
    [ cbv [fstk_ret fs_got_region fs_bcell_region decL_txr YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      rewrite ?ew_ewset_other in Hr by lia; try rewrite E2 in Hr; unfold DEC_F in *; lia |]);
  destruct Hin.
Ltac decLN_awrt E2 :=
  cbv [decLN_addf decL_hss fss_retT ss_mem add_cond];
  lazymatch type of E2 with
  | bv_unsigned (ew _ 2) = ?v =>
    lazymatch goal with
    | |- awr_ok _ _ ?Ex _ _ _ _ _ _ _ _ _ =>
      let X2 := fresh "X2" in
      assert (X2 : bv_unsigned (ew Ex 2) = v) by (rewrite ?ew_ewset_other by lia; exact E2);
      eapply (decLN_awr0 Ex _ [decL_txr] _ _ _ _ X2);
      [ lia
      | apply decLN_awr_ro; constructor; [cbv [decL_txr YP09.r_wlo YP09.r_whi]; lia | constructor] ]
    end
  end.

Lemma decLN_rehead : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k Ex ex ss ms md',
  dec_entry_ok B d ->
  dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  st_ok tfibsegs Ex ss (restrict (w_H Wc) ms) ->
  nth_error (ss_mem ss) 0 = Some (fstk_ret DEC_F decL_cs) ->
  (forall n, (n < 48)%nat -> ew Ex n = ew (decL_E d q regsc ex) n) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) decLO_kregs = true ->
  dec_J B d lyc Sc Wc Uc (ms_mem ms) md' k -> ARU tfibsegs B lyc Sc Uc Wc (ms_mem ms) md' ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp d - DEC_F <= a < d_sp d) ->
     ms_mem ms (Z_to_bv 64 a) = memc (Z_to_bv 64 a)) ->
  dec_head B d q i six pad acc Wc lyc Sc Uc (ms_regs ms) (ms_mem ms) md' k.
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k Ex ex ss ms md' HE HH HS Hnth HEx HRb HJ2 HARU2 MEQ.
pose proof (decLB_sp d HE) as (SP1 & SP2 & SP3).
pose proof (decL_lenp_range d HE) as (L1 & L2 & _).
pose proof (decLB_q d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH) as (_ & Q1 & Q2 & _).
pose proof (decL_dn_pos d) as Hdn.
pose proof asan_consts as (C1 & _).
assert (HR : forall r : bv 5, In r decLO_kregs -> sr_get (ss_regs ss) r = SOff (Z.to_nat (bv_unsigned r)) 0).
{ intros r Hin. apply sv_eqb_eq. exact (proj1 (forallb_forall _ _) HRb r Hin). }
pose proof HH as HH0. decL_unhead HH.
assert (RG : forall (r : bv 5), In r decLO_kregs -> getr (ms_regs ms) r = getr regsc r).
{ intros r Hin.
  rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) Ex ss ms r HS), (HR r Hin).
  rewrite fsw_SOff0, (HEx (Z.to_nat (bv_unsigned r)) ltac:(pose proof (u5_range r); lia)).
  rewrite (decL_E_reg d q regsc ex (Z.to_nat (bv_unsigned r)) r ltac:(pose proof (u5_range r); lia)).
  reflexivity. }
assert (E2 : bv_unsigned (ew Ex 2) = d_sp d - DEC_F)
  by (rewrite (HEx 2%nat ltac:(lia)), (decL_E_reg d q regsc ex 2 2%bv eq_refl); exact Hsp).
destruct (decL_frame_back d q regsc ex Wc ms Ex ss HS Hnth E2
  ltac:(intros n Hn; apply HEx; lia) ltac:(lia) ltac:(unfold HEAD in *; lia)) as (HFr' & HLs' & HNq').
apply (decL_mk_head d q i six pad acc Wc lyc Sc Uc regsc memc mdc k i six pad acc (ms_regs ms) (ms_mem ms) md' HH0
  HJ2 HARU2);
  [ apply (decLB_keep d q i six pad acc Wc lyc Sc Uc regsc memc mdc k memc (ms_mem ms)
             (d_sp d - DEC_F) (d_sp d) HE HH0 (decLB_memf d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HH0));
    [ unfold DEC_F; lia | lia
    | intros a Ha Hna; apply (aview_at tfibsegs); exact (MEQ a Ha Hna) ]
  | exact HFr' | exact HLs' | exact HNq'
  | unfold spZ; rewrite (RG 2%bv ltac:(decLO_in)); exact Hsp
  | rewrite (RG 3%bv ltac:(decLO_in)); exact R3
  | rewrite (RG 4%bv ltac:(decLO_in)); exact R4
  | rewrite (RG 8%bv ltac:(decLO_in)); exact R8
  | rewrite (RG 9%bv ltac:(decLO_in)); exact R9
  | rewrite (RG 18%bv ltac:(decLO_in)); exact R18
  | rewrite (RG 19%bv ltac:(decLO_in)); exact R19
  | rewrite (RG 20%bv ltac:(decLO_in)); exact R20
  | rewrite (RG 21%bv ltac:(decLO_in)); exact R21
  | rewrite (RG 22%bv ltac:(decLO_in)); exact R22
  | exact Hacc
  | rewrite (RG 23%bv ltac:(decLO_in)); exact R23
  | rewrite (RG 24%bv ltac:(decLO_in)); exact R24
  | rewrite (RG 25%bv ltac:(decLO_in)); exact R25
  | rewrite (RG 26%bv ltac:(decLO_in)); exact R26
  | rewrite (RG 27%bv ltac:(decLO_in)); exact R27
  | exact Hi | exact Hpad | exact Hsix | exact Hsix64 | exact Hlast | exact Hscan ].
Qed.

Lemma decLN_free : forall d q i six pad acc Wc lyc Sc Uc md' k Ex ss ms,
  dec_head B d q i six pad acc Wc lyc Sc Uc (ms_regs ms) (ms_mem ms) md' k ->
  (forall W3 ly3 S3 U3 regs3 mem3 md3 k3, dec_at_free B d q W3 ly3 S3 U3 regs3 mem3 md3 k3 ->
     SRr tfibsegs W3 (cfg_at tfibsegs A_fuzz_free regs3 mem3 md3) (dec_post B d)) ->
  st_ok tfibsegs Ex ss (restrict (w_H Wc) ms) -> ss_resv ss = None -> ss_pc ss = A_fuzz_free ->
  sr_get (ss_regs ss) 10 = SOff 9 0 -> sr_get (ss_regs ss) 1 = SLit DEC_RA_FREE ->
  ew Ex 9 = w64 q ->
  WriterSpec.b64_dec (d_tb d) = None ->
  SRr tfibsegs Wc (mkCfg ms md') (dec_post B d).
Proof.
intros d q i six pad acc Wc lyc Sc Uc md' k Ex ss ms HH HFREE HS Hrv Hpc S10 S1 E9 Hdec.
pose proof HH as HH0. decL_unhead HH.
assert (R10 : getr (ms_regs ms) 10 = w64 q)
  by (exact (decL_reg (w_H Wc) Ex ss ms 10%bv _ _ HS S10 ltac:(rewrite fsw_SOff0; exact E9))).
assert (R1 : getr (ms_regs ms) 1 = w64 DEC_RA_FREE)
  by (exact (fsw_reg_lit (w_H Wc) Ex ss ms 1%bv DEC_RA_FREE HS S1 ltac:(unfold DEC_RA_FREE; lia))).
exact (decL_free d q i six pad acc Wc lyc Sc Uc (ms_regs ms) (ms_mem ms) md' k Ex ss ms md' HH0 HFREE HS Hrv Hpc
  HJ HARU (decLB_memf d q i six pad acc Wc lyc Sc Uc (ms_regs ms) (ms_mem ms) md' k HH0) HFr HLs R10 R1 Hsp R3 R4 R8
  Hdec).
Qed.

Lemma decLN_exit : forall d q six pad acc Wc lyc Sc Uc regsc memc mdc k,
  dec_entry_ok B d ->
  dec_head B d q (length (d_tb d)) six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  (forall W3 ly3 S3 U3 regs3 mem3 md3 k3, dec_at_free B d q W3 ly3 S3 U3 regs3 mem3 md3 k3 ->
     SRr tfibsegs W3 (cfg_at tfibsegs A_fuzz_free regs3 mem3 md3) (dec_post B d)) ->
  (forall regs' mem' md',
     dec_head B d q (length (d_tb d)) six pad acc Wc lyc Sc Uc regs' mem' md' k ->
     getr regs' 10 = w64 2 -> pad <= 2 -> WriterSpec.six_tail_ok six = true ->
     SRr tfibsegs Wc (mkCfg (YK11.mkst regs' (Z_to_bv 64 DEC_EXIT_PAD) mem' (YK11.seg_rom tfibsegs)) md')
       (dec_post B d)) ->
  SRr tfibsegs Wc (mkCfg (YK11.mkst regsc (Z_to_bv 64 DEC_HEAD) memc (YK11.seg_rom tfibsegs)) mdc) (dec_post B d).
Proof.
intros d q six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH HFREE HCONT.
pose proof (decLB_sp d HE) as (SP1 & SP2 & SP3).
pose proof HE as (_ & _ & _ & _ & _ & _ & _ & _ & Htb & _).
assert (HSTK : 128 <= STK_preset_base64_decode) by (vm_compute; discriminate).
assert (Hc0 : nth (length (d_tb d)) (d_tb d ++ [0]) 0 = 0)
  by (rewrite app_nth2 by lia; rewrite Nat.sub_diag; reflexivity).
destruct (decL_head_st d q (length (d_tb d)) six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH) as (HS & SHOK).
cbv zeta in HS, SHOK. rewrite Hc0 in HS, SHOK.
pose proof HH as HH0. decL_unhead HH. unfold dec_J in HJ.
set (E := decL_E d q regsc [Z_to_bv 64 0]) in *.
assert (EE : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regsc r)
  by (intros n r Hn; unfold E; exact (decL_E_reg d q regsc _ n r Hn)).
assert (E2 : bv_unsigned (ew E 2) = d_sp d - DEC_F) by (rewrite (EE 2%nat 2%bv eq_refl); exact Hsp).
assert (E9 : ew E 9 = Z_to_bv 64 q) by (rewrite (EE 9%nat 9%bv eq_refl); exact R9).
assert (E22 : ew E 22 = Z_to_bv 64 acc) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (E23 : ew E 23 = Z_to_bv 64 (6 * Z.of_nat (length six) mod 8)) by (rewrite (EE 23%nat 23%bv eq_refl); exact R23).
assert (E24 : ew E 24 = Z_to_bv 64 pad) by (rewrite (EE 24%nat 24%bv eq_refl); exact R24).
assert (E27 : ew E 27 = Z_to_bv 64 DEC_WSMASK) by (rewrite (EE 27%nat 27%bv eq_refl); exact R27).
assert (E48 : ew E 48 = Z_to_bv 64 0) by (unfold E; exact (decL_E_ex d q regsc _ 0)).
assert (HDEC : WriterSpec.b64_dec (d_tb d) = decLA_out pad six (skipn (length (d_tb d)) (d_tb d))) by exact Hscan.
rewrite decLA_skipn_end, decLA_out_nil in HDEC.
pose proof (decLA_tail six acc Hlast) as HTAIL.
assert (Hbits : 0 <= 6 * Z.of_nat (length six) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
assert (Hbits2 : (6 * Z.of_nat (length six) mod 8) mod 2 = 0) by (Z.div_mod_to_equations; lia).
assert (Hpad64 : 0 <= pad < 2 ^ 63) by lia.
(* ---- run 1: the head to the whitespace test 0x84d18 ---- *)
pose proof (decLN_add_atom E decL_hss _ 48%nat (mkAF 0 0 0) HS
  (decLN_af E 48%nat 0 0 0 E48 ltac:(lia) ltac:(lia))) as HS1.
clear HS.
fsw_aj_run_tokU fsw_wr_tbl_ok HS1 HJ HARU SHOK fs_Bspan.
{ cbv [decLN_addf decL_hss fss_retT ss_mem].
  apply (decLN_awr0 E d [decL_txr] _ _ _ _ E2 ltac:(lia)).
  apply decLN_awr_ro. constructor; [cbv [decL_txr YP09.r_wlo YP09.r_whi]; lia | constructor]. }
pose proof (decLN_meq_step _ _ memc _ _ (d_sp d - DEC_F) (d_sp d) HF ltac:(decLN_fo E2) (fun _ _ _ => eq_refl)) as MEQ1.
clear HF HG.
eapply (SRr_sym_branch tfibsegs Wc _ _ _ _ _ BC_EQ
          (SAlu ALU_AND (SAlu ALU_SRL (SOff 27 0) (SOff 48 0)) (SLit 1)) (SLit 0));
  [exact HS1 | intros Hb HS2 | intros Hb HS2];
  rewrite (decLA_br_ws_eq _ 27 48 0) in Hb by (rewrite ?ew_ewset_other by lia; first [exact E27 | exact E48 | lia]);
  clear HS1.
2:{ vm_compute in Hb. discriminate Hb. }
(* not whitespace: run 2 to the `c == 0` test 0x84d40 *)
fsw_aj_run_tokU fsw_wr_tbl_ok HS2 HJ HARU SHOK fs_Bspan.
{ decLN_awrt E2. }
pose proof (decLN_meq_step _ _ memc _ _ (d_sp d - DEC_F) (d_sp d) HF ltac:(decLN_fo E2) MEQ1) as MEQ2.
clear HF HG.
eapply (SRr_sym_branch tfibsegs Wc _ _ _ _ _ BC_EQ (SOff 48 0) (SLit 0));
  [exact HS2 | intros Hb2 HS3 | intros Hb2 HS3];
  rewrite (decLA_br_eq0 _ 48 0) in Hb2 by (rewrite ?ew_ewset_other by lia; first [exact E48 | lia]);
  clear HS2.
2:{ cbn in Hb2. discriminate Hb2. }
(* the NUL: the loop exits. bits = 6 refuses at once, bits <= 4 goes on to the acc test *)
assert (HB : 6 * Z.of_nat (length six) mod 8 <= 4 \/ 6 * Z.of_nat (length six) mod 8 = 6)
  by (pose proof (decLA_bits_cases (Z.of_nat (length six)) ltac:(lia)); lia).
destruct HB as [HB|HB].
- (* bits <= 4: run 3 to the acc test 0x84e2c *)
  pose proof (decLN_add_atom _ _ _ 23%nat (mkAF 0 4 1) HS3
    (decLN_af1 _ 23%nat (6 * Z.of_nat (length six) mod 8) 0 4
       ltac:(rewrite ?ew_ewset_other by lia; exact E23) ltac:(lia) ltac:(lia) Hbits2)) as HS4.
  clear HS3.
  fsw_aj_run_tokU fsw_wr_tbl_ok HS4 HJ HARU SHOK fs_Bspan.
  { decLN_awrt E2. }
  pose proof (decLN_meq_step _ _ memc _ _ (d_sp d - DEC_F) (d_sp d) HF ltac:(decLN_fo E2) MEQ2) as MEQ3.
  clear HF HG.
  eapply (SRr_sym_branch tfibsegs Wc _ _ _ _ _ BC_NE
    (SAlu ALU_AND (SOff 22 0) (SAlu ALU_XOR (SAluw ALU_SLL (SLit 18446744073709551615) (SOff 23 0)) (SLit (-1))))
    (SLit 0));
    [exact HS4 | intros Hb3 HS5 | intros Hb3 HS5];
    rewrite (decLA_br_exit_and _ 22 23 acc (6 * Z.of_nat (length six) mod 8)) in Hb3
      by (rewrite ?ew_ewset_other by lia; first [exact E22 | exact E23 | lia]);
    clear HS4.
  + (* the unused low bits of acc are not 0: the tail refuses *)
    assert (HNONE : WriterSpec.b64_dec (d_tb d) = None).
    { rewrite HDEC, HTAIL.
      replace (acc mod 2 ^ (6 * Z.of_nat (length six) mod 8) =? 0) with false
        by (symmetry; apply negb_true_iff in Hb3; exact Hb3).
      rewrite andb_false_r, andb_false_r. reflexivity. }
    fsw_aj_run_tokU fsw_wr_tbl_ok HS5 HJ HARU SHOK fs_Bspan.
    { decLN_awrt E2. }
    pose proof (decLN_meq_step _ _ memc _ _ (d_sp d - DEC_F) (d_sp d) HF ltac:(decLN_fo E2) MEQ3) as MEQ4.
    eapply (decLN_free d q (length (d_tb d)) six pad acc Wc lyc Sc Uc _ k _ _ _);
      [ apply (decLN_rehead d q (length (d_tb d)) six pad acc Wc lyc Sc Uc regsc memc mdc k _ [Z_to_bv 64 0] _ _ _
                 HE HH0 HS5 ltac:(vm_compute; reflexivity)
                 ltac:(intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity)
                 ltac:(vm_compute; reflexivity) HJ HARU MEQ4)
      | exact HFREE | exact HS5 | vm_compute; reflexivity | vm_compute; reflexivity
      | vm_compute; reflexivity | vm_compute; reflexivity | rewrite ?ew_ewset_other by lia; exact E9 | exact HNONE ].
  + (* the low bits are 0: run 4 to DEC_EXIT_PAD *)
    assert (HTOK : WriterSpec.six_tail_ok six = true).
    { rewrite HTAIL. apply negb_false_iff in Hb3. rewrite Hb3, andb_true_r.
      apply Z.leb_le. lia. }
    fsw_aj_run_tokU fsw_wr_tbl_ok HS5 HJ HARU SHOK fs_Bspan.
    { decLN_awrt E2. }
    pose proof (decLN_meq_step _ _ memc _ _ (d_sp d - DEC_F) (d_sp d) HF ltac:(decLN_fo E2) MEQ3) as MEQ4.
    clear HF HG.
    eapply (SRr_sym_branch tfibsegs Wc _ _ _ _ _ BC_LT (SLit 2) (SOff 24 0));
      [exact HS5 | intros Hb4 HS6 | intros Hb4 HS6];
      rewrite (decLA_br_lt_lit _ 24 pad 2) in Hb4 by (rewrite ?ew_ewset_other by lia; first [exact E24 | lia]);
      clear HS5.
    * (* 2 < pad: the tail refuses *)
      apply Z.ltb_lt in Hb4.
      assert (HNONE : WriterSpec.b64_dec (d_tb d) = None).
      { rewrite HDEC. replace (pad <=? 2) with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
      fsw_aj_run_tokU fsw_wr_tbl_ok HS6 HJ HARU SHOK fs_Bspan.
      { decLN_awrt E2. }
      pose proof (decLN_meq_step _ _ memc _ _ (d_sp d - DEC_F) (d_sp d) HF ltac:(decLN_fo E2) MEQ4) as MEQ5.
      eapply (decLN_free d q (length (d_tb d)) six pad acc Wc lyc Sc Uc _ k _ _ _);
        [ apply (decLN_rehead d q (length (d_tb d)) six pad acc Wc lyc Sc Uc regsc memc mdc k _ [Z_to_bv 64 0] _ _ _
                   HE HH0 HS6 ltac:(vm_compute; reflexivity)
                   ltac:(intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity)
                   ltac:(vm_compute; reflexivity) HJ HARU MEQ5)
        | exact HFREE | exact HS6 | vm_compute; reflexivity | vm_compute; reflexivity
        | vm_compute; reflexivity | vm_compute; reflexivity | rewrite ?ew_ewset_other by lia; exact E9 | exact HNONE ].
    * (* pad <= 2: the success tail, at DEC_EXIT_PAD with a0 = 2 *)
      apply Z.ltb_ge in Hb4.
      rewrite (st_ok_restrict_mkst tfibsegs (w_H Wc) _ _ _ HS6 ltac:(vm_compute; reflexivity)).
      apply (HCONT _ _ _);
        [ apply (decLN_rehead d q (length (d_tb d)) six pad acc Wc lyc Sc Uc regsc memc mdc k _ [Z_to_bv 64 0] _ _ _
                   HE HH0 HS6 ltac:(vm_compute; reflexivity)
                   ltac:(intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity)
                   ltac:(vm_compute; reflexivity) HJ HARU MEQ4)
        | exact (fsw_reg_lit (w_H Wc) _ _ _ 10%bv 2 HS6 ltac:(vm_compute; reflexivity) ltac:(lia))
        | exact Hb4 | exact HTOK ].
- (* bits = 6: the tail refuses at 0x84dcc *)
  pose proof (decLN_add_atom _ _ _ 23%nat (mkAF 6 6 1) HS3
    (decLN_af1 _ 23%nat (6 * Z.of_nat (length six) mod 8) 6 6
       ltac:(rewrite ?ew_ewset_other by lia; exact E23) ltac:(lia) ltac:(lia) Hbits2)) as HS4.
  assert (HNONE : WriterSpec.b64_dec (d_tb d) = None).
  { rewrite HDEC, HTAIL, HB. replace (6 <=? 5) with false by reflexivity.
    rewrite andb_false_l, andb_false_r. reflexivity. }
  clear HS3.
  fsw_aj_run_tokU fsw_wr_tbl_ok HS4 HJ HARU SHOK fs_Bspan.
  { decLN_awrt E2. }
  pose proof (decLN_meq_step _ _ memc _ _ (d_sp d - DEC_F) (d_sp d) HF ltac:(decLN_fo E2) MEQ2) as MEQ3.
  eapply (decLN_free d q (length (d_tb d)) six pad acc Wc lyc Sc Uc _ k _ _ _);
    [ apply (decLN_rehead d q (length (d_tb d)) six pad acc Wc lyc Sc Uc regsc memc mdc k _ [Z_to_bv 64 0] _ _ _
               HE HH0 HS4 ltac:(vm_compute; reflexivity)
               ltac:(intros n Hn; rewrite ?ew_ewset_other by lia; reflexivity)
               ltac:(vm_compute; reflexivity) HJ HARU MEQ3)
    | exact HFREE | exact HS4 | vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity | vm_compute; reflexivity | rewrite ?ew_ewset_other by lia; exact E9 | exact HNONE ].
Qed.

Lemma decLN_succ_rs : forall d q six pad acc Wc lyc Sc Uc regs2 mem2 md2 k,
  dec_entry_ok B d ->
  dec_head B d q (length (d_tb d)) six pad acc Wc lyc Sc Uc regs2 mem2 md2 k ->
  getr regs2 10 = w64 2 -> pad <= 2 -> WriterSpec.six_tail_ok six = true ->
  SRr tfibsegs Wc (mkCfg (YK11.mkst regs2 (Z_to_bv 64 DEC_EXIT_PAD) mem2 (YK11.seg_rom tfibsegs)) md2)
    (dec_post B d).
Proof.
intros d q six pad acc Wc lyc Sc Uc regs2 mem2 md2 k HE HH R10 Hpad2 HTOK.
pose proof asan_consts as (C1 & _ & _ & _).
pose proof (decLB_sp d HE) as (SP1 & SP2 & SP3).
pose proof (decLB_q d q (length (d_tb d)) six pad acc Wc lyc Sc Uc regs2 mem2 md2 k HE HH)
  as (Q16 & Q1 & Q2 & Qn & _).
pose proof (decL_dn_pos d) as Hdn.
pose proof (decLB_lenp d q (length (d_tb d)) six pad acc Wc lyc Sc Uc regs2 mem2 md2 k HE HH)
  as (LP1 & LP2 & LP3 & LP4 & LP5 & LP6 & LRA & LW).
pose proof HH as HH0. decL_unhead HH. unfold dec_J in HJ.
pose proof (decL_atoms_k d q (length (d_tb d)) six pad acc Wc lyc Sc Uc regs2 mem2 md2 k regs2 [] 0 2 0 6 HE HH0
  (fun r _ => eq_refl) ltac:(lia)
  ltac:(destruct (decLA_bits_cases (Z.of_nat (length six)) ltac:(lia)) as [X|[X|[X|X]]]; lia)) as HGF.
pose proof HE as (HPRE & _ & _ & _ & _ & _ & _ & _ & Htb & _ & _ & _ & _ & _ & _ & _ & HLV & HCNT & HPL).
destruct HPL as (HFP & _).
pose proof (proj1 HPRE) as ((_ & HRET & _) & _).
pose proof HKe as (Kv & Kw & Kc & Kr).
pose proof Hglob as (_ & _ & _ & _ & GL1 & GL2 & GL3 & GL4).
set (E := decL_E d q regs2 []) in *.
assert (E2 : bv_unsigned (ew E 2) = d_sp d - DEC_F)
  by (unfold E; rewrite (decL_E_reg d q regs2 [] 2 2%bv eq_refl); exact Hsp).
assert (E9 : ew E 9 = Z_to_bv 64 q)
  by (unfold E; rewrite (decL_E_reg d q regs2 [] 9 9%bv eq_refl); exact R9).
assert (E20 : ew E 20 = Z_to_bv 64 SHADOW_OFF)
  by (unfold E; rewrite (decL_E_reg d q regs2 [] 20 20%bv eq_refl); exact R20).
assert (E21 : ew E 21 = Z_to_bv 64 (Z.of_nat (length (WriterSpec.six_bytes six))))
  by (unfold E; rewrite (decL_E_reg d q regs2 [] 21 21%bv eq_refl); exact R21).
assert (E33 : ew E 33 = Z_to_bv 64 (d_lenp d)) by (unfold E; exact (decL_E_lenp d q regs2 [])).
assert (E33u : bv_unsigned (ew E 33) = d_lenp d) by (rewrite E33; apply wz; lia).
pose proof (WriterSpecFacts.six_bytes_length six) as Hnb.
assert (Hn64 : 0 <= Z.of_nat (length (WriterSpec.six_bytes six)) < 2 ^ 64) by lia.
assert (HS : st_ok tfibsegs E (decLN_addf decL_lss 10 (mkAF 2 2 0))
  (restrict (w_H Wc) (YK11.mkst regs2 (Z_to_bv 64 DEC_EXIT_PAD) mem2 (YK11.seg_rom tfibsegs)))).
{ apply decLN_add_atom;
    [| apply (decLN_af E 10%nat 2 2 2); [unfold E; rewrite (decL_E_reg d q regs2 [] 10 10%bv eq_refl); exact R10
       | lia | lia]].
  unfold decL_lss.
  apply (decL_build d q Wc lyc Sc Uc regs2 mem2 md2 k [] DEC_EXIT_PAD [decL_lpr] decL_lgf HE HJ HARU
    Hsp HFr HLs HNq ltac:(unfold HEAD in *; lia)).
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    unfold decL_lpr, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    fold E. rewrite E33u. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply LW. lia.
  - fold E. apply pairwise_disjoint_of_extents.
    unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, decL_lpr, extent_of_region.
    cbn [map app YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, E33u.
    unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, DEC_F in *.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia].
  - unfold decL_lgf. cbn [atoms_ok]. split; [|exact HGF].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E. rewrite E33u.
    change (2 ^ 3) with 8. split; [lia | split; [exact LP3 | lia]]. }
assert (SHOK : sh_ok tfibsegs decL_Bx decL_lSH E (mrestrict (w_H Wc) mem2)).
{ unfold sh_ok, decL_lSH. constructor; [|constructor].
  apply (shent_ok_of_range tfibsegs (w_H Wc) mem2 E decL_Bx 33%nat (d_lenp d) 8 (d_lenp d) 0 8 LRA).
  - unfold decL_Bx. apply (U_atom E 20 SHADOW_OFF); [exact E20 | unfold SHADOW_OFF; lia].
  - apply (U_atom E 33 (d_lenp d)); [exact E33 | lia].
  - lia.
  - lia.
  - intros x Hx. cbn in Hx. unfold SHADOW_OFF, kHighMemBeg, kLowShadowBeg in *. lia. }
fsw_aj_run_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan.
- cbv [decLN_addf decL_lss fss_retT ss_mem].
  apply (decLN_awr0 E d [decL_lpr] _ _ _ _ E2 ltac:(lia)).
  eapply awr_ok_cons_gen with (k := 33%nat) (b := d_lenp d);
    [ reflexivity | exact E33u
    | cbv [decL_lpr YP09.r_wlo YP09.r_whi]; intros a Ha; left; left; unfold d_STKJ;
      assert (HSTK0 : 0 <= STK_preset_base64_decode) by (vm_compute; discriminate); lia
    | apply awr_ok_nil ].
- subst k. subst Uc.
  assert (FR : forall a, 0 <= a < 2 ^ 64 ->
    ~ ((d_sp d - DEC_F <= a < d_sp d) \/ (d_lenp d <= a < d_lenp d + 8)) ->
    ms_mem ms (Z_to_bv 64 a) = mem2 (Z_to_bv 64 a)).
  { intros a Ha HnP. apply HF. intros (r & Hin & Hr). rewrite (wz a Ha) in Hr. apply HnP.
    cbv [decLN_addf decL_lss fss_retT ss_mem fsT_ret_regions app In] in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
      cbv [fstk_ret fs_got_region fs_bcell_region decL_lpr
           YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      [ rewrite E2 in Hr; left; unfold DEC_F in *; lia | lia | lia | rewrite E33u in Hr; right; lia ]. }
  assert (SB : same_below mem2 (ms_mem ms) alloc_ceiling)
    by (intros x Hx; apply FR; [lia | unfold DEC_F in *; lia]).
  assert (E47 : ew E 47 = getr (d_regs d) 1%bv)
    by (unfold E; change 47%nat with (35 + 12)%nat; rewrite (decLN_E_sav d q regs2 [] 12%nat ltac:(lia));
        reflexivity).
  assert (E2w : ew E 2 = w64 (d_sp d - DEC_F))
    by (unfold w64; rewrite <- E2; symmetry; apply Z_to_bv_bv_unsigned).
  assert (R1F : getr (ms_regs ms) 1 = getr (d_regs d) 1)
    by (exact (decL_reg (w_H Wc) E _ ms 1%bv (SOff 47 0) _ HS ltac:(vm_compute; reflexivity)
                 ltac:(rewrite fsw_SOff0; exact E47))).
  assert (R10F : getr (ms_regs ms) 10 = w64 q)
    by (exact (decL_reg (w_H Wc) E _ ms 10%bv (SOff 9 0) _ HS ltac:(vm_compute; reflexivity)
                 ltac:(rewrite fsw_SOff0; exact E9))).
  assert (HPRES : aregs_preserved (d_regs d) (ms_regs ms)).
  { lazymatch type of HS with
    | st_ok _ _ ?ssf _ =>
      apply (fsw_preserved (w_H Wc) E ssf ms (d_regs d) (fun r : bv 5 => sr_get (ss_regs ssf) r) HS);
      [vm_compute; reflexivity|];
      let r := fresh "r" in let Hr := fresh "Hr" in
      intros r Hr; cbv [CALLEE_SAVED In] in Hr;
      repeat (destruct Hr as [<-|Hr]); [..|destruct Hr]
    end; cbv beta;
    lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end;
    first
    [ rewrite (decL_soff E 2 128 (d_sp d - DEC_F) E2w ltac:(unfold DEC_F in *; lia) ltac:(unfold DEC_F in *; lia));
      replace (d_sp d - DEC_F + 128) with (d_sp d) by (unfold DEC_F; lia);
      unfold w64, d_sp, spZ; apply Z_to_bv_bv_unsigned
    | rewrite fsw_SOff0; unfold E; rewrite (decL_E_reg d q regs2 [] 3 3%bv eq_refl); exact R3
    | rewrite fsw_SOff0; unfold E; rewrite (decL_E_reg d q regs2 [] 4 4%bv eq_refl); exact R4
    | rewrite fsw_SOff0; unfold E;
      lazymatch goal with |- ew _ ?n = _ =>
        let j := eval vm_compute in (n - 35)%nat in change n with (35 + j)%nat;
        rewrite (decLN_E_sav d q regs2 [] j ltac:(lia)); reflexivity end ]. }
  assert (VL : val_mem tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) (d_lenp d) 8
                 (Z.of_nat (length (WriterSpec.six_bytes six)))).
  { lazymatch type of HS with
    | st_ok _ _ ?ssf _ =>
      pose proof (fsw_region_nth E ssf (restrict (w_H Wc) ms) 3%nat
        (YP09.mkRegion (Some 33%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 21 0))]) HS
        ltac:(vm_compute; reflexivity)) as HR3
    end.
    cbn [ms_mem restrict] in HR3.
    rewrite <- (Z.add_0_r (d_lenp d)).
    apply (fsw_field E _ 33%nat (d_lenp d) [YP09.mkChunk 0 (CVal 8 (SOff 21 0))] 0 8 0 8 0 8%N (SOff 21 0) _ HR3
             E33u);
      [ cbv [In]; tauto | rewrite fsw_SOff0; exact E21 | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia ]. }
  assert (HSOME : WriterSpec.b64_dec (d_tb d) = Some (WriterSpec.six_bytes six)).
  { assert (HDEC : WriterSpec.b64_dec (d_tb d) = decLA_out pad six (skipn (length (d_tb d)) (d_tb d)))
      by exact Hscan.
    rewrite decLA_skipn_end, decLA_out_nil in HDEC.
    rewrite HDEC, HTOK. replace (pad <=? 2) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
  lazymatch goal with
  | |- SRr _ _ (mkCfg _ ?mdX) _ =>
    assert (MAIN : SRr tfibsegs Wc (mkCfg ms mdX)
      (fpostU tfibsegs B (d_STKJ d) (d_ot d) (d_FP d) (d_regs d) (d_ly d) (d_S d) (d_U d) (d_W d) (d_mem d)
         (d_md d) 1 (d_U d ++ [(q - HEAD, HEAD)])
         (fun (ly' : alayout) (S' : astate) (W' : world tfibsegs) (regs' : bvmap 5 word)
              (mem' : word -> option byte) (md' : Model) =>
            getr regs' 10 = w64 q /\ 4096 + HEAD <= q /\
            ablocks B ly' S' = ablocks B (d_ly d) (d_S d) ++ [(q - HEAD, dec_size (d_tb d) + HEAD)] /\
            fs_rblock tfibsegs B ly' S' W' mem' q (dec_size (d_tb d)) /\
            zbytes_at tfibsegs W' mem' q (WriterSpec.six_bytes six) /\
            wkeep tfibsegs (d_W d) W' (d_mem d) mem' (spZ (d_regs d)) (d_ot d) (d_lenp d) 8 /\
            val_mem tfibsegs (mrestrict (w_H W') mem') (d_lenp d) 8
              (Z.of_nat (length (WriterSpec.six_bytes six))) /\
            cstr_ok tfibsegs W' mem' (d_text d) (d_tb d) /\
            fs_glob tfibsegs W' mem' (d_live d + dec_size (d_tb d))
              (Z.max (d_peak d) (d_live d + dec_size (d_tb d))) ((d_cnt d + 1) mod 2 ^ 64) (d_fail d))))
  end.
  { eapply (fsw_retU B fsw_wr_tbl fsw_wr_tbl_ok);
      [ exact HS | vm_compute; reflexivity | vm_compute; reflexivity
      | rewrite R1F; exact HRET | exact HJ | exact HARU | exact HPRES |].
    intros mat2. cbn beta.
    split; [exact R10F|]. split; [exact Hq|]. split; [exact Hbl|].
    split.
    { pose proof Hrb as (RB1 & RB2 & RB3 & RB4). split; [exact RB1|]. split; [exact RB2|]. split; [exact RB3|].
      exact (val_mem_below (w_H Wc) mem2 (ms_mem ms) alloc_ceiling (q - HEAD) 8%nat (d_n d) SB
               ltac:(unfold HEAD in *; lia) ltac:(unfold HEAD in *; lia) RB4). }
    split.
    { unfold zbytes_at in HZb |- *. apply (garr8_frame tfibsegs _ _ q _ HZb).
      intros a Ha. apply (mbyte_below (w_H Wc) mem2 (ms_mem ms) alloc_ceiling a SB).
      pose proof (decLA_nbytes six (d_tb d) ltac:(lia)) as Hnb2. unfold d_n, HEAD in *. lia. }
    split.
    { intros a Ha Hno. change (spZ (d_regs d)) with (d_sp d) in Ha. destruct (Kw a Ha Hno) as [K1 K2].
      assert (HAV : aview tfibsegs (w_H Wc) (ms_mem ms) a = aview tfibsegs (w_H Wc) mem2 a)
        by (apply (aview_at tfibsegs); apply FR; [lia | unfold DEC_F in *; lia]).
      split.
      - rewrite <- K1. apply (mbyte_of_aview tfibsegs). exact HAV.
      - etransitivity; [exact K2|].
        apply decLB_wr_eq; [lia | intros X; pose proof (fs_segs_img a X) as Hl; unfold FS_IMG_END in Hl; lia
                           | exact HAV]. }
    split; [exact VL|].
    split; [exact (cstr_ok_below Wc mem2 (ms_mem ms) (d_text d) (d_tb d) SB Kc)|].
    rewrite Z.mod_small by lia.
    exact (fs_glob_below Wc mem2 (ms_mem ms) _ _ _ _ SB Hglob). }
  eapply SRr_mono; [exact MAIN|].
  cbv beta. intros W' c' Hle HP. right. right.
  exists q, (WriterSpec.six_bytes six).
  split; [exact Hcf|]. split; [exact HSOME|]. split; [unfold HEAD in *; lia|]. exact HP.
Qed.

Lemma decL_arm_nul : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  (forall W3 ly3 S3 U3 regs3 mem3 md3 k3, dec_at_free B d q W3 ly3 S3 U3 regs3 mem3 md3 k3 ->
     SRr tfibsegs W3 (cfg_at tfibsegs A_fuzz_free regs3 mem3 md3) (dec_post B d)) ->
  i = length (d_tb d) ->
  SRr tfibsegs Wc (decL_hcfg regsc memc mdc) (dec_post B d).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH HFREE Hi. subst i.
apply (decLN_exit d q six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH HFREE).
intros regs' mem' md' HH' R10 Hpad2 HTOK.
exact (decLN_succ_rs d q six pad acc Wc lyc Sc Uc regs' mem' md' k HE HH' R10 Hpad2 HTOK).
Qed.

(* ---- one iteration, and the loop by induction on the bytes left ---- *)
Lemma decL_head_i : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k,
  dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k -> (i <= length (d_tb d))%nat.
Proof. intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HH. decL_unhead HH. exact Hi. Qed.

Lemma decL_step : forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k,
  dec_entry_ok B d -> dec_head B d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  (forall W3 ly3 S3 U3 regs3 mem3 md3 k3, dec_at_free B d q W3 ly3 S3 U3 regs3 mem3 md3 k3 ->
     SRr tfibsegs W3 (cfg_at tfibsegs A_fuzz_free regs3 mem3 md3) (dec_post B d)) ->
  (forall six' pad' acc' Wc' lyc' Sc' Uc' regsc' memc' mdc' k',
     dec_head B d q (S i) six' pad' acc' Wc' lyc' Sc' Uc' regsc' memc' mdc' k' ->
     SRr tfibsegs Wc' (decL_hcfg regsc' memc' mdc') (dec_post B d)) ->
  SRr tfibsegs Wc (decL_hcfg regsc memc mdc) (dec_post B d).
Proof.
intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH HFREE HIH.
pose proof (decL_head_i d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HH) as Hi.
destruct (Nat.eq_dec i (length (d_tb d))) as [Heq | Hne];
  [exact (decL_arm_nul d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH HFREE Heq)|].
assert (Hlt : (i < length (d_tb d))%nat) by lia.
destruct (WriterSpec.b64_ws (nth i (d_tb d) 0)) eqn:Ew.
- exact (decL_arm_skip d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH HIH Hlt (or_introl Ew)).
- destruct (Z.eq_dec (nth i (d_tb d) 0) 61) as [E61 | N61].
  + exact (decL_arm_skip d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH HIH Hlt (or_intror E61)).
  + exact (decL_arm_other d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH HFREE HIH Hlt Ew N61).
Qed.

Lemma dec_loop_stage : dec_stage_loop B.
Proof.
unfold dec_stage_loop. intros d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH HFREE.
change (SRr tfibsegs Wc (decL_hcfg regsc memc mdc) (dec_post B d)).
remember (length (d_tb d) - i)%nat as m eqn:Hm.
revert i six pad acc Wc lyc Sc Uc regsc memc mdc k HH Hm.
induction m as [|m IH]; intros i six pad acc Wc lyc Sc Uc regsc memc mdc k HH Hm.
- apply (decL_step d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH HFREE).
  intros six' pad' acc' Wc' lyc' Sc' Uc' regsc' memc' mdc' k' HH'.
  pose proof (decL_head_i d q (S i) six' pad' acc' Wc' lyc' Sc' Uc' regsc' memc' mdc' k' HH') as Hi'.
  pose proof (decL_head_i d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HH) as Hi. lia.
- apply (decL_step d q i six pad acc Wc lyc Sc Uc regsc memc mdc k HE HH HFREE).
  intros six' pad' acc' Wc' lyc' Sc' Uc' regsc' memc' mdc' k' HH'.
  apply (IH (S i) six' pad' acc' Wc' lyc' Sc' Uc' regsc' memc' mdc' k' HH'). lia.
Qed.
End LOOP.

Theorem decode_holds : forall (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) (B : asyms),
  (@FSH_Rt.fs_img_facts rc YB1v.tfibsegs B) -> (FSH_Base.FsShadowSyms B) ->
  (astrlen_realizesU YB1v.tfibsegs B PC_strlen) -> (amemchr_realizesU YB1v.tfibsegs B PC_memchr) ->
  (@FSH_Fn_alloc.fuzz_malloc_spec fx rc SK YB1v.tfibsegs B) -> (@FSH_Fn_alloc.fuzz_free_spec fx rc SK YB1v.tfibsegs B) ->
  @decode_spec fx rc SK B YB1v.tfibsegs.
Proof.
intros fx rc SK B HIMG HSS HSTRLEN HMEMCHR HMALLOC HFREE.
apply (decode_of_stages B).
- exact (dec_entry_ok_stage B HSS HIMG HSTRLEN HMALLOC).
- exact (dec_loop_stage B HSS HIMG HMEMCHR).
- exact (dec_free_stage B HSS HFREE).
Qed.
