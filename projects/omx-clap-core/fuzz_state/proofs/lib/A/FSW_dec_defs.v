(* preset_base64_decode (fs.asan 0x8481c, pf.c:610-650), the shared definitions of the walk (a Theorem Labs lane):
   the entry bundle, the frame layout, the three cut predicates (loop head, the call of fuzz_free) and the three arm posts.
   SCRATCH during the walk; becomes the head of lib/A/FSW_preset_base64_decode.v.
   Addresses MEASURED with the engine (sym_run_toN / sym_runN_tok over FSW_writer_tbl.fsw_wr_tbl from fss0T 0x8481c 112):
   frame 112 (13 saved words s11..s0, ra at sp-104..sp-8; lenp spilled at sp-112 before the loop); strlen call
   0x8486c -> PC_strlen (ra 0x8486c); fuzz_malloc call (ra 0x84880, a0 = ((len >> 2) << 1) + (len >> 2) + 3 = dec_size);
   loop head 0x848bc (s0 = 0x100002600 the whitespace mask, s1 = q, s2 = s4 = text + i, s3 = G_B64, s5 = shadow base,
   s6 = n, s7 = acc, s8 = bits, s9 = 61, s10 = pad, s11 = 2); memchr call (ra 0x848fc, a0 = G_B64, a1 = c, a2 = 65);
   fuzz_free call (ra 0x8497c, a0 = q); final ret 0x849bc. *)
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
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSH_Fn_alloc FSH_Fn_writer
FSW_K FSW_K3 FSW_ret FSW_rres FSW_writer_tbl FSW_writer_model.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- addresses and constants ---- *)
Definition DEC_F : Z := 112.                    (* = FSH_Base.FRAME_preset_base64_decode *)
Definition DEC_RA_STRLEN : Z := 0x8486c.
Definition DEC_RA_MALLOC : Z := 0x84880.
Definition DEC_HEAD : Z := 0x848bc.
Definition DEC_RA_MEMCHR : Z := 0x848fc.
Definition DEC_RA_FREE : Z := 0x8497c.
Definition DEC_WSMASK : Z := 4294977024.        (* 2^32 + 2^13 + 2^10 + 2^9: ' ', '\r', '\n', '\t' *)

(* the frame: base b = entry sp - 112; word 0 holds lenp (spilled before the loop); word 1 + j holds the entry value of
   the j-th register of dec_saved (s11 first, ra last) *)
Definition dec_saved : list (bv 5) := [27; 26; 25; 24; 23; 22; 21; 20; 19; 18; 9; 8; 1]%bv.
Definition dec_frame_ok (W : world tfibsegs) (mem : word -> option byte) (b : Z) (regs0 : bvmap 5 word) : Prop :=
  forall j r, nth_error dec_saved j = Some r ->
    val_mem tfibsegs (mrestrict (w_H W) mem) (b + 8 + 8 * Z.of_nat j) 8 (bv_unsigned (getr regs0 r)).
Definition dec_lenp_slot (W : world tfibsegs) (mem : word -> option byte) (b lenp : Z) : Prop :=
  val_mem tfibsegs (mrestrict (w_H W) mem) b 8 lenp.

(* ---- the entry bundle: the parameters of decode_spec / decode_spec_ff ---- *)
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

(* the premises both specs share, then the two placements of *lenp: a caller real-stack object under the raised window
   top ot (decode_spec), or 8 bytes of a live caller fake frame with ot = sp and the slot in FP, its shadow addressable
   (decode_spec_ff). No CTX conjunct: the specs dropped `In (raZ regs :: spine ch) CTX` and their CTX binder
   (a working branch 50968be8342). *)
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
  ((d_FP d = FS_PSTAT_FP /\ spZ regs <= lenp /\ lenp + 8 <= d_ot d /\ d_ot d mod 16 = 0 /\ d_ot d <= ly_top ly /\
    (forall a, spZ regs <= a < d_ot d -> apresent (w_H W) mem a) /\
    (* dec_chain_lenp (a Theorem Labs lane 00:30Z, ruling pending at a Theorem Labs lane): fuzz_malloc is called with s0 = lenp, a real-stack
       address here, so its fpreU needs a frame chain from lenp, which reads caller stack above ot *)
    (exists chl, achain ly (aview tfibsegs (w_H W) (unpoison U mem)) (spZ regs) lenp chl)) \/
   (d_FP d = FS_PSTAT_FP ++ [(lenp, lenp + 8)] /\ d_ot d = spZ regs /\
    (exists cid pos, In (cid, pos) (frames S) /\ forall a, lenp <= a < lenp + 8 -> in_zr a (frame_rng ly (cid, pos))) /\
    (forall a, lenp <= a < lenp + 8 -> apresent (w_H W) mem a) /\
    (* *lenp's 8 bytes addressable in the shadow (decode_spec_ff, a Theorem Labs lane 11:5xZ): the inline check of the store reads it *)
    range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF lenp 8)).

(* the caller's journal from the entry, at the raised top ot (= sp for the fake-frame placement) *)
Definition dec_J (d : DE) (lyc : alayout) (Sc : astate) (Wc : world tfibsegs) (Uc : list (Z * Z))
    (memc : word -> option byte) (mdc : Model) (k : Z) : Prop :=
  ajournal tfibsegs B (d_STKJ d) (d_ot d) (d_FP d) (d_ly d) (d_S d) (d_W d) (unpoison (d_U d) (d_mem d)) (d_md d) []
    lyc Sc Wc (unpoison Uc memc) mdc k.

(* the facts every cut keeps about the caller's objects: *lenp's value, the window bytes outside it (wkeep, vacuous
   when ot = sp), the text, the image read-only view and the shadow-base cells *)
Definition dec_kept (d : DE) (Wc : world tfibsegs) (memc : word -> option byte) : Prop :=
  val_mem tfibsegs (rdW Wc memc) (d_lenp d) 8 (d_v d) /\
  wkeep tfibsegs (d_W d) Wc (d_mem d) memc (d_sp d) (d_ot d) (d_lenp d) 8 /\
  cstr_ok tfibsegs Wc memc (d_text d) (d_tb d) /\
  arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H Wc) memc).

(* ---- the loop head 0x848bc: i bytes of the text read, six the sextets taken so far, pad the '=' count, acc the
   accumulator (only acc mod 64 = the last sextet is used); the block q holds six_bytes six; one allocation made (k = 1,
   U gains q's head) ---- *)
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
  (* registers *)
  spZ regsc = d_sp d - DEC_F /\ getr regsc 3 = getr (d_regs d) 3 /\ getr regsc 4 = getr (d_regs d) 4 /\
  getr regsc 8 = w64 DEC_WSMASK /\ getr regsc 9 = w64 q /\
  getr regsc 18 = w64 (text + Z.of_nat i) /\ getr regsc 19 = w64 G_B64 /\ getr regsc 20 = w64 (text + Z.of_nat i) /\
  getr regsc 21 = w64 SHADOW_OFF /\ getr regsc 22 = w64 n /\ getr regsc 23 = w64 acc /\ 0 <= acc < 2 ^ 64 /\
  getr regsc 24 = w64 (6 * Z.of_nat (length six) mod 8) /\ getr regsc 25 = w64 61 /\ getr regsc 26 = w64 pad /\
  getr regsc 27 = w64 2 /\
  (* the frame *)
  dec_frame_ok Wc memc (d_sp d - DEC_F) (d_regs d) /\ dec_lenp_slot Wc memc (d_sp d - DEC_F) (d_lenp d) /\
  (* the data *)
  dec_kept d Wc memc /\ zbytes_at tfibsegs Wc memc q (WriterSpec.six_bytes six) /\
  (* the model (old proof's at_head, 211ff3e9df0 lib/A/Prog/preset_base64_decode_blocks.v:627-640) *)
  (i <= length tb)%nat /\ 0 <= pad <= Z.of_nat i /\ (length six <= i)%nat /\
  Forall (fun x => 0 <= x < 64) six /\ acc mod 64 = last six 0 /\
  WriterSpec.b64_dec tb =
    match WriterSpec.b64_scan pad six (skipn i tb) with
    | Some (six', pad') => if (pad' <=? 2) && WriterSpec.six_tail_ok six' then Some (WriterSpec.six_bytes six') else None
    | None => None
    end.

(* ---- the call of fuzz_free on a refused text (pc A_fuzz_free, ra 0x8497c, a0 = q) ---- *)
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
  getr regsc 8 = w64 DEC_WSMASK /\
  dec_frame_ok Wc memc (d_sp d - DEC_F) (d_regs d) /\ dec_lenp_slot Wc memc (d_sp d - DEC_F) (d_lenp d) /\
  dec_kept d Wc memc.

(* ---- the three arms of the post, at the raised top (decode_spec's wpost = fpostU at STK + (ot - sp), ot; decode_spec_ff's
   fpostU at STK, sp is the same with ot = sp, where wkeep is vacuous) ---- *)
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

(* ---- the three stage statements the walk proves (each in its own scratch part during the walk) ---- *)
(* (E) entry -> strlen -> fuzz_malloc; the refused arm closes; on success the loop head with nothing read. No trace
   premise: fuzz_malloc_spec dropped its CTX premise with the writer specs (ALLOC, a Theorem Labs lane). *)
Definition dec_stage_entry : Prop :=
  forall d, dec_entry_ok d ->
  (forall Wc lyc Sc Uc regsc memc mdc k q, dec_head d q 0 [] 0 0 Wc lyc Sc Uc regsc memc mdc k ->
     SRr tfibsegs Wc (mkCfg (YK11.mkst regsc (Z_to_bv 64 DEC_HEAD) memc (YK11.seg_rom tfibsegs)) mdc) (dec_post d)) ->
  SRr tfibsegs (d_W d) (cfg_at tfibsegs A_preset_base64_decode (d_regs d) (d_mem d) (d_md d)) (dec_post d).
(* (L) the loop from any head to the end: the success arm closes; a refused text reaches the fuzz_free call *)
Definition dec_stage_loop : Prop :=
  forall d q i six pad acc Wc lyc Sc Uc regsc memc mdc k, dec_entry_ok d ->
  dec_head d q i six pad acc Wc lyc Sc Uc regsc memc mdc k ->
  (forall W3 ly3 S3 U3 regs3 mem3 md3 k3, dec_at_free d q W3 ly3 S3 U3 regs3 mem3 md3 k3 ->
     SRr tfibsegs W3 (cfg_at tfibsegs A_fuzz_free regs3 mem3 md3) (dec_post d)) ->
  SRr tfibsegs Wc (mkCfg (YK11.mkst regsc (Z_to_bv 64 DEC_HEAD) memc (YK11.seg_rom tfibsegs)) mdc) (dec_post d).
(* (F) the fuzz_free call on a refused text and the return: the bad-text arm closes *)
Definition dec_stage_free : Prop :=
  forall d q W3 ly3 S3 U3 regs3 mem3 md3 k3, dec_entry_ok d ->
  dec_at_free d q W3 ly3 S3 U3 regs3 mem3 md3 k3 ->
  SRr tfibsegs W3 (cfg_at tfibsegs A_fuzz_free regs3 mem3 md3) (dec_post d).
End D.
