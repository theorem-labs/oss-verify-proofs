(* lv2_locate_manifest_readings 0x81c04 (lv2_locate.c:85-148), 331 instructions: the walk's shared base.
   The walk is cut at fixed pcs (after each call, the loop heads); every cut carries a semantic invariant (registers,
   frame slots, memory facts, the journal from readings' entry), and every segment builds its own symbolic state from
   it (the donor's entry-lemma pattern, A/ACex.v:107 rfc_entry, here generic over the frame slots).
   Frame (MEASURED, fm-fn-measure.md 5): addi sp,sp,-208; ra@200, s0@192, s1@184, s2@176, s3@168, s4@160, s5@152,
   s6@144, s7@136, s8@128, s9@120, s10@112, s11@104 (offsets from F = entry sp - 208). Locals after 0x81cb4: F+0 rp,
   F+8 read_again, F+0x18 mask2, F+0x20 uri, F+0x30 uri_len, F+0x40 text, F+0x48 uri-2, F+0x50 uri-3, F+0x58 "prefix",
   F+0x60 mask1; scratch F+0x10 -p0, F+0x28 ns, F+0x38 p0/local. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YCbm.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0q YCbq YC20 YI00 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import AB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison FMPstat FMH_Base FMH_Rt FMH_Fn.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMW_g3kit.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the code table of readings (0x81c04, 331 words) ---- *)
Definition rd_tbl : ctable := Eval vm_compute in build_table tfibsegs A_readings 331 TEmpty.
Lemma rd_tbl_eq : rd_tbl = build_table tfibsegs A_readings 331 TEmpty.
Proof. vm_cast_no_check (eq_refl rd_tbl). Qed.
Lemma rd_tbl_ok : table_ok tfibsegs rd_tbl.
Proof. rewrite rd_tbl_eq. apply build_table_ok0. unfold A_readings. lia. Qed.
Lemma rd_tbl_probe : clookup rd_tbl 0x81c04 = Some 0xf3010113 /\ clookup rd_tbl 0x820f0 = Some 0x00008067 /\
  clookup rd_tbl 0x8212c = Some 0xa55d60ef /\ clookup rd_tbl 0x82130 = None.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* ---- the cut pcs ---- *)
Definition RD_C1 : Z := 0x81c5c.   (* after strlen (uri) *)
Definition RD_C2 : Z := 0x81c70.   (* after fuzz_malloc (uri_len + 3) *)
Definition RD_C3 : Z := 0x81c90.   (* after snprintf (whole, uri_len + 3, "<%s>", uri) *)
Definition RD_C4 : Z := 0x81c9c.   (* after strstr (text, whole) *)
Definition RD_C5 : Z := 0x81ca8.   (* after fuzz_free (whole) *)
Definition RD_L : Z := 0x81d18.    (* the declaration scan's head, lv2_locate.c:104 *)
Definition RD_C6 : Z := 0x81d4c.   (* after strncmp (at + 1, "prefix", 6) *)
Definition RD_C7 : Z := 0x81d64.   (* after strncasecmp (at, "PREFIX", 6) *)
Definition RD_P : Z := 0x81da8.    (* p = at + 6 or at + 7, lv2_locate.c:115 *)
Definition RD_C8 : Z := 0x81f20.   (* after strchr (ns, '>') *)
Definition RD_C9 : Z := 0x81f4c.   (* after strncmp (uri, ns, ns_len) *)
Definition RD_C10 : Z := 0x81f70.  (* after strlen (local) *)
Definition RD_C11 : Z := 0x81fe4.  (* after isalnum (local[i]) *)
Definition RD_C12 : Z := 0x82070.  (* after has_prefixed *)
Definition RD_R0 : Z := 0x820b0.   (* s5 = 0; return *)
Definition RD_R : Z := 0x820b4.    (* a0 = s5; restore; return *)
Definition RD_CONT : Z := 0x82028. (* s4 = '@'; at = s3 + 1; back to RD_L *)

(* the constants the scan keeps in its frame *)
Definition RD_MASK1 : Z := 0x100003e01.        (* bits 0, 9..13, 32: NUL and isspace, lv2_locate.c:120 *)
Definition RD_MASK2 : Z := 0x4000000002003.    (* bits 0, 1, 13, 50: '-', '.', ':', '_' (c - 45), plain_local *)
Definition RD_PREFIX : Z := 0x20fc0.           (* "prefix", lv2_locate.c:109 *)
Definition RD_PREFIXU : Z := 0x20fe0.          (* "PREFIX", lv2_locate.c:111 *)

(* the saved registers: (offset from F, register) *)
Definition RD_SAVED : list (Z * Z) :=
  [(200, 1); (192, 8); (184, 9); (176, 18); (168, 19); (160, 20); (152, 21); (144, 22); (136, 23); (128, 24);
   (120, 25); (112, 26); (104, 27)].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* readings' entry: the values readings_spec quantifies *)
Record rdcx := mkRDCX {
  cx_ly : alayout; cx_S : astate; cx_W : world tfibsegs; cx_regs : bvmap 5 word; cx_mem : word -> option byte;
  cx_md : Model; cx_ch : list (Z * Z * Z);
  cx_t : Z; cx_u : Z; cx_v : Z; cx_tb : list Z; cx_ub : list Z;
  cx_live : Z; cx_peak : Z; cx_cnt : Z; cx_fail : Z }.

Definition cx_sp (cx : rdcx) : Z := spZ (cx_regs cx).
Definition cx_F (cx : rdcx) : Z := cx_sp cx - 208.
Definition cx_ulen (cx : rdcx) : Z := Z.of_nat (length (cx_ub cx)).

(* readings_spec's premises (CTX is the call context) *)
Definition rd_base (CTX : list (list Z)) (cx : rdcx) : Prop :=
  let ly := cx_ly cx in let S := cx_S cx in let W := cx_W cx in let regs := cx_regs cx in let mem := cx_mem cx in
  afn_pre tfibsegs B STK_readings ly S W regs mem (cx_md cx) (cx_ch cx) /\ In (raZ regs :: spine (cx_ch cx)) CTX /\
  arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W) mem) /\
  getr regs 10 = w64 (cx_t cx) /\ getr regs 11 = w64 (cx_u cx) /\ getr regs 12 = w64 (cx_sp cx) /\
  (forall a, cx_sp cx <= a < cx_sp cx + 16 -> apresent (w_H W) mem a) /\ cx_sp cx + 16 <= ly_top ly /\
  val_mem tfibsegs (rdW W mem) (cx_sp cx) 8 (cx_v cx) /\ 0 <= cx_v cx < 2 ^ 63 /\
  cstr_ok tfibsegs W mem (cx_t cx) (cx_tb cx) /\ cstr_ok tfibsegs W mem (cx_u cx) (cx_ub cx) /\
  cstr_kept B ly S (cx_t cx) (cx_tb cx) /\ cstr_kept B ly S (cx_u cx) (cx_ub cx) /\
  (length (cx_ub cx) <= 255)%nat /\ Z.of_nat (length (cx_tb cx)) <= MANIFEST_MAX /\
  fm_glob tfibsegs W mem (cx_live cx) (cx_peak cx) (cx_cnt cx) (cx_fail cx) /\
  cx_live cx + cx_ulen cx + 3 < 2 ^ 33 /\ cx_cnt cx + 1 < 2 ^ 33 /\
  st_nev S + EV_names <= EV_MAX /\ blocks_bytes S + LIVE_names <= LIVE_MAX.

(* readings_spec's post *)
Definition rd_post (cx : rdcx) : world tfibsegs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' res,
    c' = mkCfg (mkst regs' (getr (cx_regs cx) 1) mem' (seg_rom tfibsegs)) md' /\
    ajournal tfibsegs B (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
      [] ly' S' W' mem' md' EV_names /\
    (forall a, cx_sp cx + 8 <= a < cx_sp cx + 16 -> aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H (cx_W cx)) (cx_mem cx) a) /\
    aregs_preserved (cx_regs cx) regs' /\
    getr regs' 10 = w64 res /\ Permutation (ablocks B ly' S') (ablocks B (cx_ly cx) (cx_S cx)) /\
    names_res tfibsegs (cx_tb cx) (cx_ub cx) (cx_live cx) (cx_peak cx) (cx_cnt cx) (cx_fail cx) res W' mem' /\
    val_mem tfibsegs (rdW W' mem') (cx_sp cx) 8
      (if (length (cx_ub cx) =? 0)%nat || (cx_cnt cx =? cx_fail cx) then cx_v cx
       else cx_v cx + Z.of_nat (ManifestModel.nreadings (cx_tb cx) (cx_ub cx))).

(* the saved registers in the frame *)
Definition rd_saved_ok (cx : rdcx) (W3 : world tfibsegs) (mem3 : word -> option byte) : Prop :=
  Forall (fun s => val_mem tfibsegs (rdW W3 mem3) (cx_F cx + fst s) 8
    (bv_unsigned (getr (cx_regs cx) (Z_to_bv 5 (snd s))))) RD_SAVED.

(* what every cut point after the prologue carries: the journal from readings' entry (over the user-poison view U,
   POISON.md 8), sp = F, gp/tp, s0 = the shadow base, the saved registers, names' saved ra kept, the relro view, the
   two strings with their homes *)
Definition rd_com (cx : rdcx) (k : Z) (U : list (Z * Z)) ly3 S3 (W3 : world tfibsegs) (regs3 : bvmap 5 word)
  (mem3 : word -> option byte) (md3 : Model) : Prop :=
  ajournal tfibsegs B (STK_readings + 16) (cx_sp cx + 16) FM_PSTAT_FP (cx_ly cx) (cx_S cx) (cx_W cx) (cx_mem cx) (cx_md cx)
    [] ly3 S3 W3 (unpoison U mem3) md3 k /\
  0 <= k <= EV_names /\
  getr regs3 2 = w64 (cx_F cx) /\ getr regs3 3 = getr (cx_regs cx) 3 /\ getr regs3 4 = getr (cx_regs cx) 4 /\
  getr regs3 8 = w64 SHADOW_OFF /\
  rd_saved_ok cx W3 mem3 /\
  (forall a, cx_sp cx + 8 <= a < cx_sp cx + 16 -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H (cx_W cx)) (cx_mem cx) a) /\
  arodata_okP tfibsegs FM_RLO FM_RHI B (aview tfibsegs (w_H W3) mem3) /\
  cstr_ok tfibsegs W3 mem3 (cx_t cx) (cx_tb cx) /\ cstr_ok tfibsegs W3 mem3 (cx_u cx) (cx_ub cx) /\
  cstr_kept B ly3 S3 (cx_t cx) (cx_tb cx) /\ cstr_kept B ly3 S3 (cx_u cx) (cx_ub cx).

(* the value readings returns and leaves in *rp, from the facts at the return *)
Definition rd_ret_facts (cx : rdcx) ly3 S3 (W3 : world tfibsegs) (mem3 : word -> option byte) (res : Z) : Prop :=
  Permutation (ablocks B ly3 S3) (ablocks B (cx_ly cx) (cx_S cx)) /\
  names_res tfibsegs (cx_tb cx) (cx_ub cx) (cx_live cx) (cx_peak cx) (cx_cnt cx) (cx_fail cx) res W3 mem3 /\
  val_mem tfibsegs (rdW W3 mem3) (cx_sp cx) 8
    (if (length (cx_ub cx) =? 0)%nat || (cx_cnt cx =? cx_fail cx) then cx_v cx
     else cx_v cx + Z.of_nat (ManifestModel.nreadings (cx_tb cx) (cx_ub cx))).

(* the return at RD_R: a0 = s5 *)
Definition rd_seg_R (CTX : list (list Z)) : Prop :=
  forall cx k ly3 S3 W3 regs3 mem3 md3 res,
  rd_base CTX cx -> rd_com cx k [] ly3 S3 W3 regs3 mem3 md3 ->
  getr regs3 21 = w64 res -> 0 <= res < 2 ^ 64 ->
  rd_ret_facts cx ly3 S3 W3 mem3 res ->
  SRr tfibsegs W3 (cfg_at tfibsegs RD_R regs3 mem3 md3) (rd_post cx).
End c.

(* ---- frame slots as a symbolic region: chunk (offset, j) holds extra atom 32 + j ---- *)
Definition rd_slot_chunks (cs : list (Z * nat)) : list YP09.chunk :=
  map (fun c => YP09.mkChunk (fst c) (CVal 8 (SOff (32 + snd c) 0))) cs.

Section f. Context {fx : YK11.FPState}.
Lemma rd_chunks_ok : forall E m b cs,
  Forall (fun c => val_mem tfibsegs m (b + fst c) 8 (bv_unsigned (ew E (32 + snd c)))) cs ->
  Forall (YP09.chunk_ok tfibsegs E m b) (rd_slot_chunks cs).
Proof.
intros E m b cs H. induction H as [|c cs Hc _ IH]; [constructor|]. constructor; [|exact IH].
apply (chunk_ok_val tfibsegs E m b (fst c) 8 (SOff (32 + snd c) 0) (bv_unsigned (ew E (32 + snd c)))).
- cbn [sv_denot]. rewrite Z.add_0_r. reflexivity.
- pose proof (bv_unsigned_in_range _ (ew E (32 + snd c))) as R. change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in R. exact R.
- cbn. lia.
- exact Hc.
Qed.

Lemma rd_frame_region_ok : forall E m b lo hi wlo whi cs,
  bv_unsigned (ew E 2) = b -> 0 <= b + lo -> b + hi <= 2 ^ 64 ->
  (forall o, wlo <= o < whi -> writable_at tfibsegs m (b + o)) ->
  Forall (fun c => val_mem tfibsegs m (b + fst c) 8 (bv_unsigned (ew E (32 + snd c)))) cs ->
  region_ok tfibsegs E m (YP09.mkRegion (Some 2%nat) lo hi wlo whi (rd_slot_chunks cs)).
Proof.
intros E m b lo hi wlo whi cs Hb Hlo Hhi Hw Hc. unfold region_ok.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Hb.
split; [exact Hlo|]. split; [exact Hhi|]. split; [exact Hw|]. exact (rd_chunks_ok E m b cs Hc).
Qed.
End f.
