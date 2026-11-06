(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMgxaSeamPost.v (cold/port-fm-rtprintf-param 0ddf65fd8cc); relocated to libreac/fuzz_disco.asan by g9/tool (reloc.py target disco-A): module paths changed; 5 address numerals moved (port_addr_check 0767e70e074a predict, fm.asan -> fuzz_disco.asan, symbol + offset; table g9/tool/tables/disco-A/FMgxaSeamPost.table); names: record RT_IImgA -> . *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_disco/lib/A/FMgxaSeamPost.v at 2d2ff01bb6f2 relocated to reac-pw/fuzz_rate's ASan image A: module paths changed; numerals by port_core 1e42da8952ec (ledger provenance/reloc/A-Snp.tsv). *)
(* Step 3 of the evt -> SRr seam at musl vfprintf: GXA's post read as the harness's post, every
   piece of it except the final assembly (GxSeam does that).

   GXA's walk ends in a store m' with (lib/CJ/RL/GX/G_vfprintf_snf.v:203 vfprintf_snf_post)
     munch Wn m m'       every byte outside the window list Wn is the old one
                         (Wn = [(lo, sp); (Fp, Fp + 232); (CK, CK + 16); (D, D + dn)], each (lo, hi))
     wmono img_segs m m' every byte the old store could write is still writable
   and the bridge (FMgxa_bridge.v srr_of_cj_evt) hands the harness the store
   `munrestrict (w_H W) mem m'` (lib/Reusable/YK04.v:20).  This file reads those two facts as
   the harness's frame (win_view_out), its presence post (win_present), the destination bytes
   (view_of_bytes_at) and ARU (aru_of_window, by FMupoison.ARU_frame, the U form of the harness's
   frame law AR_frame_law, lib/Reusable/YG0d.v:439).  The machine-state shapes the assembly needs
   are frm0_mkFP and cfg_of_ms.

   Two facts about fm.asan's four segments (tfibsegs) are checked by vm_compute: a writable segment
   is readable (so a writable byte is a byte the harness can read), and every segment lies in
   [0x10000, 0x5f7000) (0x5f7000 = sym 0x35000 = GXA's GLOBALS_TOP on A_img, RT_IImgA.v:73). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK04 YK0i YK14 YK1b YK1a YK18 YP09 YG0n YG00 YG0a YG01 YG0f YG0v YG0d YA0n YM05.

From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Rt Require Import SnUpoison.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib Require Mem Frame MState FP.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.RL.I Require Import RecAsanVfA.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import FMgxa_bridge FMgxaSeamBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* the CJ tree's modules, named by their full paths (lib/Lib has modules of the same short names) *)
Module CJM := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Mem.
Module CJF := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.Frame.
Module CJMS := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.MState.
Module CJFP := OSSVerify.Proofs.reac_pw.fuzz_rate.lib.CJ.Lib.FP.

(* ---- fm.asan's segments ---- *)
Lemma tfib_wr_rd : forall seg, In seg tfibsegs -> seg_writable seg = true -> seg_readable seg = true.
Proof.
assert (F : forallb (fun seg => negb (seg_writable seg) || seg_readable seg)%bool tfibsegs = true)
  by (vm_compute; reflexivity).
intros seg Hin Hw. pose proof (proj1 (forallb_forall _ _) F seg Hin) as Hs. cbn beta in Hs.
rewrite Hw in Hs. exact Hs.
Qed.

Lemma tfib_seg_range : forall (x : word) seg, find_segment tfibsegs (bv_unsigned x) 1 = Some seg ->
  65536 <= bv_unsigned x < 0x5fa000.
Proof.
assert (F : forallb (fun seg => (65536 <=? Z.of_N (seg_base seg)) &&
                                (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? 0x5fa000))%bool tfibsegs = true)
  by (vm_compute; reflexivity).
intros x seg Hf. destruct (find_segment_some_spec _ _ _ _ Hf) as (Hin & H1 & H2).
pose proof (proj1 (forallb_forall _ _) F seg Hin) as Hs. cbn beta in Hs.
apply andb_prop in Hs as [A1 A2]. apply Z.leb_le in A1. apply Z.leb_le in A2. lia.
Qed.

(* a byte a store could write and does not hold is a byte of a readable segment *)
Lemma seg_rom_of_wview : forall (m : word -> option byte) (x : word),
  wview tfibsegs m x <> None -> m x = None -> YK11.seg_rom tfibsegs x <> None.
Proof.
intros m x Wv E. unfold wview in Wv. rewrite E in Wv.
destruct (find_segment tfibsegs (bv_unsigned x) 1) as [seg|] eqn:Hf; [|exfalso; exact (Wv eq_refl)].
destruct (seg_writable seg) eqn:Hw; [|exfalso; exact (Wv eq_refl)].
destruct (segment_byte_at (seg_bytes seg) (Z.to_N (bv_unsigned x - Z.of_N (seg_base seg)))) as [b|] eqn:Eb;
  [|exfalso; exact (Wv eq_refl)].
destruct (find_segment_some_spec _ _ _ _ Hf) as (Hin & _ & _).
unfold YK11.seg_rom, memory_read. change (Z.of_N 1) with 1. rewrite Hf.
rewrite (tfib_wr_rd seg Hin Hw). change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
rewrite Eb. cbv beta iota. discriminate.
Qed.

(* ---- windows ---- *)
Lemma outside_dec : forall (W : list (Z * Z)) x, CJF.outside W x \/ Exists (fun r => fst r <= x < snd r) W.
Proof.
induction W as [|[lo hi] W IH]; intros x; cbn [CJF.outside]; [left; exact I|].
destruct (Z_lt_le_dec x lo) as [L|L]; [|destruct (Z_lt_le_dec x hi) as [L2|L2]].
- destruct (IH x) as [Ho|HE]; [left; split; [lia | exact Ho] | right; apply Exists_cons_tl; exact HE].
- right. apply Exists_cons_hd. cbn [fst snd]. lia.
- destruct (IH x) as [Ho|HE]; [left; split; [lia | exact Ho] | right; apply Exists_cons_tl; exact HE].
Qed.

(* a (p, len) list that misses a misses the same list read as (lo, hi) intervals, when no lo is negative *)
Lemma outside_of_not_in_zr : forall (W : list (Z * Z)) a,
  Forall (fun r => 0 <= fst r) W -> ~ Exists (in_zr a) W -> CJF.outside W a.
Proof.
induction W as [|[lo hi] W IH]; intros a HF HN; cbn [CJF.outside]; [exact I|].
apply Forall_cons_iff in HF as [H0 HF]. cbn [fst] in H0. split.
- intros Hin. apply HN. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. lia.
- apply IH; [exact HF|]. intros HE. apply HN. apply Exists_cons_tl. exact HE.
Qed.

(* an address in an image segment is outside a window list whose intervals all lie off the image *)
Lemma outside_of_off_img : forall (W : list (Z * Z)) x,
  Forall (fun r => snd r <= 65536 \/ 0x5fa000 <= fst r) W -> 65536 <= x < 0x5fa000 -> CJF.outside W x.
Proof.
induction W as [|[lo hi] W IH]; intros x HF Hx; cbn [CJF.outside]; [exact I|].
apply Forall_cons_iff in HF as [H0 HF]. cbn [fst snd] in H0. split; [lia | exact (IH x HF Hx)].
Qed.

(* the harness's store at an address the walk did not touch is the old one *)
Lemma munrestrict_out : forall H mem (m' : word -> option byte) (W : list (Z * Z)) (x : word),
  CJF.munch W (cjstore H mem) m' -> CJF.outside W (bv_unsigned x) -> munrestrict H mem m' x = mem x.
Proof.
intros H mem m' W x MU Ho. unfold munrestrict. destruct (H x) eqn:E; [reflexivity|].
rewrite (MU x Ho). unfold cjstore, mrestrict. rewrite E. reflexivity.
Qed.

Lemma aview_at_eq : forall H (m1 m2 : word -> option byte) a,
  m1 (Z_to_bv 64 a) = m2 (Z_to_bv 64 a) -> aview tfibsegs H m1 a = aview tfibsegs H m2 a.
Proof. intros H m1 m2 a E. unfold aview, mbyte, mrestrict. rewrite E. reflexivity. Qed.

Section P. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

(* 1. the frame, in the form munch states it: outside every (lo, hi) of W the view is the old one *)
Lemma win_view_out : forall H mem (m' : word -> option byte) (W : list (Z * Z)),
  CJF.munch W (cjstore H mem) m' ->
  (forall a, 0 <= a < 2 ^ 64 -> CJF.outside W a ->
     aview tfibsegs H (munrestrict H mem m') a = aview tfibsegs H mem a).
Proof.
intros H mem m' W MU a Ha Ho. apply aview_at_eq. apply (munrestrict_out H mem m' W); [exact MU|].
rewrite CJMS.unsigned_lit by lia. exact Ho.
Qed.

(* 1'. the frame with the miss written over in_zr (the harness's (p, len) form) on the same list:
   true only when every interval of W starts at 0 or above, which is the premise added *)
Lemma win_view : forall H mem (m' : word -> option byte) (W : list (Z * Z)),
  CJF.munch W (cjstore H mem) m' ->
  Forall (fun r => 0 <= fst r) W ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Exists (in_zr a) W ->
     aview tfibsegs H (munrestrict H mem m') a = aview tfibsegs H mem a).
Proof.
intros H mem m' W MU HF a Ha HN. apply (win_view_out H mem m' W MU a Ha).
exact (outside_of_not_in_zr W a HF HN).
Qed.

(* 2. nothing present goes away.  wmono alone does not give it: at an address a writable image
   segment backs, wview reads the segment's byte when the store has none, so a walk that dropped
   the stored byte there would still satisfy wmono.  The premise added closes exactly that gap. *)
Lemma win_present : forall H mem m',
  CJF.wmono tfibsegs (cjstore H mem) m' ->
  (forall a, apresent H mem a -> find_segment tfibsegs (bv_unsigned (Z_to_bv 64 a)) 1 <> None ->
     m' (Z_to_bv 64 a) <> None) ->
  (forall a, apresent H mem a -> apresent H (munrestrict H mem m') a).
Proof.
intros H mem m' WM SEG a Hp. pose proof Hp as (Hh & b & Hb). split; [exact Hh|].
unfold munrestrict. rewrite Hh.
destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:E; [exists b'; reflexivity|]. exfalso.
assert (Wv : wview tfibsegs m' (Z_to_bv 64 a) <> None).
{ apply WM. unfold wview, cjstore, mrestrict. rewrite Hh, Hb. cbv beta iota. discriminate. }
unfold wview in Wv. rewrite E in Wv.
destruct (find_segment tfibsegs (bv_unsigned (Z_to_bv 64 a)) 1) as [seg|] eqn:Hf; [|exact (Wv eq_refl)].
apply (SEG a Hp); [rewrite Hf; discriminate | exact E].
Qed.

(* 2'. the form GXA's post discharges: munch and wmono, every interval of the window off the image
   (GXA asks GLOBALS_TOP <= lo <= sp <= Fp < CK and D + dn <= 65536 \/ GLOBALS_TOP <= D) *)
Lemma win_present_off : forall H mem m' (Wn : list (Z * Z)),
  CJF.munch Wn (cjstore H mem) m' -> CJF.wmono tfibsegs (cjstore H mem) m' ->
  Forall (fun r => snd r <= 65536 \/ 0x5fa000 <= fst r) Wn ->
  (forall a, apresent H mem a -> apresent H (munrestrict H mem m') a).
Proof.
intros H mem m' Wn MU WM OFF. apply (win_present H mem m' WM).
intros a (Hh & b & Hb) Hf E.
destruct (find_segment tfibsegs (bv_unsigned (Z_to_bv 64 a)) 1) as [seg|] eqn:Hs; [|exact (Hf eq_refl)].
pose proof (tfib_seg_range _ seg Hs) as R.
rewrite (MU _ (outside_of_off_img Wn _ OFF R)) in E. unfold cjstore, mrestrict in E.
rewrite Hh, Hb in E. discriminate.
Qed.

(* 3. bytes the walk leaves at p, on a range the harness sees, are the harness's view there *)
Lemma view_of_bytes_at : forall H mem m' p (bs : list byte),
  CJM.bytes_at tfibsegs m' p bs ->
  (forall a, p <= a < p + Z.of_nat (length bs) -> H (Z_to_bv 64 a) = false) ->
  (forall i, (i < length bs)%nat ->
     aview tfibsegs H (munrestrict H mem m') (p + Z.of_nat i) = Some (bv_unsigned (nth i bs (Z_to_bv 8 0)))).
Proof.
intros H mem m' p bs (Hp & Hl & HB) HV i Hi.
rewrite aview_mrd. unfold cjstore. rewrite mrestrict_munrestrict.
assert (E : CJM.mrd tfibsegs (mrestrict H m') (CJM.wa (p + Z.of_nat i)) = CJM.mrd tfibsegs m' (CJM.wa (p + Z.of_nat i))).
{ unfold CJM.mrd, mrestrict, CJM.wa. rewrite (HV (p + Z.of_nat i)) by lia. reflexivity. }
assert (En : nth_error bs i = Some (nth i bs (Z_to_bv 8 0))) by (apply nth_error_nth'; exact Hi).
rewrite E, (HB i Hi), En. reflexivity.
Qed.

(* every byte the harness could read before, it can read after: a stored byte the walk dropped is
   still writable (wmono), and a writable byte of fm.asan is a readable segment byte *)
Lemma win_visible : forall H mem m',
  CJF.wmono tfibsegs (cjstore H mem) m' ->
  (forall a, aview tfibsegs H mem a <> None -> aview tfibsegs H (munrestrict H mem m') a <> None).
Proof.
intros H mem m' WM a Hv. unfold aview, mbyte in *. rewrite mrestrict_munrestrict.
set (x := Z_to_bv 64 a) in *. clearbody x.
unfold mrestrict in *. destruct (H x) eqn:Ex; [exact Hv|].
destruct (m' x) as [b|] eqn:Em; [cbv beta iota delta [option_map]; discriminate|].
destruct (mem x) as [b0|] eqn:E0; [|exact Hv].
assert (Wv : wview tfibsegs m' x <> None).
{ apply WM. unfold wview, cjstore, mrestrict. rewrite Ex, E0. cbv beta iota. discriminate. }
pose proof (seg_rom_of_wview m' x Wv Em) as R.
change (option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom tfibsegs x) <> None).
destruct (YK11.seg_rom tfibsegs x); [cbv beta iota delta [option_map]; discriminate | contradiction].
Qed.

Hypothesis LAWS : AR_laws tfibsegs B.

(* the window condition aru_of_window takes, from "each byte of Wn is on the stack or not owned"
   (scratch below sp: the stack holds no owned byte, al_stack; dest_ok: ~ aowned) *)
Lemma win_owned : forall ly S U W regs mem md (Wn : list (Z * Z)),
  ecall_preU tfibsegs B ly S U W regs mem md ->
  (forall a, 0 <= a < 2 ^ 64 -> Exists (fun r => fst r <= a < snd r) Wn ->
     (ly_stk_lo ly <= a < ly_stk_hi ly) \/ ~ aowned B ly S a) ->
  (forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> CJF.outside Wn a).
Proof.
intros ly S U W regs mem md Wn HPRE HW a Ha Hown.
destruct (outside_dec Wn a) as [Ho|HE]; [exact Ho|]. exfalso.
destruct (HW a Ha HE) as [Hs|Hn]; [|exact (Hn Hown)].
destruct HPRE as ((HAR & _) & _ & _).
exact (al_stack _ _ LAWS ly S W (unpoison U mem) md a HAR Hs Hown).
Qed.

(* 4. ARU after the walk.  FMupoison.ARU_frame (YG0d.v AR_frame_law with U) asks: every owned byte
   keeps its view, every visible byte stays visible, the model's maps are the same, the hidden
   bytes are the old ones.  munch gives the first for an owned byte outside Wn, so the window
   premise is that no owned byte lies in Wn (a user-poisoned shadow byte is owned, FMupoison
   ush_facts, so none lies there either); wmono with fm.asan's segments gives the second; the
   model does not change (md' = md); munrestrict gives the hidden bytes back. *)
Lemma aru_of_window : forall ly S U W regs mem md m' (Wn : list (Z * Z)),
  ecall_preU tfibsegs B ly S U W regs mem md ->
  CJF.munch Wn (cjstore (w_H W) mem) m' ->
  CJF.wmono tfibsegs (cjstore (w_H W) mem) m' ->
  (forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> CJF.outside Wn a) ->
  exists md', same_but_materialized md md' /\ ARU tfibsegs B ly S U W (munrestrict (w_H W) mem m') md'.
Proof.
intros ly S U W regs mem md m' Wn HPRE MU WM OWN.
exists md. split; [apply same_but_materialized_refl|].
destruct HPRE as ((HAR & _) & OK & PO).
apply (ARU_frame tfibsegs B LAWS ly S U W mem md (munrestrict (w_H W) mem m') md (conj HAR (conj OK PO))).
- intros a Ha Hown. exact (win_view_out (w_H W) mem m' Wn MU a Ha (OWN a Ha Hown)).
- exact (win_visible (w_H W) mem m' WM).
- reflexivity.
- reflexivity.
- reflexivity.
- intros a _ Hh. unfold munrestrict. rewrite Hh. reflexivity.
Qed.

End P.

(* 5. the FP state GxSeam quantifies, built from GXA's final Ft and fc' *)
Lemma frm0_mkFP : forall (Ft : bvmap 5 word) (fc : bv 32),
  CJFP.frm0 fc -> @fp_csr (YK11.mkFP Ft fc) = fc /\ @fp_regs (YK11.mkFP Ft fc) = Ft.
Proof. intros Ft fc _. split; reflexivity. Qed.

(* 6. the harness's configuration at a pc is CJ's machine state (MS sets ms_svc_pending := None;
   its fifth argument is ms_resv, None as YK11.mkst has it).  cfg_at takes {fx} segs and no rc, B. *)
Lemma cfg_of_ms : forall (fx' : YK11.FPState) regs' (pc : Z) (m : word -> option byte) md',
  @cfg_at fx' tfibsegs pc regs' m md'
  = mkCfg (CJMS.MS regs' (@fp_regs fx') (w64 pc) (@fp_csr fx') None m (YK11.seg_rom tfibsegs)) md'.
Proof. intros. reflexivity. Qed.
