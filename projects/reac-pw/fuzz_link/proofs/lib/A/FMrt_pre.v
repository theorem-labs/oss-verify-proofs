(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMrt_pre.v (a working branch 3e35620c52e); relocated to libreac/fuzz_disco.asan by g9/tool (reloc.py target disco-A): module paths changed; 0 address numerals moved (port_addr_check 0767e70e074a predict, fm.asan -> fuzz_disco.asan, symbol + offset; table g9/tool/tables/disco-A/FMrt_pre.table); hand checks: Bz.A.I_strncmpw STOP: no twin: strncmp / strncasecmp are absent from both disco images (P0 README; FMrt_pre drops its use). *)
(* Modified by Theorem Labs, 2026-10 (G9 row P5-A-clean-FMrt_pre, by hand after the tool): dropped `Require
   I_strncmpw`, `Module BSC`, icells_sc_of_ARm and icells_sc_of_ARm_clean (___interceptor_strncmp is absent from
   fuzz_disco.asan, so I_strncmpw has no twin; no route file uses the two lemmas), and dropped `Require
   ManifestModel` with find_byte_map (fm's program model has no disco twin; its only users, fm's FMmemchr.v and
   FMstrchr.v, are not on disco's route), and dropped icells_chr_of_ARm / icells_chr_of_ARm_clean (no route user:
   fm's only user is FMstrchr.v; disco's lib/A/AF0m.v Tfib_const has no 1-byte rows at the strchr interceptor's
   flag bytes 0x13acdd / 0x13ace5, only the 8-byte rows 0x13acd8 / 0x13ace0 holding the same bytes, so the exact
   cell_lookup the proof uses is None). Everything else is the tool's text. *)
(* fm's runtime contracts in the donor's form, the pre side (a Theorem Labs lane): from the premises of a contract of
   lib/A/FMH_Rt.v (ecall_pre_k, store_clean, cstr_ok / bytes_at, AR) to the premises of a Bz body walk
   (lib/A/Bz: Mem.bytes_at, Frame.stk, I_qck.chk_ok, mem_inv, the runtime's fixed cells), and what a Bz post
   says of the walk's stack window, in the words a Theorem Labs lane's lib/A/FMrt_lift.v rt_post_ro_win asks for.
   - bytes: FMH_Base's cstr / bytes_at are garr8 over the restricted memory, the same reader as Bz's mrd
     (FMbz_str.mbyte_mrd);
   - cells: each fixed cell is a row of the donor's constant table (lib/A/AF0m.v Tfib_const), read with
     AF0x.tfib_const_lookup; a writable cell also needs its addresses in a writable segment (computed);
   - stack: ecall_pre_k's window is Bz's stk (FMbz_bridge.stk_of_apresent), below the layout's top
     (YG0f.v lo_top) and above alloc_ceiling;
   - store: FMH_Base's store_clean gives Bz's mem_inv (FMbz_str);
   - range check: Bz's chk_ok from range_addressable and shadow_hull_vis (FMbz_str.chk_ok_of_AR), its
     region_in_mem from amem_range over n + 7;
   - (fm's find_byte_map, Bz find_byte vs ManifestModel.find_idx, is dropped here: see line 2);
   - entry: bz_canon writes FMrt_lift.canon_at as a Bz walk states its entry machine state. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YK0i YK14 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YI00 YI04 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m AF0x.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import SnUpoison.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import FMH_Base.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require FMbz_str FMbz_bridge FMrt_lift FMbz_clean.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Common.PropExec.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib.ImageA.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib.MState.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib.Exec.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib.Mem.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib.Frame.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib.Cells.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib.Step.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.A.Shadow.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.A.R_m2s.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.A.I_consts.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.A.I_qck.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.A.I_memchrw.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Spec.StrFun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module BPE := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Common.PropExec.
Module BI := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib.ImageA.
Module BMS := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib.MState.
Module BE := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib.Exec.
Module BM := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib.Mem.
Module BF := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib.Frame.
Module BC := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib.Cells.
Module BS := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib.Step.
Module BSh := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.A.Shadow.
Module BR := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.A.R_m2s.
Module BK := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.A.I_consts.
Module BQ := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.A.I_qck.
Module BMC := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.A.I_memchrw.
Module BSF := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Spec.StrFun.

(* ---- byte arithmetic ---- *)
Lemma u8z : forall c, 0 <= c < 256 -> bv_unsigned (Z_to_bv 8 c) = c.
Proof.
  intros c Hc. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  apply Z.mod_small. exact Hc.
Qed.

Lemma u64z : forall v, 0 <= v < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 v) = v.
Proof.
  intros v Hv. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  apply Z.mod_small. exact Hv.
Qed.

Lemma le_byte1 : forall v, 0 <= v < 256 -> Z_to_bv 8 (YO0f.le_byte v 1 0) = Z_to_bv 8 v.
Proof.
  intros v Hv. unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256. rewrite Z.mod_mod by lia. rewrite Z.mod_small by lia.
  reflexivity.
Qed.

Lemma nth_le_bytes : forall n z k, (k < n)%nat ->
  nth_error (Z_to_le_bytes n z) k = Some (Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k))).
Proof.
  induction n as [|n IH]; intros z k Hk; [lia|].
  destruct k as [|k]; cbn [Z_to_le_bytes nth_error].
  - replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r. reflexivity.
  - rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. do 3 f_equal. lia.
Qed.

Lemma le8_nth : forall v k, 0 <= v < 2 ^ 64 -> (k < 8)%nat ->
  nth_error (BM.le8 (Z_to_bv 64 v)) k = Some (Z_to_bv 8 (YO0f.le_byte v 8 k)).
Proof.
  intros v k Hv Hk. unfold BM.le8, word_to_le_bytes. rewrite nth_le_bytes by exact Hk.
  rewrite (u64z v Hv). f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap.
  change (8 * Z.of_nat 8) with 64. rewrite (Z.mod_small v (2 ^ 64)) by lia.
  change (bv_modulus 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.

(* the donor's reader and Bz's are one reader *)
Lemma mrd_mbyte : forall (m : word -> option byte) a, BM.mrd BI.asegs m (BM.wa a) = mbyte tfibsegs m a.
Proof. intros m a. reflexivity. Qed.

(* ---- bytes ---- *)
Lemma garr8_range : forall (m : word -> option byte) base (l : list Z),
  garr8 tfibsegs m base l -> Forall (fun c => 0 <= c < 256) l.
Proof.
  intros m base l HG. apply Forall_forall. intros c Hc. destruct (In_nth l c 0 Hc) as (j & Hj & <-).
  exact (proj2 (HG j Hj)).
Qed.

Lemma bytes_of_garr8 : forall (m : word -> option byte) base (l : list Z),
  0 <= base -> base + Z.of_nat (length l) <= 2 ^ 64 -> garr8 tfibsegs m base l ->
  BM.bytes_at BI.asegs m base (map (Z_to_bv 8) l).
Proof.
  intros m base l Hb Hl HG. split; [exact Hb|]. split; [rewrite length_map; exact Hl|].
  intros i Hi. rewrite length_map in Hi. destruct (HG i Hi) as (HV & HR).
  rewrite nth_error_map, (nth_error_nth' l 0 Hi). cbn [option_map].
  rewrite mrd_mbyte. specialize (HV 0%nat ltac:(lia)).
  replace (base + Z.of_nat i + Z.of_nat 0) with (base + Z.of_nat i) in HV by lia.
  rewrite HV, (le_byte1 _ HR). reflexivity.
Qed.

(* FMH_Base's bytes_at (a buffer the caller names) as Bz reads it *)
Lemma bytes_of_bytes_at : forall (W : world tfibsegs) mem p (l : list Z),
  FMH_Base.bytes_at tfibsegs W mem p l -> 0 <= p -> p + Z.of_nat (length l) <= 2 ^ 64 ->
  BM.bytes_at BI.asegs (mrestrict (w_H W) mem) p (map (Z_to_bv 8) l) /\ Forall (fun c => 0 <= c < 256) l.
Proof.
  intros W mem p l HB Hp Hl. split; [exact (bytes_of_garr8 _ p l Hp Hl HB) | exact (garr8_range _ p l HB)].
Qed.

(* a C string as Bz reads it: its bytes, then the NUL, and no NUL before *)
Lemma bytes_of_cstr : forall (W : world tfibsegs) mem p (l : list Z),
  cstr tfibsegs W mem p l -> 0 <= p -> p + Z.of_nat (length l) + 1 <= 2 ^ 64 ->
  BM.bytes_at BI.asegs (mrestrict (w_H W) mem) p (map (Z_to_bv 8) l ++ [Z_to_bv 8 0]) /\
  ~ In (Z_to_bv 8 0) (map (Z_to_bv 8) l) /\ Forall (fun c => 0 <= c < 256 /\ c <> 0) l.
Proof.
  intros W mem p l (HG & HNZ) Hp Hl.
  pose proof (garr8_range _ p _ HG) as HR. apply Forall_app in HR as (HR & _).
  split; [|split].
  - replace (map (Z_to_bv 8) l ++ [Z_to_bv 8 0]) with (map (Z_to_bv 8) (l ++ [0])) by (rewrite map_app; reflexivity).
    apply bytes_of_garr8; [exact Hp | rewrite length_app; cbn [length]; lia | exact HG].
  - intros Hin. apply in_map_iff in Hin as (c & Hc & Hin).
    pose proof (proj1 (Forall_forall _ _) HNZ c Hin) as Hc0. pose proof (proj1 (Forall_forall _ _) HR c Hin) as Hcr.
    apply Hc0. apply (f_equal bv_unsigned) in Hc. rewrite (u8z c Hcr) in Hc. rewrite Hc. reflexivity.
  - apply Forall_forall. intros c Hc. split; [exact (proj1 (Forall_forall _ _) HR c Hc) | exact (proj1 (Forall_forall _ _) HNZ c Hc)].
Qed.

(* ---- the runtime's fixed cells ---- *)
Lemma c8_of_val_mem : forall (m : word -> option byte) a v,
  0 <= a -> a + 8 <= 2 ^ 64 -> 0 <= v < 2 ^ 64 -> val_mem tfibsegs m a 8 v ->
  BS.ro_cells BI.asegs m a [BC.C8 (Z_to_bv 64 v)].
Proof.
  intros m a v Ha Ha8 Hv HV. unfold BS.ro_cells, BC.cells_at. split; [cbn; tauto|].
  cbn [BC.cells_bytes BC.cbytes]. rewrite app_nil_r.
  split; [exact Ha|]. split; [rewrite BM.length_le8; cbn; lia|].
  intros i Hi. rewrite BM.length_le8 in Hi. rewrite (le8_nth v i Hv Hi), mrd_mbyte. exact (HV i Hi).
Qed.

Lemma c1_of_val_mem : forall (m : word -> option byte) a v,
  0 <= a -> a + 1 <= 2 ^ 64 -> 0 <= v < 256 -> val_mem tfibsegs m a 1 v ->
  BS.ro_cells BI.asegs m a [BC.C1 (Z_to_bv 8 v)].
Proof.
  intros m a v Ha Ha1 Hv HV. unfold BS.ro_cells, BC.cells_at. split; [cbn; tauto|].
  cbn [BC.cells_bytes BC.cbytes app].
  split; [exact Ha|]. split; [cbn; lia|].
  intros i Hi. cbn [length] in Hi. assert (Hi0 : i = 0%nat) by lia. subst i.
  rewrite mrd_mbyte. cbn [nth_error]. rewrite (HV 0%nat ltac:(lia)), (le_byte1 v Hv). reflexivity.
Qed.

(* a byte a writable segment holds is a byte the store may be written at (lib/A/BzBridge.v wview_of_mrd, at
   fm.asan's segments) *)
Lemma wview_of_mrd : forall (m : word -> option byte) (x : word) b,
  BM.mrd BI.asegs m x = Some b -> BM.ro_addr BI.asegs x = false -> wview BI.asegs m x <> None.
Proof.
  intros m x b H R. unfold wview. destruct (m x) as [c|] eqn:E; [discriminate|].
  unfold BM.mrd in H. rewrite E in H. unfold BM.ro_addr in R. unfold BPE.seg_rom, memory_read in H.
  change (Z.of_N 1) with 1 in H.
  destruct (find_segment BI.asegs (bv_unsigned x) 1) as [s|]; [|discriminate H].
  apply negb_false_iff in R. rewrite R.
  destruct (seg_readable s); [|discriminate H].
  destruct (segment_byte_at (seg_bytes s) (Z.to_N (bv_unsigned x - Z.of_N (seg_base s)))) eqn:Eb; [discriminate|].
  exfalso. simpl in H. rewrite Eb in H. discriminate H.
Qed.

Definition rw_range (a : Z) (n : nat) : bool :=
  forallb (fun i => negb (BM.ro_addr BI.asegs (BM.wa (a + Z.of_nat i)))) (seq 0 n).

Lemma rw_of_ro : forall (m : word -> option byte) a cs,
  BS.ro_cells BI.asegs m a cs -> rw_range a (BC.cells_size cs) = true -> BS.rw_cells BI.asegs m a cs.
Proof.
  intros m a cs HC HRO. split; [exact HC|]. destruct HC as (Hwf & Hb).
  pose proof (BM.bytes_at_bound BI.asegs m a _ Hb) as (H0 & H1). rewrite (BC.cells_bytes_length cs Hwf) in H1.
  split; [exact H0|]. split; [exact H1|]. intros i Hi.
  destruct Hb as (_ & _ & Hb).
  specialize (Hb (Z.to_nat i) ltac:(rewrite (BC.cells_bytes_length cs Hwf); lia)).
  rewrite Z2Nat.id in Hb by lia.
  destruct (nth_error (BC.cells_bytes cs) (Z.to_nat i)) as [b|] eqn:E;
    [| apply nth_error_None in E; rewrite (BC.cells_bytes_length cs Hwf) in E; lia].
  apply (wview_of_mrd m _ b Hb).
  unfold rw_range in HRO. pose proof (proj1 (forallb_forall _ _) HRO (Z.to_nat i)) as Hi'.
  rewrite in_seq in Hi'. specialize (Hi' ltac:(lia)). rewrite Z2Nat.id in Hi' by lia.
  apply negb_true_iff in Hi'. exact Hi'.
Qed.

Lemma cells_cons : forall (m : word -> option byte) a c cs,
  BS.ro_cells BI.asegs m a [c] -> BS.ro_cells BI.asegs m (a + Z.of_nat (BC.csize c)) cs ->
  BS.ro_cells BI.asegs m a (c :: cs).
Proof.
  intros m a c cs (W1 & B1) (W2 & B2). destruct W1 as (Wc & _).
  split; [split; [exact Wc | exact W2]|].
  cbn [BC.cells_bytes] in B1 |- *. rewrite app_nil_r in B1.
  apply (proj2 (BM.bytes_at_app BI.asegs m a _ _)). split; [exact B1|].
  rewrite (BC.cbytes_length c Wc). exact B2.
Qed.

Lemma cells_cons8 : forall (m : word -> option byte) a w cs,
  BS.ro_cells BI.asegs m a [BC.C8 w] -> BS.ro_cells BI.asegs m (a + 8) cs ->
  BS.ro_cells BI.asegs m a (BC.C8 w :: cs).
Proof. intros m a w cs H1 H2. apply cells_cons; [exact H1 | exact H2]. Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis TB : PcapSyms B.

Lemma ro_c8 : forall ly S H mem a v, ARm B ly S (aview tfibsegs H mem) ->
  cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) 8 (AV (ANum v))) ->
  0 <= a -> a + 8 <= 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  BS.ro_cells BI.asegs (mrestrict H mem) a [BC.C8 (Z_to_bv 64 v)].
Proof.
  intros ly S H mem a v M E Ha Ha8 Hv. apply c8_of_val_mem; [exact Ha | exact Ha8 | exact Hv |].
  exact (tfib_const_lookup B TB ly S H mem a 8 v M E).
Qed.

Lemma ro_c1 : forall ly S H mem a v, ARm B ly S (aview tfibsegs H mem) ->
  cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) 1 (AV (ANum v))) ->
  0 <= a -> a + 1 <= 2 ^ 64 -> 0 <= v < 256 ->
  BS.ro_cells BI.asegs (mrestrict H mem) a [BC.C1 (Z_to_bv 8 v)].
Proof.
  intros ly S H mem a v M E Ha Ha1 Hv. apply c1_of_val_mem; [exact Ha | exact Ha1 | exact Hv |].
  exact (tfib_const_lookup B TB ly S H mem a 1 v M E).
Qed.

Local Ltac c8 M := eapply (ro_c8 _ _ _ _ _ _ M); [vm_compute; reflexivity | lia | lia | lia].
Local Ltac c1 M := eapply (ro_c1 _ _ _ _ _ _ M); [vm_compute; reflexivity | lia | lia | lia].

(* musl's and the interceptors' shared cells (Bz R_m2s.v:20) *)
Lemma m2s_of_ARm : forall ly S H mem, ARm B ly S (aview tfibsegs H mem) -> BR.m2s_cells (mrestrict H mem).
Proof.
  intros ly S H mem M. unfold BR.m2s_cells, BSh.SHB, BR.kHighMemEnd.
  split; [|split]; (apply rw_of_ro; [|vm_compute; reflexivity]).
  - apply cells_cons8; [c8 M|]. apply cells_cons8; [c8 M|]. apply cells_cons8; [c8 M|]. c8 M.
  - c8 M.
  - apply cells_cons8; [c8 M|]. apply cells_cons8; [c8 M|]. c8 M.
Qed.

(* the memchr interceptor's cells (Bz I_memchrw.v:29) *)
Lemma icells_mc_of_ARm : forall ly S H mem, ARm B ly S (aview tfibsegs H mem) -> BMC.icells_mc (mrestrict H mem).
Proof.
  intros ly S H mem M. unfold BMC.icells_mc.
  split; [|split; [|split]].
  - c8 M.
  - c8 M.
  - c8 M.
  - apply rw_of_ro; [c1 M | vm_compute; reflexivity].
Qed.

(* the same fixed cells on the cleaned store: each cell lies below 2^47 and holds the bytes it held, and a
   writable cell's addresses are writable in the image (decided) *)
Local Ltac roc RE H :=
  apply (FMbz_clean.ro_cells_clean _ _ _ RE); [cbn; unfold BM.UTOP; lia | exact H].
Local Ltac rwc RE H :=
  apply (FMbz_clean.rw_cells_clean _ _ _ RE);
  [lia | cbn; unfold BM.UTOP; lia | vm_compute; reflexivity | exact H].

Lemma m2s_of_ARm_clean : forall ly S H mem, FMbz_clean.rom_eq (mrestrict H mem) ->
  ARm B ly S (aview tfibsegs H mem) -> BR.m2s_cells (FMbz_clean.clean (mrestrict H mem)).
Proof.
  intros ly S H mem RE M. destruct (m2s_of_ARm ly S H mem M) as (C1 & C2 & C3).
  split; [|split].
  - rwc RE C1.
  - rwc RE C2.
  - rwc RE C3.
Qed.

Lemma icells_mc_of_ARm_clean : forall ly S H mem, FMbz_clean.rom_eq (mrestrict H mem) ->
  ARm B ly S (aview tfibsegs H mem) -> BMC.icells_mc (FMbz_clean.clean (mrestrict H mem)).
Proof.
  intros ly S H mem RE M. destruct (icells_mc_of_ARm ly S H mem M) as (C1 & C2 & C3 & C4).
  split; [|split; [|split]].
  - roc RE C1.
  - roc RE C2.
  - roc RE C3.
  - rwc RE C4.
Qed.

(* ---- stack, store, range check ---- *)
(* the callee's stack window: Bz's stk over [sp - STK, sp), above alloc_ceiling (so above every heap or image
   byte a string can sit in, and above Bz's kHighShadowEnd), and sp at most 2^47 *)
Lemma stk_of_pre : forall ly S (W : world tfibsegs) regs mem md STK,
  ecall_pre_k tfibsegs B STK ly S W regs mem md -> 0 <= STK ->
  BF.stk BI.asegs (mrestrict (w_H W) mem) (spZ regs - STK) (spZ regs) /\
  0x7fff7f800000 <= alloc_ceiling /\ alloc_ceiling <= spZ regs - STK /\ spZ regs <= 2 ^ 47.
Proof.
  intros ly S W regs mem md STK (HEP & HAC & HLO & HW) HS.
  pose proof HEP as (HAR & _ & _ & _ & HHI & _).
  pose proof (lo_top ly (am_layout B ly S _ (proj1 HAR))) as (_ & _ & _ & Lhi & _ & _ & _).
  pose proof ASAN_CEIL_range as ((C1 & C2) & _). unfold ASAN_CEIL in C1, C2.
  unfold kHighMemEnd in Lhi.
  split; [apply FMbz_bridge.stk_of_apresent; [lia | lia | exact HW] | lia].
Qed.

Lemma ra_prefix : forall rd p n n', range_addressable rd SHADOW_OFF p n -> n' <= n ->
  range_addressable rd SHADOW_OFF p n'.
Proof. intros rd p n n' H Hn x Hx. apply H. lia. Qed.

Lemma hull_prefix : forall rd p n n', shadow_hull_vis rd p n -> 0 < n' <= n -> shadow_hull_vis rd p n'.
Proof.
  intros rd p n n' H Hn s Hs. apply H. unfold shadow_addr in *.
  assert ((p + n' - 1) / 8 <= (p + n - 1) / 8) by (apply Z.div_le_mono; lia).
  assert ((SHADOW_OFF + (p + n' - 1) / 8) / 8 <= (SHADOW_OFF + (p + n - 1) / 8) / 8) by (apply Z.div_le_mono; lia).
  lia.
Qed.

Lemma amem_range_mono : forall p a b, amem_range p a -> 0 <= b <= a -> amem_range p b.
Proof. intros p a b H Hb. unfold amem_range in *. lia. Qed.

(* the interceptors' range check over [p, p + n) *)
Lemma chk_ok_of_pre : forall ly S (W : world tfibsegs) mem md p n,
  AR tfibsegs B ly S W mem md -> 0 <= p -> 0 <= n < 2 ^ 32 -> amem_range p (n + 7) ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF p n ->
  (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) p n) ->
  BQ.chk_ok (mrestrict (w_H W) mem) p n.
Proof.
  intros ly S W mem md p n HAR Hp Hn Ham HRA HV.
  destruct (Z.eq_dec n 0) as [->|Hn0].
  - split; [intros i Hi; lia|]. split; [intros Hq; lia | intros Hq; lia].
  - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham.
    apply (FMbz_str.chk_ok_of_AR B ly S W mem md p n HAR); [exact Hp | lia | lia | lia | | exact HRA | exact (HV ltac:(lia))].
    unfold BK.region_in_mem, BR.kLowMemEnd, BR.kHighShadowEnd, BR.kHighMemEnd. lia.
Qed.

(* a C string's range check over its first n <= len + 1 bytes *)
Lemma chk_ok_of_cstr : forall ly S (W : world tfibsegs) mem md p (l : list Z) n,
  AR tfibsegs B ly S W mem md -> cstr_ok tfibsegs W mem p l -> 0 <= n <= Z.of_nat (length l) + 1 ->
  BQ.chk_ok (mrestrict (w_H W) mem) p n.
Proof.
  intros ly S W mem md p l n HAR (_ & Hp & _ & H32 & Ham & HRA & HV & _) Hn.
  apply (chk_ok_of_pre ly S W mem md p n HAR); [lia | lia | apply (amem_range_mono _ _ _ Ham); lia | |].
  - apply (ra_prefix _ _ _ _ HRA). lia.
  - intros Hn0. apply (hull_prefix _ _ _ _ HV). lia.
Qed.

End c.

(* what a Bz post says of the memory, in the words FMrt_lift.rt_post_ro_win asks for: outside the walk's window
   [sp - K, sp) the store is the caller's, and inside it every byte is in the store (the window is above the
   image, so a readable byte there is a stored byte) *)
Lemma bz_window : forall (m m' : word -> option byte) (sp K lo : Z),
  BF.munch [(sp - K, sp)] m m' -> BF.stk BI.asegs m' lo sp -> lo <= sp - K -> TFIB_IMG_END <= lo ->
  (forall x : word, ~ (sp - K <= bv_unsigned x < sp) -> m' x = m x) /\
  (forall a, sp - K <= a < sp -> m' (Z_to_bv 64 a) <> None).
Proof.
  intros m m' sp K lo MU (Hlo & Hhi & ST) Hk Himg. split.
  - intros x Hx. apply MU. cbn [BF.outside]. split; [exact Hx | exact I].
  - intros a Ha. destruct (ST a ltac:(lia)) as (_ & b & Hb). unfold BM.mrd, BM.wa in Hb.
    destruct (m' (Z_to_bv 64 a)) as [c|] eqn:E; [discriminate|].
    assert (HN : BPE.seg_rom BI.asegs (Z_to_bv 64 a) = None) by exact (seg_rom_none_high a ltac:(lia)).
    rewrite HN in Hb. discriminate.
Qed.

Section k. Context {fx : YK11.FPState}.
(* a Theorem Labs lane's canonical entry state (FMrt_lift.canon_at) written in a Bz walk's own words, so that the walk's
   statement applies to it as it stands *)
Lemma bz_canon : forall (Q : machine_state -> Prop) (regs : bvmap 5 word) pc (m : word -> option byte),
  BE.evt BI.asegs Q
    (BMS.MS (BF.mkR (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4) (reg_get regs 5)
              (reg_get regs 6) (reg_get regs 7) (reg_get regs 8) (reg_get regs 9) (reg_get regs 10)
              (reg_get regs 11) (reg_get regs 12) (reg_get regs 13) (reg_get regs 14) (reg_get regs 15)
              (reg_get regs 16) (reg_get regs 17) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20)
              (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25)
              (reg_get regs 26) (reg_get regs 27) (reg_get regs 28) (reg_get regs 29) (reg_get regs 30)
              (reg_get regs 31))
            fp_regs (Z_to_bv 64 pc) fp_csr None m (seg_rom BI.asegs)) ->
  BE.evt BI.asegs Q (FMrt_lift.canon_at regs pc m).
Proof. intros Q regs pc m H. exact H. Qed.
End k.
