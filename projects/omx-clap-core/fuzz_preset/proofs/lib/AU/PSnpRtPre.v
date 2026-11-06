(* fm's runtime contracts in the donor's form, the pre side (RtScan lane): from the premises of a contract of
   lib/A/FMH_Rt.v (ecall_pre_k, store_clean, cstr_ok / bytes_at, AR) to the premises of a Bz body walk
   (lib/A/Bz: Mem.bytes_at, Frame.stk, I_qck.chk_ok, mem_inv, the runtime's fixed cells), and what a Bz post
   says of the walk's stack window, in the words RtStr's lib/A/PSnpRtLift.v rt_post_ro_win asks for.
   - bytes: FMH_Base's cstr / bytes_at are garr8 over the restricted memory, the same reader as Bz's mrd
     (PSnpBzStr.mbyte_mrd);
   - cells: each fixed cell is a row of the donor's constant table (lib/A/YF0m.v Tfib_const), read with
     YF0x.tfib_const_lookup; a writable cell also needs its addresses in a writable segment (computed);
   - stack: ecall_pre_k's window is Bz's stk (PSnpBzBridge.stk_of_apresent), below the layout's top
     (YG0f.v lo_top) and above alloc_ceiling;
   - store: FMH_Base's store_clean gives Bz's mem_inv (FMbz_str);
   - range check: Bz's chk_ok from range_addressable and shadow_hull_vis (PSnpBzStr.chk_ok_of_AR), its
     region_in_mem from amem_range over n + 7;
   - answers: Bz's find_byte over a string's bytes is ManifestModel.find_idx over their values;
   - entry: bz_canon writes PSnpRtLift.canon_at as a Bz walk states its entry machine state. *)
(* Modified by Theorem Labs, 2026-10: c-libc-stdio's copy for fuzz_preset image A (route (a) P2, ASan's printf_common over ARx; parent c-libc-stdio 13:0xZ) of proofs/omx-clap-core/fuzz_manifest/lib/A/FMrt_pre.v at origin/cold/port-fm-rtprintf-param 7e395de08f5: module paths fuzz_manifest -> fuzz_preset, lib/A/Bz -> lib/A/PSnpBz (the Bz files relocated to image A by c-asan's alreloc), FM glue modules -> their PSnp twins; ro_c8 / ro_c1 / m2s_of_ARm restated over the engine's ARx with the ghost list Hp (m2s_of_x), the constant cells from AR_laws_x's alx_const_cells through PSnpRodata.const_lookup_lx (in place of ARm and tfib_const_lookup); the strchr / memchr / strncmp interceptor cells and their imports (I_strchrw, I_memchrw, I_strncmpw), the FMH_Base / ManifestModel items (bytes_of_bytes_at, bytes_of_cstr, find_byte_map, stk_of_pre) and the AR range checks (chk_ok_of_pre, chk_ok_of_cstr) are left out, unreached by the printf_common contract. No numeral changes (the cell numerals are computed from Tfib_const by vm_compute). *)
(* Modified by Theorem Labs, 2026-10: image B twin (fuzz_preset.asan-ubsan f8f98a95) of lib/A/PSnpRtPre.v, by the unit's image-B convention (lib/AU/FCxA.v's rule): module paths lib/A/PSnpBz -> lib/AU/PSnpBz (alreloc's image-B relocation), the image-A core A<x> -> image B's Y<x> (lib/Reusable), lib/A/Img0 -> lib/B/Img0, the PSnp glue lib/A -> lib/AU. Sentences above that name image A describe the A twin. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YK0i YK14 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YI00 YI04 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YF0m YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PSnpRodata.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PSnpBzStr PSnpBzBridge PSnpRtLift PSnpBzClean.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.Common.PropExec.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.Lib.ImageA.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.Lib.MState.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.Lib.Exec.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.Lib.Mem.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.Lib.Frame.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.Lib.Cells.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.Lib.Step.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.A.Shadow.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.A.R_m2s.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.A.I_consts.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.A.I_qck.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.Spec.StrFun.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module BPE := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.Common.PropExec.
Module BI := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.Lib.ImageA.
Module BMS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.Lib.MState.
Module BE := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.Lib.Exec.
Module BM := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.Lib.Mem.
Module BF := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.Lib.Frame.
Module BC := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.Lib.Cells.
Module BS := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.Lib.Step.
Module BSh := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.A.Shadow.
Module BR := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.A.R_m2s.
Module BK := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.A.I_consts.
Module BQ := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.A.I_qck.
Module BSF := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.Spec.StrFun.

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
(* a C string as Bz reads it: its bytes, then the NUL, and no NUL before *)
(* the walks' byte search (Bz find_byte) on a string's bytes is fm's model search on their values *)
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
Variable ARx : alayout -> astate -> list Z -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
(* the one AR_laws_x field these cells need (YCbqG.v), and the image's symbol binding *)
Hypothesis alx_const_cells : ARx_const_cells_law tfibsegs B ARx.
Hypothesis TB : TfibSyms B.

Lemma ro_c8 : forall ly S Hp W mem md a v, ARx ly S Hp W mem md ->
  cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) 8 (AV (ANum v))) ->
  0 <= a -> a + 8 <= 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  BS.ro_cells BI.asegs (mrestrict (w_H W) mem) a [BC.C8 (Z_to_bv 64 v)].
Proof.
  intros ly S Hp W mem md a v HAR E Ha Ha8 Hv. apply c8_of_val_mem; [exact Ha | exact Ha8 | exact Hv |].
  exact (PSnpRodata.const_lookup_lx B ARx alx_const_cells TB ly S Hp W mem md a 8 v HAR E).
Qed.

Lemma ro_c1 : forall ly S Hp W mem md a v, ARx ly S Hp W mem md ->
  cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) 1 (AV (ANum v))) ->
  0 <= a -> a + 1 <= 2 ^ 64 -> 0 <= v < 256 ->
  BS.ro_cells BI.asegs (mrestrict (w_H W) mem) a [BC.C1 (Z_to_bv 8 v)].
Proof.
  intros ly S Hp W mem md a v HAR E Ha Ha1 Hv. apply c1_of_val_mem; [exact Ha | exact Ha1 | exact Hv |].
  exact (PSnpRodata.const_lookup_lx B ARx alx_const_cells TB ly S Hp W mem md a 1 v HAR E).
Qed.

Local Ltac c8 M := eapply (ro_c8 _ _ _ _ _ _ _ _ M); [vm_compute; reflexivity | lia | lia | lia].

(* musl's and the interceptors' shared cells (Bz R_m2s.v:20) *)
Lemma m2s_of_x : forall ly S Hp W mem md, ARx ly S Hp W mem md -> BR.m2s_cells (mrestrict (w_H W) mem).
Proof.
  intros ly S Hp W mem md M. unfold BR.m2s_cells, BSh.SHB, BR.kHighMemEnd.
  split; [|split]; (apply rw_of_ro; [|vm_compute; reflexivity]).
  - apply cells_cons8; [c8 M|]. apply cells_cons8; [c8 M|]. apply cells_cons8; [c8 M|]. c8 M.
  - c8 M.
  - apply cells_cons8; [c8 M|]. apply cells_cons8; [c8 M|]. c8 M.
Qed.

End c.

(* what a Bz post says of the memory, in the words PSnpRtLift.rt_post_ro_win asks for: outside the walk's window
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
(* RtStr's canonical entry state (PSnpRtLift.canon_at) written in a Bz walk's own words, so that the walk's
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
  BE.evt BI.asegs Q (PSnpRtLift.canon_at regs pc m).
Proof. intros Q regs pc m H. exact H. Qed.
End k.
