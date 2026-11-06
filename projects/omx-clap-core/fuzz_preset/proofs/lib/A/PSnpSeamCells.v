(* Step 2 of the evt -> SRr seam at musl vfprintf: the harness's WORDS and WRITABILITY as the CJ
   tree's CELLS.

   The shared contract (FMsnprintfShared.v) states memory as `rdword` reads of whole words
   (`words_at`, the stack-protector cells gc -> gv -> cval) and as `writable_at` per byte.  The
   released GXA statement (lib/CJ/RL/GXA/VfprintfCall.v, G_vfprintf_snf.v) asks for `rw_cells`
   (CJ/Lib/Step.v:25): a cell list whose bytes the store holds (`cells_at`) and whose span the
   store may write (`wr_at`).  Everything here goes through one fact, `bytes_of_rdword`: the
   little-endian bytes a word read sees are the bytes of `C8 (w64 v)`.

   musl vsnprintf's FILE: the harness's `sn_file snw bp cp` is 29 words; GXA's `snf_file bp cp`
   is 33 cells over the same 232 bytes (it splits words 0, 15, 17 and 18 into C4 halves).  The two
   byte strings are equal when snw is GXA's `sym K_SN_WRITE` (rw_cells_snf_file).

   GXA's va_list slots (`va_area`, G_pop_arg.v:456) are the same words as the contract's
   `words_at`, in both directions (va_area_words_at_iff). *)
(* Modified by Theorem Labs, 2026-10: c-libc-stdio's copy for fuzz_preset image A (L3-V2, the GXA seam over ARx, helper H2; parent c-libc-stdio 15:0xZ, split scratch/vfp/SEAM-SPLIT.txt) of proofs/omx-clap-core/fuzz_manifest/lib/A/FMgxaSeamCells.v at origin/cold/port-fm-rtprintf-param 3e35620c52e: module paths fuzz_manifest -> fuzz_preset; the image record RT_IImgA.A_img -> preset's rebuilt-pin lib/CJ/RL/I/IImgA.v N_img_asan (c-libc-str f697dea427f); FMsnprintfShared -> Reusable/PSnpShared (sn_file, words_at); FMgxaSeamBase -> A/PSnpSeamBase. R7 numerals (preset A, by vm_compute against N_img_asan): ssp_cells_of_view's @sym N_img_asan 0x22e18 = 0xa2758 and @sym N_img_asan 0x34288 = 0x5fd910 (fm 0x9a638 / 0x5f4db0). No AR, no U. Runtime-option cells (c-omx-hpreset 15:22Z): this file holds no walk and reads no option cell. The sentences above name fm's files. *)
(* Modified by Theorem Labs, 2026-10: moved to the #102 pins, image A' (fuzz_preset.asan 1be0f53d, unstripped bff8519b), from the old-pin donor origin/cold/c-libc-stdio-presetsnp-vfp ac1750cac8be: every code numeral by symbol + offset by c-asan's alreloc of record (frame/alreloc.py.frozen-c4338d099cfb8025, --src omx-clap-core/fuzz_preset --src-pin d83eb25d --assume-source; the chain's code is equal old -> #102); kept as written: the IImg record keys (fm addresses), the instruction words and the segment sizes; audited by port_addr_check 0767e70e074a (only the record keys flag). Per-numeral table: c-libc-stdio scratch/p102/reloc/A/PSnpSeamCells.v.reloc.tsv. Comment numerals are as written (sentences above that name preset A's addresses describe the old pin). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK04 YK0i YK0s YK14 YK1b YK1a YK18 YP09 YG0n YG00 YG0a YG01 YG0f YG0d YA0n YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.Lib Require Mem Cells Step Arr.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.G Require G_pad G_pop_arg.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GX Require G_printf_core_common G_vfprintf_snf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.I Require Import IImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import PSnpShared.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PSnpSeamBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.

(* ---- byte arithmetic ---- *)
Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof.
intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R.
change (2 ^ Z.of_N 8) with 256 in R. exact R.
Qed.

(* one step of Z_to_le_bytes on a value whose low byte is c *)
Lemma le_bytes_cons : forall n (c : byte) r, 0 <= r ->
  Z_to_le_bytes (S n) (bv_unsigned c + 256 * r) = c :: Z_to_le_bytes n r.
Proof.
intros n c r Hr. pose proof (byte_range c) as Hc. cbn [Z_to_le_bytes]. f_equal.
- apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  rewrite Z.mul_comm, Z_mod_plus_full. apply Z.mod_small. exact Hc.
- f_equal. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  rewrite Z.mul_comm, Z.div_add by lia. rewrite Z.div_small by exact Hc. lia.
Qed.

Lemma bytes_unsigned_inj : forall l1 l2 : list byte,
  map (@bv_unsigned 8) l1 = map (@bv_unsigned 8) l2 -> l1 = l2.
Proof.
induction l1 as [|b l1 IH]; intros [|c l2] E; cbn [map] in E; try discriminate; [reflexivity|].
injection E as Eb El. f_equal; [apply bv_eq; exact Eb | apply IH; exact El].
Qed.

(* the eight bytes of a C8 cell are the little-endian digits of its value *)
Lemma le8_w64_bytes : forall b0 b1 b2 b3 b4 b5 b6 b7 : byte,
  Cells.cbytes (Cells.C8 (w64 (bv_unsigned b0 + 256 * (bv_unsigned b1 + 256 * (bv_unsigned b2 +
    256 * (bv_unsigned b3 + 256 * (bv_unsigned b4 + 256 * (bv_unsigned b5 + 256 * (bv_unsigned b6 +
    256 * bv_unsigned b7))))))))) = [b0; b1; b2; b3; b4; b5; b6; b7].
Proof.
intros b0 b1 b2 b3 b4 b5 b6 b7.
pose proof (byte_range b0). pose proof (byte_range b1). pose proof (byte_range b2). pose proof (byte_range b3).
pose proof (byte_range b4). pose proof (byte_range b5). pose proof (byte_range b6). pose proof (byte_range b7).
cbn [Cells.cbytes]. unfold Mem.le8, word_to_le_bytes, w64. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
rewrite !le_bytes_cons by lia. cbn [Z_to_le_bytes]. rewrite byte_roundtrip. reflexivity.
Qed.

(* ---- 1. a word read is the bytes of its C8 cell ---- *)
Lemma bytes_of_rdword : forall H mem a v, 0 <= a -> a + 8 <= 2 ^ 64 ->
  rdword (aview tfibsegs H mem) a = Some v ->
  Mem.bytes_at tfibsegs (cjstore H mem) a (Cells.cbytes (Cells.C8 (w64 v))).
Proof.
intros H mem a v Ha Hhi Hw. unfold rdword in Hw. rewrite !aview_mrd in Hw.
destruct (Mem.mrd tfibsegs (cjstore H mem) (Mem.wa a)) as [b0|] eqn:E0; [|discriminate].
destruct (Mem.mrd tfibsegs (cjstore H mem) (Mem.wa (a + 1))) as [b1|] eqn:E1; [|discriminate].
destruct (Mem.mrd tfibsegs (cjstore H mem) (Mem.wa (a + 2))) as [b2|] eqn:E2; [|discriminate].
destruct (Mem.mrd tfibsegs (cjstore H mem) (Mem.wa (a + 3))) as [b3|] eqn:E3; [|discriminate].
destruct (Mem.mrd tfibsegs (cjstore H mem) (Mem.wa (a + 4))) as [b4|] eqn:E4; [|discriminate].
destruct (Mem.mrd tfibsegs (cjstore H mem) (Mem.wa (a + 5))) as [b5|] eqn:E5; [|discriminate].
destruct (Mem.mrd tfibsegs (cjstore H mem) (Mem.wa (a + 6))) as [b6|] eqn:E6; [|discriminate].
destruct (Mem.mrd tfibsegs (cjstore H mem) (Mem.wa (a + 7))) as [b7|] eqn:E7; [|discriminate].
cbn [option_map] in Hw. injection Hw as <-.
rewrite le8_w64_bytes. split; [exact Ha|]. split; [exact Hhi|].
intros i Hi. destruct i as [|[|[|[|[|[|[|[|i]]]]]]]].
- change (Z.of_nat 0) with 0. rewrite Z.add_0_r. exact E0.
- exact E1.
- exact E2.
- exact E3.
- exact E4.
- exact E5.
- exact E6.
- exact E7.
- cbn [length] in Hi. lia.
Qed.

(* ---- words ---- *)
Lemma words_at_head : forall (rd : reader) p v ws, words_at rd p (v :: ws) -> rdword rd p = Some v.
Proof.
intros rd p v ws Hw. specialize (Hw 0%nat ltac:(cbn [length]; lia)). cbn [nth] in Hw.
change (Z.of_nat 0) with 0 in Hw. rewrite Z.mul_0_r, Z.add_0_r in Hw. exact Hw.
Qed.

Lemma words_at_tail : forall (rd : reader) p v ws, words_at rd p (v :: ws) -> words_at rd (p + 8) ws.
Proof.
intros rd p v ws Hw i Hi. specialize (Hw (S i) ltac:(cbn [length]; lia)). cbn [nth] in Hw.
replace (p + 8 + 8 * Z.of_nat i) with (p + 8 * Z.of_nat (S i)) by lia. exact Hw.
Qed.

Lemma cells_size_words : forall ws : list Z,
  Cells.cells_size (map (fun v => Cells.C8 (w64 v)) ws) = (8 * length ws)%nat.
Proof.
induction ws as [|v ws IH]; cbn [map Cells.cells_size Cells.csize length]; [reflexivity|].
rewrite IH. lia.
Qed.

(* ---- 2. words the harness reads are C8 cells ---- *)
Lemma cells_at_of_words : forall H mem p (ws : list Z), 0 <= p ->
  p + 8 * Z.of_nat (length ws) <= 2 ^ 64 ->
  words_at (aview tfibsegs H mem) p ws ->
  Cells.cells_at tfibsegs (cjstore H mem) p (map (fun v => Cells.C8 (w64 v)) ws).
Proof.
intros H mem p ws. revert p. induction ws as [|v ws IH]; intros p Hp Hhi Hw.
- cbn [map]. unfold Cells.cells_at. split; [exact I|]. cbn [Cells.cells_bytes].
  apply Mem.bytes_at_nil. cbn [length] in Hhi. change (Z.of_nat 0) with 0 in Hhi. lia.
- cbn [map]. unfold Cells.cells_at. cbn [Cells.cells_wf Cells.cell_wf Cells.cells_bytes].
  cbn [length] in Hhi.
  destruct (IH (p + 8) ltac:(lia) ltac:(lia) (words_at_tail _ _ _ _ Hw)) as [IW IB].
  split; [split; [exact I | exact IW]|].
  apply (proj2 (Mem.bytes_at_app tfibsegs _ _ _ _)). split.
  + exact (bytes_of_rdword H mem p v Hp ltac:(lia) (words_at_head _ _ _ _ Hw)).
  + cbn [Cells.cbytes]. rewrite Mem.length_le8. exact IB.
Qed.

(* ---- GXA's va_area (G_pop_arg.v:456) over the same words ---- *)
Lemma u64s_words : forall ws : list Z,
  Arr.u64s (map w64 ws) = Cells.cells_bytes (map (fun v => Cells.C8 (w64 v)) ws).
Proof.
induction ws as [|v ws IH]; cbn [map Arr.u64s Cells.cells_bytes Cells.cbytes]; [reflexivity|].
rewrite IH. reflexivity.
Qed.

Lemma nth_error_u64s : forall (ws : list word) (d : word) i k, (i < length ws)%nat -> (k < 8)%nat ->
  nth_error (Arr.u64s ws) (8 * i + k) = nth_error (Mem.le8 (nth i ws d)) k.
Proof.
induction ws as [|w ws IH]; intros d i k Hi Hk; [cbn [length] in Hi; lia|].
cbn [Arr.u64s]. destruct i as [|i]; cbn [nth].
- rewrite Nat.mul_0_r, Nat.add_0_l. apply nth_error_app1. rewrite Mem.length_le8. exact Hk.
- rewrite nth_error_app2 by (rewrite Mem.length_le8; lia). rewrite Mem.length_le8.
  replace (8 * S i + k - 8)%nat with (8 * i + k)%nat by lia. cbn [length] in Hi. apply IH; lia.
Qed.

(* the pairing port-reply's snf_spill_ok and the SRr-side callers meet through: GXA's slot
   predicate over the plain byte model versus the shared contract's word reader.
   Instance at the vsnprintf geometry: VA = S - 40, ws = map (argZ regs) [3;4;5;6;7] ++ xs. *)
Lemma va_area_words_at_iff : forall H mem (VA : Z) (ws : list Z),
  0 <= VA -> VA + 8 * Z.of_nat (length ws) <= 2 ^ 64 ->
  Forall (fun v => 0 <= v < 2 ^ 64) ws ->
  (@G_pop_arg.va_area N_img_asan (cjstore H mem) VA (map w64 ws)
     <-> words_at (aview tfibsegs H mem) VA ws).
Proof.
intros H mem VA ws HVA Hhi HF. unfold G_pop_arg.va_area. split.
- intros (_ & _ & HB) i Hi.
  assert (Hw : 0 <= nth i ws 0 < 2 ^ 64).
  { apply (proj1 (Forall_forall _ _) HF). apply nth_In. exact Hi. }
  assert (HK : forall k, (k < 8)%nat ->
    Mem.mrd tfibsegs (cjstore H mem) (Mem.wa (VA + 8 * Z.of_nat i + Z.of_nat k))
    = nth_error (Mem.le8 (w64 (nth i ws 0))) k).
  { intros k Hk. rewrite Arr.u64s_length, length_map in HB.
    specialize (HB (8 * i + k)%nat ltac:(lia)).
    rewrite (nth_error_u64s (map w64 ws) (w64 0) i k) in HB by (rewrite ?length_map; lia).
    rewrite map_nth in HB.
    replace (VA + 8 * Z.of_nat i + Z.of_nat k) with (VA + Z.of_nat (8 * i + k)) by lia.
    exact HB. }
  pose proof (Mem.length_le8 (w64 (nth i ws 0))) as L8. revert HK L8.
  destruct (Mem.le8 (w64 (nth i ws 0))) as [|c0 [|c1 [|c2 [|c3 [|c4 [|c5 [|c6 [|c7 [|c8 l]]]]]]]]] eqn:EL;
    intros HK L8; cbn [length] in L8; try lia.
  set (P := VA + 8 * Z.of_nat i) in *.
  pose proof (HK 0%nat ltac:(lia)) as K0. pose proof (HK 1%nat ltac:(lia)) as K1.
  pose proof (HK 2%nat ltac:(lia)) as K2. pose proof (HK 3%nat ltac:(lia)) as K3.
  pose proof (HK 4%nat ltac:(lia)) as K4. pose proof (HK 5%nat ltac:(lia)) as K5.
  pose proof (HK 6%nat ltac:(lia)) as K6. pose proof (HK 7%nat ltac:(lia)) as K7.
  cbn [nth_error] in K0, K1, K2, K3, K4, K5, K6, K7.
  change (Z.of_nat 0) with 0 in K0. rewrite Z.add_0_r in K0.
  change (Z.of_nat 1) with 1 in K1. change (Z.of_nat 2) with 2 in K2. change (Z.of_nat 3) with 3 in K3.
  change (Z.of_nat 4) with 4 in K4. change (Z.of_nat 5) with 5 in K5. change (Z.of_nat 6) with 6 in K6.
  change (Z.of_nat 7) with 7 in K7.
  unfold rdword. rewrite !aview_mrd. rewrite K0, K1, K2, K3, K4, K5, K6, K7. cbn [option_map].
  f_equal.
  pose proof (byte_range c0). pose proof (byte_range c1). pose proof (byte_range c2). pose proof (byte_range c3).
  pose proof (byte_range c4). pose proof (byte_range c5). pose proof (byte_range c6). pose proof (byte_range c7).
  pose proof (le8_w64_bytes c0 c1 c2 c3 c4 c5 c6 c7) as EV. cbn [Cells.cbytes] in EV. rewrite <- EL in EV.
  apply (f_equal le_bytes_to_word) in EV. rewrite !Mem.le_bytes_to_word_le8 in EV.
  apply (f_equal (fun x : word => bv_unsigned x)) in EV. cbv beta in EV. unfold w64 in EV.
  rewrite !Z_to_bv_unsigned in EV. unfold bv_wrap in EV. change (bv_modulus 64) with (2 ^ 64) in EV.
  rewrite !Z.mod_small in EV by lia. exact EV.
- intros Hw. rewrite u64s_words. exact (proj2 (cells_at_of_words H mem VA ws HVA Hhi Hw)).
Qed.

(* ---- 3. ... and writable ones are rw_cells ---- *)
Lemma rw_cells_of_words : forall H mem p (ws : list Z), 0 <= p ->
  p + 8 * Z.of_nat (length ws) <= 2 ^ 64 ->
  words_at (aview tfibsegs H mem) p ws ->
  (forall a, p <= a < p + 8 * Z.of_nat (length ws) -> writable_at tfibsegs (cjstore H mem) a) ->
  Step.rw_cells tfibsegs (cjstore H mem) p (map (fun v => Cells.C8 (w64 v)) ws).
Proof.
intros H mem p ws Hp Hhi Hw HW. unfold Step.rw_cells. split.
- exact (cells_at_of_words H mem p ws Hp Hhi Hw).
- rewrite cells_size_words, Nat2Z.inj_mul. change (Z.of_nat 8) with 8.
  apply wr_at_of_writable; assumption.
Qed.

(* ---- 4. musl vsnprintf's FILE ---- *)
Lemma snf_file_bytes : forall bp cp,
  Cells.cells_bytes (@G_vfprintf_snf.snf_file N_img_asan bp cp)
  = Cells.cells_bytes (map (fun v => Cells.C8 (w64 v))
      (sn_file (@sym N_img_asan GX.G_printf_core_common.G_printf_iface.K_SN_WRITE) bp cp)).
Proof.
intros bp cp. unfold G_vfprintf_snf.snf_file, sn_file, w64.
cbn [map Cells.cells_bytes Cells.cbytes].
(* compared by value: a byte's proof field remembers the unwrapped Z it was built from, and the C4
   halves and the C8 words build the same byte from different Z *)
apply bytes_unsigned_inj. rewrite !map_app.
(* the three words that are not literals stay abstract; the rest is closed and computed *)
generalize (map (@bv_unsigned 8)
    (Mem.le8 (Z_to_bv 64 (@sym N_img_asan GX.G_printf_core_common.G_printf_iface.K_SN_WRITE))))
  (map (@bv_unsigned 8) (Mem.le8 (Z_to_bv 64 bp))) (map (@bv_unsigned 8) (Mem.le8 (Z_to_bv 64 cp))).
intros l1 l2 l3. vm_compute. reflexivity.
Qed.

Lemma rw_cells_snf_file : forall H mem fp snw bp cp,
  snw = @sym N_img_asan GX.G_printf_core_common.G_printf_iface.K_SN_WRITE ->
  0 <= fp -> fp + 232 <= 2 ^ 64 ->
  words_at (aview tfibsegs H mem) fp (sn_file snw bp cp) ->
  (forall a, fp <= a < fp + 232 -> writable_at tfibsegs (cjstore H mem) a) ->
  Step.rw_cells tfibsegs (cjstore H mem) fp (@G_vfprintf_snf.snf_file N_img_asan bp cp).
Proof.
intros H mem fp snw bp cp Esnw Hp Hhi Hw HW. subst snw.
pose proof (rw_cells_of_words H mem fp
  (sn_file (@sym N_img_asan GX.G_printf_core_common.G_printf_iface.K_SN_WRITE) bp cp) Hp) as R.
assert (L : 8 * Z.of_nat (length
  (sn_file (@sym N_img_asan GX.G_printf_core_common.G_printf_iface.K_SN_WRITE) bp cp)) = 232) by reflexivity.
rewrite L in R. destruct (R Hhi Hw HW) as [[_ HB] HR].
unfold Step.rw_cells, Cells.cells_at. split; [split|].
- unfold G_vfprintf_snf.snf_file. cbn [Cells.cells_wf Cells.cell_wf]. tauto.
- rewrite snf_file_bytes. exact HB.
- rewrite cells_size_words in HR. exact HR.
Qed.

(* ---- 5. the cookie {s, n} ---- *)
Lemma rw_cells_pair : forall H mem cp x y, 0 <= cp -> cp + 16 <= 2 ^ 64 ->
  words_at (aview tfibsegs H mem) cp [x; y] ->
  (forall a, cp <= a < cp + 16 -> writable_at tfibsegs (cjstore H mem) a) ->
  Step.rw_cells tfibsegs (cjstore H mem) cp [Cells.C8 (w64 x); Cells.C8 (w64 y)].
Proof.
intros H mem cp x y Hp Hhi Hw HW. exact (rw_cells_of_words H mem cp [x; y] Hp Hhi Hw HW).
Qed.

(* ---- 6. a writable block whose bytes are present, as one CB cell ---- *)
Lemma rw_cells_block : forall H mem d (n : nat), 0 <= d -> d + Z.of_nat n <= 2 ^ 64 ->
  (forall a, d <= a < d + Z.of_nat n -> writable_at tfibsegs (cjstore H mem) a) ->
  (forall a, d <= a < d + Z.of_nat n -> aview tfibsegs H mem a <> None) ->
  exists junk : list byte, length junk = n /\ Step.rw_cells tfibsegs (cjstore H mem) d [Cells.CB n junk].
Proof.
intros H mem d n Hd Hhi HW HV.
exists (map (fun i : nat => match Mem.mrd tfibsegs (cjstore H mem) (Mem.wa (d + Z.of_nat i)) with
                            | Some b => b | None => Z_to_bv 8 0 end) (seq 0 n)).
assert (L : length (map (fun i : nat => match Mem.mrd tfibsegs (cjstore H mem) (Mem.wa (d + Z.of_nat i)) with
                            | Some b => b | None => Z_to_bv 8 0 end) (seq 0 n)) = n)
  by (rewrite length_map, length_seq; reflexivity).
split; [exact L|].
unfold Step.rw_cells, Cells.cells_at.
cbn [Cells.cells_wf Cells.cell_wf Cells.cells_bytes Cells.cbytes Cells.cells_size Cells.csize].
rewrite app_nil_r, Nat.add_0_r.
split; [split; [split; [exact L | exact I]|]|].
- split; [exact Hd|]. split; [rewrite L; exact Hhi|].
  intros i Hi. rewrite L in Hi.
  rewrite nth_error_map, nth_error_nth' with (d := 0%nat) by (rewrite length_seq; exact Hi).
  rewrite seq_nth by exact Hi. cbn [option_map Nat.add].
  specialize (HV (d + Z.of_nat i) ltac:(lia)). rewrite aview_mrd in HV.
  destruct (Mem.mrd tfibsegs (cjstore H mem) (Mem.wa (d + Z.of_nat i))) as [b|];
    [reflexivity | exfalso; apply HV; reflexivity].
- apply wr_at_of_writable; assumption.
Qed.

(* ---- 7. ... holding musl vsnprintf's NUL at its first byte ---- *)
Lemma rw_cells_block_hd0 : forall H mem d (n : nat), 0 <= d -> d + Z.of_nat n <= 2 ^ 64 ->
  (forall a, d <= a < d + Z.of_nat n -> writable_at tfibsegs (cjstore H mem) a) ->
  (forall a, d <= a < d + Z.of_nat n -> aview tfibsegs H mem a <> None) ->
  aview tfibsegs H mem d = Some 0 -> (0 < n)%nat ->
  exists junk : list byte, length junk = n /\
    Step.rw_cells tfibsegs (cjstore H mem) d [Cells.CB n (Z_to_bv 8 0 :: skipn 1 junk)].
Proof.
intros H mem d n Hd Hhi HW HV H0 Hn.
destruct (rw_cells_block H mem d n Hd Hhi HW HV) as (junk & L & R).
exists junk. split; [exact L|].
destruct junk as [|b rest]; [cbn [length] in L; lia|].
assert (Eb : b = Z_to_bv 8 0).
{ destruct R as [[_ (_ & _ & HB)] _]. specialize (HB 0%nat ltac:(cbn; lia)).
  cbn [Cells.cells_bytes Cells.cbytes app nth_error] in HB.
  change (Z.of_nat 0) with 0 in HB. rewrite Z.add_0_r in HB.
  rewrite (mrd_of_view H mem d 0 H0) in HB. congruence. }
subst b. exact R.
Qed.

(* ---- 8. the stack-protector cells ---- *)
Lemma rw_cells_word : forall H mem p v, 0 <= p -> p + 8 <= 2 ^ 64 ->
  rdword (aview tfibsegs H mem) p = Some v ->
  (forall a, p <= a < p + 8 -> writable_at tfibsegs (cjstore H mem) a) ->
  Step.rw_cells tfibsegs (cjstore H mem) p [Cells.C8 (w64 v)].
Proof.
intros H mem p v Hp Hhi Hr HW.
apply (rw_cells_of_words H mem p [v]); [exact Hp | exact Hhi | | exact HW].
intros i Hi. cbn [length] in Hi. assert (i = 0%nat) by lia. subst i. cbn [nth].
change (Z.of_nat 0) with 0. rewrite Z.mul_0_r, Z.add_0_r. exact Hr.
Qed.

Lemma ssp_cells_of_view : forall H mem gc gv cval canary,
  gc = @sym N_img_asan 0x22e18 -> gv = @sym N_img_asan 0x34288 ->
  rdword (aview tfibsegs H mem) gc = Some gv -> rdword (aview tfibsegs H mem) gv = Some cval ->
  canary = w64 cval ->
  (forall a, gc <= a < gc + 8 -> writable_at tfibsegs (cjstore H mem) a) ->
  (forall a, gv <= a < gv + 8 -> writable_at tfibsegs (cjstore H mem) a) ->
  @G_pad.ssp_cells N_img_asan (cjstore H mem) canary.
Proof.
intros H mem gc gv cval canary Egc Egv Hgc Hgv -> Wgc Wgv.
assert (Rgc : gc = 0xa2c98) by (rewrite Egc; vm_compute; reflexivity).
assert (Rgv : gv = 0x5fdf30) by (rewrite Egv; vm_compute; reflexivity).
unfold G_pad.ssp_cells, G_pad.got_ssp, G_pad.ssp_guard. split.
- rewrite <- Egc, <- Egv. apply rw_cells_word; [lia | lia | exact Hgc | exact Wgc].
- rewrite <- Egv. apply rw_cells_word; [lia | lia | exact Hgv | exact Wgv].
Qed.

End c.
