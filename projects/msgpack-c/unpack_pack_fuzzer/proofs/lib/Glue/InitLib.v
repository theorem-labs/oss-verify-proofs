(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence FinInput.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import
  W64 W64Proofs Val IMap Mem Instr State Step Plan Notation.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import StackInit.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan SI.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module InitLib.

Lemma imap_of_bst : forall A (l : list (int * A)), IMap.bst (imap_of l).
Proof.
  intros A l. unfold imap_of.
  assert (G : forall acc, IMap.bst acc -> IMap.bst (fold_left (fun m kv => IMap.add (fst kv) (snd kv) m) l acc)).
  { induction l as [|kv l IH]; intros acc Hacc; cbn [fold_left]; [exact Hacc|]. apply IH. apply IMap.add_bst. exact Hacc. }
  apply G. exact I.
Qed.

Lemma find_in_elements : forall A k (v : A) m, IMap.bst m -> IMap.find k m = Some v -> In (k, v) (IMap.elements m).
Proof. intros A k v m Hb Hf. apply (proj2 (IMap.elements_spec k v m Hb)). exact Hf. Qed.

Lemma byte_of_le8 : forall (w : word) (i : nat), (i < 8)%nat -> nth i (word_le8 w) (Z_to_bv 8 0) = byte_of w (Z.of_nat i).
Proof. intros w i Hi. rewrite (word_le8_nth w i _ Hi). reflexivity. Qed.

Lemma ext_Z_false_id8 : forall u, 0 <= u < 2 ^ 64 -> ext_Z false 0 8 u = u.
Proof. intros u Hu. unfold ext_Z. change (2 ^ (8 * 0)) with 1. change (2 ^ (8 * 8)) with (2 ^ 64). rewrite Z.div_1_r. apply Z.mod_small. exact Hu. Qed.

Lemma bytes_val_le8 : forall z, 0 <= z < 2 ^ 64 ->
  bytes_val false 8 (blob_bytes (Z_to_le_bytes 8 z) 0 8) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold bytes_val, blob_bytes. change (Z.to_nat 8) with 8%nat. change (Z.to_nat 0) with 0%nat.
  rewrite skipn_O. rewrite firstn_all2 by (rewrite (length_Z_to_le_bytes 8%nat z); lia).
  rewrite bytes_le_to_Z_of_le_bytes by lia.
  change (8 * Z.of_nat 8) with 64. rewrite Z.mod_small by lia.
  rewrite ext_Z_false_id8; [reflexivity|]. lia.
Qed.

Definition segs_below (sgs : list Segment) (B : Z) : bool :=
  forallb (fun s => Z.leb (Z.of_N (seg_base s) + Z.of_N (seg_size s)) B) sgs.

Lemma find_segment_bound : forall (sgs : list Segment) a n seg B,
  forallb (fun s => Z.leb (Z.of_N (seg_base s) + Z.of_N (seg_size s)) B) sgs = true ->
  find_segment sgs a n = Some seg -> a + n <= B.
Proof.
  induction sgs as [|sg sgs IH]; intros a n seg B Hf H; cbn [find_segment] in H; [discriminate|].
  cbn [forallb] in Hf. apply andb_prop in Hf as [H1 H2]. apply Z.leb_le in H1.
  destruct (Z.leb (Z.of_N (seg_base sg)) a && Z.leb (a + n) (Z.of_N (seg_base sg) + Z.of_N (seg_size sg)))%bool eqn:Hc.
  - apply andb_prop in Hc as [_ Hc]. apply Z.leb_le in Hc. lia.
  - exact (IH a n seg B H2 H).
Qed.

Lemma find_segment_none : forall (sgs : list Segment) a n B,
  forallb (fun s => Z.leb (Z.of_N (seg_base s) + Z.of_N (seg_size s)) B) sgs = true ->
  B <= a -> 0 < n -> find_segment sgs a n = None.
Proof.
  induction sgs as [|sg sgs IH]; intros a n B Hf Ha Hn; cbn [find_segment]; [reflexivity|].
  cbn [forallb] in Hf. apply andb_prop in Hf as [H1 H2]. apply Z.leb_le in H1.
  replace (Z.leb (a + n) (Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) with false by (symmetry; apply Z.leb_gt; lia).
  rewrite andb_false_r. exact (IH a n B H2 Ha Hn).
Qed.

Section Image.
Variables (SEGS : list Segment) (PC : N) (PH : PhdrInfo) (SEGTOP : Z).
Hypothesis segs_below_top : segs_below SEGS SEGTOP = true.
Hypothesis segtop_low : SEGTOP <= 0x7fff7f800000.
Hypothesis HphA : Z.of_N (ph_addr PH) = 65600.
Hypothesis HphE : Z.of_N (ph_ent PH) = 56.
Hypothesis HphN : Z.of_N (ph_num PH) = 10.

Lemma memory_read_find : forall a bs, 0 <= a < 2 ^ 64 -> memory_read SEGS (Z_to_bv 64 a) 1 = Some bs -> a + 1 <= SEGTOP.
Proof.
  intros a bs Ha H. unfold memory_read in H. rewrite Z_to_bv64_unsigned in H by exact Ha.
  destruct (find_segment SEGS a (Z.of_N 1)) as [seg|] eqn:Hf; [|discriminate].
  exact (find_segment_bound SEGS a 1 seg SEGTOP segs_below_top Hf).
Qed.

Definition PB_STD (b : int -> list byte) : Prop :=
  exists (a0 : list byte) (eptrs : list word),
    b 1%uint63 = a0 ++ [Z_to_bv 8 0] /\ ~ In (Z_to_bv 8 0) a0 /\ Z.of_nat (length a0) <= 131071 /\
    b 2%uint63 = flat_map word_le8 eptrs ++ word_le8 (Z_to_bv 64 0) /\ Z.of_nat (length eptrs) <= 256 /\
    Forall (fun p => 0 < bv_unsigned p) eptrs /\
    b 8%uint63 = Z_to_le_bytes 8 (8 * Z.of_nat (length eptrs) + 8) /\
    b 9%uint63 = Z_to_le_bytes 8 (Z.of_nat (length a0) + 1) /\
    length (b 6%uint63) = 16%nat.

Definition PB_ARG1 (b : int -> list byte) : Prop :=
  exists (a1 : list byte),
    b 3%uint63 = a1 ++ [Z_to_bv 8 0] /\ ~ In (Z_to_bv 8 0) a1 /\ Z.of_nat (length a1) <= 131071 /\
    b 10%uint63 = Z_to_le_bytes 8 (Z.of_nat (length a1) + 1).

Section Entry.
Variables (sp : word) (argv envp : list (list byte)) (uid hwcap : word) (draw : EntryDraw).
Variable xb : int -> list byte.
Hypothesis Hva : valid_argv argv.
Hypothesis Hve : valid_envp envp.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hfit : entry_stack_fits sp argv envp.
Hypothesis Hhw : valid_hwcap hwcap.

Local Notation SP := (SI.SP sp).
Let a0 : list byte := hd [] argv.
Let a1 : list byte := hd [] (tl argv).
Let ms0 : machine_state := init_machine_state SEGS PC PH sp draw argv envp uid hwcap.

Definition ev0 (k : int) : word :=
  match to_Z k with
  | 1 => sp
  | 2 => Z_to_bv 64 (SP + envp_off argv)
  | 3 => Z_to_bv 64 (SP + auxv_off argv envp)
  | 4 => len_word argv
  | 5 => str_base sp argv envp
  | 6 => ARND sp argv envp
  | 7 => hwcap
  | 8 => uid
  | 10 => Z_to_bv 64 (SP + Z.of_nat (sstruct argv envp) + Z.of_nat (length a0) + 1)
  | 12 => str_base sp argv envp
  | _ => Z_to_bv 64 0
  end.

Definition eb0 (j : int) : list byte :=
  match to_Z j with
  | 1 => a0 ++ [Z_to_bv 8 0]
  | 2 => envp_img sp argv envp
  | 3 => a1 ++ [Z_to_bv 8 0]
  | 6 => at_random_bytes (ed_random draw)
  | 8 => Z_to_le_bytes 8 (8 * envcZ envp + 8)
  | 9 => Z_to_le_bytes 8 (Z.of_nat (length a0) + 1)
  | 10 => Z_to_le_bytes 8 (Z.of_nat (length a1) + 1)
  | 12 => strarea argv envp
  | 15 => Z_to_le_bytes 8 (Z.of_nat (length (strarea argv envp)))
  | _ => xb j
  end.

Definition eg0 (k : int) (o : Z) : byte :=
  match to_Z k with
  | 6 => nth (Z.to_nat o) (at_random_bytes (ed_random draw)) (Z_to_bv 8 0)
  | _ => Z_to_bv 8 0
  end.

Definition E0 : env := Env ev0 eb0 eg0.

Let Hlo := SP_lo sp Hsp.
Let Htop := BSB_top PH sp argv envp uid hwcap draw Hfit.
Let Hargc := argc_range argv Hva.
Let Henvc := envc_range envp Hve.

Lemma argv_eq : argv = a0 :: tl argv.
Proof.
  destruct (argv_cons argv Hva) as (x & rest & Hx). unfold a0. rewrite Hx. reflexivity.
Qed.

Lemma a0_len : Z.of_nat (length a0) <= 131071.
Proof.
  pose proof Hva as (_ & _ & Hl & _). rewrite argv_eq in Hl. inversion Hl. assumption.
Qed.

Lemma a0_nonul : ~ In (Z_to_bv 8 0) a0.
Proof.
  pose proof Hva as (_ & _ & _ & Hn & _). rewrite argv_eq in Hn. inversion Hn. assumption.
Qed.

Lemma len_BSB : Z.of_nat (length (BSB PH sp argv envp uid hwcap draw)) =
  Z.of_nat (sstruct argv envp) + Z.of_nat (total_nat argv) + Z.of_nat (total_nat envp) + Z.of_nat (pad argv envp) + 16.
Proof. rewrite length_BSB. unfold raw_len. lia. Qed.

Lemma sstruct_val : Z.of_nat (sstruct argv envp) = 184 + 8 * argcZ argv + 8 * envcZ envp.
Proof. unfold sstruct, argcZ, envcZ, nargc, nenvc. lia. Qed.

Lemma total_ge_a0 : Z.of_nat (length a0) + 1 <= Z.of_nat (total_nat argv).
Proof. pose proof argv_eq as E. replace (total_nat argv) with (total_nat (a0 :: tl argv)) by (rewrite <- E; reflexivity). cbn [total_nat]. lia. Qed.

Lemma ev0_0 : ev E0 0%uint63 = Z_to_bv 64 0. Proof. reflexivity. Qed.
Lemma ev0_1 : ev E0 1%uint63 = sp. Proof. reflexivity. Qed.
Lemma ev0_2 : bv_unsigned (ev E0 2%uint63) = SP + envp_off argv.
Proof. change (ev E0 2%uint63) with (Z_to_bv 64 (SP + envp_off argv)). apply Z_to_bv64_unsigned. unfold envp_off. pose proof len_BSB. pose proof sstruct_val. lia. Qed.
Lemma ev0_3 : bv_unsigned (ev E0 3%uint63) = SP + auxv_off argv envp.
Proof. change (ev E0 3%uint63) with (Z_to_bv 64 (SP + auxv_off argv envp)). apply Z_to_bv64_unsigned. unfold auxv_off. pose proof len_BSB. pose proof sstruct_val. lia. Qed.
Lemma ev0_4 : ev E0 4%uint63 = len_word argv. Proof. reflexivity. Qed.
Lemma ev0_5 : bv_unsigned (ev E0 5%uint63) = SP + Z.of_nat (sstruct argv envp).
Proof. change (ev E0 5%uint63) with (str_base sp argv envp). apply (str_base_val PH sp argv envp uid hwcap draw Hfit). Qed.
Lemma ev0_6 : bv_unsigned (ev E0 6%uint63) = SP + Z.of_nat (raw_len argv envp + pad argv envp).
Proof. change (ev E0 6%uint63) with (ARND sp argv envp). apply (ARND_val PH sp argv envp uid hwcap draw Hfit). Qed.
Lemma ev0_7 : ev E0 7%uint63 = hwcap. Proof. reflexivity. Qed.
Lemma ev0_8 : ev E0 8%uint63 = uid. Proof. reflexivity. Qed.
Lemma ev0_12 : bv_unsigned (ev E0 12%uint63) = SP + Z.of_nat (sstruct argv envp).
Proof. change (ev E0 12%uint63) with (str_base sp argv envp). apply (str_base_val PH sp argv envp uid hwcap draw Hfit). Qed.
Lemma strarea_len : Z.of_nat (length (strarea argv envp)) = Z.of_nat (total_nat argv) + Z.of_nat (total_nat envp) + Z.of_nat (pad argv envp).
Proof. rewrite length_strarea. lia. Qed.

Lemma den_VP0 : forall k, den E0 (VP k (wp 0%uint63)) = ev E0 k.
Proof. intros k. cbn [den]. apply bv_add_0_r. reflexivity. Qed.

Lemma den_SIZE8 : den E0 (VBlob false 8%uint63 (VL (wp 0%uint63)) 8%uint63) = Z_to_bv 64 (8 * envcZ envp + 8).
Proof.
  cbn [den eb E0 eb0]. change (bv_unsigned (wbv (wp 0%uint63))) with 0. change (to_Z 8%uint63) with 8.
  apply bytes_val_le8. lia.
Qed.
Lemma den_SIZE9 : den E0 (VBlob false 9%uint63 (VL (wp 0%uint63)) 8%uint63) = Z_to_bv 64 (Z.of_nat (length a0) + 1).
Proof.
  cbn [den eb E0 eb0]. change (bv_unsigned (wbv (wp 0%uint63))) with 0. change (to_Z 8%uint63) with 8.
  apply bytes_val_le8. pose proof a0_len. lia.
Qed.
Lemma den_SIZE15 : den E0 (VBlob false 15%uint63 (VL (wp 0%uint63)) 8%uint63) = Z_to_bv 64 (Z.of_nat (length (strarea argv envp))).
Proof.
  cbn [den eb E0 eb0]. change (bv_unsigned (wbv (wp 0%uint63))) with 0. change (to_Z 8%uint63) with 8.
  apply bytes_val_le8. pose proof len_BSB. pose proof strarea_len. lia.
Qed.

Definition Z0 : sv := VL (wp 0%uint63).
Definition R0T : region := Region 0%uint63 (VL (wp 0%uint63)) false BGImage (imap_of []).

Definition R1NT : region := Region 9223372036846387200%uint63 (VL (wp 16%uint63)) true BGZero
  (imap_of [(0%uint63, Gran false [Cell 0%uint63 8%uint63 (VP 4%uint63 (wp 0%uint63))]);
            (1%uint63, Gran false [Cell 0%uint63 8%uint63 (VP 5%uint63 (wp 0%uint63))])]).

Definition R1FT : region := Region 9223372036846387200%uint63 (VL (wp 32%uint63)) true BGZero
  (imap_of [(0%uint63, Gran false [Cell 0%uint63 8%uint63 (VL (wp 2%uint63))]);
            (1%uint63, Gran false [Cell 0%uint63 8%uint63 (VP 5%uint63 (wp 0%uint63))]);
            (2%uint63, Gran false [Cell 0%uint63 8%uint63 (VP 10%uint63 (wp 0%uint63))]);
            (3%uint63, Gran false [Cell 0%uint63 8%uint63 (VL (wp 0%uint63))])]).
Definition R2T : region := Region 0%uint63 (VBlob false 8%uint63 (VL (wp 0%uint63)) 8%uint63) false (BGBlob 2%uint63 0%uint63) (imap_of []).
Definition auxsv : list sv :=
  [VL (wp 3%uint63); VL (wp 65600%uint63); VL (wp 4%uint63); VL (wp 56%uint63); VL (wp 5%uint63); VL (wp 10%uint63);
   VL (wp 16%uint63); VP 7%uint63 (wp 0%uint63); VL (wp 6%uint63); VL (wp 4096%uint63); VL (wp 11%uint63); VP 8%uint63 (wp 0%uint63);
   VL (wp 12%uint63); VP 8%uint63 (wp 0%uint63); VL (wp 23%uint63); VL (wp 0%uint63); VL (wp 25%uint63); VP 6%uint63 (wp 0%uint63);
   VL (wp 0%uint63); VL (wp 0%uint63)].
Definition R3T : region := Region 0%uint63 (VL (wp 160%uint63)) false BGNone
  (imap_of [(0%uint63, Gran false [Cell 0%uint63 8%uint63 (VL (wp 3%uint63))]); (1%uint63, Gran false [Cell 0%uint63 8%uint63 (VL (wp 65600%uint63))]);
            (2%uint63, Gran false [Cell 0%uint63 8%uint63 (VL (wp 4%uint63))]); (3%uint63, Gran false [Cell 0%uint63 8%uint63 (VL (wp 56%uint63))]);
            (4%uint63, Gran false [Cell 0%uint63 8%uint63 (VL (wp 5%uint63))]); (5%uint63, Gran false [Cell 0%uint63 8%uint63 (VL (wp 10%uint63))]);
            (6%uint63, Gran false [Cell 0%uint63 8%uint63 (VL (wp 16%uint63))]); (7%uint63, Gran false [Cell 0%uint63 8%uint63 (VP 7%uint63 (wp 0%uint63))]);
            (8%uint63, Gran false [Cell 0%uint63 8%uint63 (VL (wp 6%uint63))]); (9%uint63, Gran false [Cell 0%uint63 8%uint63 (VL (wp 4096%uint63))]);
            (10%uint63, Gran false [Cell 0%uint63 8%uint63 (VL (wp 11%uint63))]); (11%uint63, Gran false [Cell 0%uint63 8%uint63 (VP 8%uint63 (wp 0%uint63))]);
            (12%uint63, Gran false [Cell 0%uint63 8%uint63 (VL (wp 12%uint63))]); (13%uint63, Gran false [Cell 0%uint63 8%uint63 (VP 8%uint63 (wp 0%uint63))]);
            (14%uint63, Gran false [Cell 0%uint63 8%uint63 (VL (wp 23%uint63))]); (15%uint63, Gran false [Cell 0%uint63 8%uint63 (VL (wp 0%uint63))]);
            (16%uint63, Gran false [Cell 0%uint63 8%uint63 (VL (wp 25%uint63))]); (17%uint63, Gran false [Cell 0%uint63 8%uint63 (VP 6%uint63 (wp 0%uint63))]);
            (18%uint63, Gran false [Cell 0%uint63 8%uint63 (VL (wp 0%uint63))]); (19%uint63, Gran false [Cell 0%uint63 8%uint63 (VL (wp 0%uint63))])]).
Definition R5T : region := Region 0%uint63 (VBlob false 9%uint63 (VL (wp 0%uint63)) 8%uint63) false (BGBlob 1%uint63 0%uint63) (imap_of []).
Definition R6T : region := Region 0%uint63 (VL (wp 16%uint63)) false (BGBlob 6%uint63 0%uint63) (imap_of []).
Definition R10T : region := Region 0%uint63 (VBlob false 10%uint63 (VL (wp 0%uint63)) 8%uint63) false (BGBlob 3%uint63 0%uint63) (imap_of []).

Definition R12T : region := Region 0%uint63 (VBlob false 15%uint63 (VL (wp 0%uint63)) 8%uint63) false (BGBlob 12%uint63 0%uint63) IMap.empty.

Lemma hiZ_R1 : hiZ E0 R1NT = 16. Proof. reflexivity. Qed.
Lemma loZ_R1 : loZ R1NT = - 8388608. Proof. reflexivity. Qed.
Lemma hiZ_R2 : hiZ E0 R2T = 8 * envcZ envp + 8.
Proof. unfold hiZ. change (rg_hi R2T) with (VBlob false 8%uint63 (VL (wp 0%uint63)) 8%uint63). rewrite den_SIZE8. apply Z_to_bv64_unsigned. lia. Qed.
Lemma hiZ_R3 : hiZ E0 R3T = 160. Proof. reflexivity. Qed.
Lemma hiZ_R12 : hiZ E0 R12T = Z.of_nat (length (strarea argv envp)).
Proof. unfold hiZ. cbn [rg_hi R12T]. rewrite den_SIZE15. apply Z_to_bv64_unsigned. pose proof len_BSB. pose proof strarea_len. lia. Qed.
Lemma hiZ_R5 : hiZ E0 R5T = Z.of_nat (length a0) + 1.
Proof. unfold hiZ. change (rg_hi R5T) with (VBlob false 9%uint63 (VL (wp 0%uint63)) 8%uint63). rewrite den_SIZE9. apply Z_to_bv64_unsigned. pose proof a0_len. lia. Qed.
Lemma loZ_0 : forall r, rg_lo r = 0%uint63 -> loZ r = 0. Proof. intros r H. unfold loZ. rewrite H. reflexivity. Qed.

Local Notation mem0 := (SI.mem0 SEGS PC PH sp argv envp uid hwcap draw).
Lemma ms0_mem : ms_mem ms0 = mem0. Proof. reflexivity. Qed.

Lemma rb_some : forall a b, mem0 (Z_to_bv 64 a) = Some b -> rb SEGS mem0 a = Some b.
Proof. intros a b H. unfold rb. rewrite H. reflexivity. Qed.
Lemma wb_some : forall a b, mem0 (Z_to_bv 64 a) = Some b -> wb SEGS mem0 a = true.
Proof. intros a b H. unfold wb, wview. rewrite H. reflexivity. Qed.

Lemma stack_byte : forall a, SP - stack_max_size <= a < SP + Z.of_nat (length (BSB PH sp argv envp uid hwcap draw)) ->
  exists b, mem0 (Z_to_bv 64 a) = Some b.
Proof.
  intros a Ha. destruct (Z.lt_ge_cases a SP) as [Hl|Hge].
  - exists (Z_to_bv 8 0). apply (mem0_below SEGS PC PH sp argv envp uid hwcap draw Hsp). lia.
  - destruct (nth_error (BSB PH sp argv envp uid hwcap draw) (Z.to_nat (a - SP))) as [b|] eqn:Hn.
    + exists b. replace a with (SP + Z.of_nat (Z.to_nat (a - SP))) by lia. apply (mem0_block SEGS PC PH sp argv envp uid hwcap draw Hsp Hfit). exact Hn.
    + exfalso. apply nth_error_None in Hn. lia.
Qed.

Lemma stack_valid : forall a, SP - stack_max_size <= a < SP + Z.of_nat (length (BSB PH sp argv envp uid hwcap draw)) ->
  rb SEGS mem0 a <> None /\ wb SEGS mem0 a = true /\ find_segment SEGS a 1 = None.
Proof.
  intros a Ha. destruct (stack_byte a Ha) as [b Hb]. split; [|split].
  - rewrite (rb_some a b Hb). discriminate.
  - exact (wb_some a b Hb).
  - apply (find_segment_none SEGS a 1 SEGTOP segs_below_top); [|lia]. pose proof segtop_low. unfold stack_max_size in *. lia.
Qed.

Lemma slot_ok_word : forall base v w,
  word_at SEGS PC PH sp argv envp uid hwcap draw base w -> den E0 v = w ->
  slot_ok SEGS E0 mem0 base [Cell 0%uint63 8%uint63 v].
Proof.
  intros base v w Hw Hv. split; [exact (conj I I)|].
  constructor; [|constructor]. unfold cell_ok. cbn [c_idx c_w c_v].
  change (to_Z 0%uint63) with 0. change (to_Z 8%uint63) with 8.
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. replace (base + 0 + i) with (base + Z.of_nat (Z.to_nat i)) by lia.
  apply rb_some. rewrite (Hw (Z.to_nat i)) by lia. rewrite byte_of_le8 by lia. rewrite Z2Nat.id by lia. rewrite Hv. reflexivity.
Qed.

Definition R1L := Eval vm_compute in IMap.elements (rg_cells R1NT).
Lemma R1_elements : IMap.elements (rg_cells R1NT) = R1L. Proof. vm_compute. reflexivity. Qed.
Definition R3L := Eval vm_compute in IMap.elements (rg_cells R3T).
Lemma R3_elements : IMap.elements (rg_cells R3T) = R3L. Proof. vm_compute. reflexivity. Qed.

Lemma R3_find : forall g gr, IMap.find g (rg_cells R3T) = Some gr ->
  exists j : nat, (j < 20)%nat /\ keyZ g = Z.of_nat j /\ gr = Gran false [Cell 0%uint63 8%uint63 (nth j auxsv (VL (wp 0%uint63)))].
Proof.
  intros g gr H. apply (find_in_elements _ g gr (rg_cells R3T) (imap_of_bst _ _)) in H. rewrite R3_elements in H. unfold R3L in H.
  Ltac tac j := match goal with
    | H : In _ (_ :: _) |- _ => destruct H as [H|H]; [exists j; injection H as <- <-; split; [lia|]; split; reflexivity | tac (S j)]
    | H : In _ [] |- _ => destruct H
    end.
  tac 0%nat.
Qed.

Lemma R1_find : forall g gr, IMap.find g (rg_cells R1NT) = Some gr ->
  (g = 0%uint63 /\ gr = Gran false [Cell 0%uint63 8%uint63 (VP 4%uint63 (wp 0%uint63))]) \/
  (g = 1%uint63 /\ gr = Gran false [Cell 0%uint63 8%uint63 (VP 5%uint63 (wp 0%uint63))]).
Proof.
  intros g gr H. apply (find_in_elements _ g gr (rg_cells R1NT) (imap_of_bst _ _)) in H. rewrite R1_elements in H. unfold R1L in H.
  destruct H as [H|[H|[]]]; [left|right]; injection H as <- <-; split; reflexivity.
Qed.

Lemma auxsv_den : forall j, (j < 20)%nat ->
  den E0 (nth j auxsv (VL (wp 0%uint63))) = nth j (auxws PH sp argv envp uid hwcap) (Z_to_bv 64 0).
Proof.
  intros j Hj. unfold auxws. rewrite HphA, HphE, HphN.
  do 20 (destruct j as [|j]; [first [reflexivity | (cbn [nth auxsv]; rewrite den_VP0; reflexivity)] |]). lia.
Qed.

Lemma covered_not_uncovered : forall r o g v,
  keyZ g = o / 8 -> 0 <= o mod 8 < 8 ->
  IMap.find g (rg_cells r) = Some (Gran false [Cell 0%uint63 8%uint63 v]) -> ~ uncovered r o.
Proof.
  intros r o g v Hg Ho Hf Hu. destruct (Hu g _ Hg Hf) as [_ Hc].
  inversion Hc as [|c l Hn _]; subst. apply Hn. unfold covers. cbn [c_idx c_w].
  change (to_Z 0%uint63) with 0. change (to_Z 8%uint63) with 8. lia.
Qed.

Lemma R0_ok : region_ok SEGS [] E0 mem0 0%uint63 R0T.
Proof.
  split.
  - exact I.
  - intros H; discriminate H.
  - intros H; discriminate H.
  - intros g gr Hg. cbn in Hg. discriminate.
  - intros g gr c i Hg. cbn in Hg. discriminate.
  - intros o _ Ho _. destruct (Ho eq_refl) as (Hr & [bs Hbs] & _).
    cbn [bg_byte rg_bg R0T]. unfold img_byte.
    pose proof (memory_read_find o bs ltac:(unfold two63 in Hr; lia) Hbs) as Hb.
    destruct (rom_of SEGS (Z_to_bv 64 o)) as [b|] eqn:Hrom; [|exact I].
    unfold rb. rewrite ev0_0. change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite Z.add_0_l.
    rewrite (mem0_none_low SEGS PC PH sp argv envp uid hwcap draw Hsp o); [exact Hrom|].
    unfold stack_max_size in *. pose proof Hlo. pose proof segtop_low. unfold SP in *. lia.
Qed.

Lemma R1_ok : region_ok SEGS [] E0 mem0 1%uint63 R1NT.
Proof.
  pose proof len_BSB as HL. pose proof sstruct_val as HS.
  split.
  - apply imap_of_bst.
  - intros _. rewrite ev0_1, loZ_R1, hiZ_R1. fold SP. unfold two64. lia.
  - intros _ a. rewrite ev0_1, loZ_R1, hiZ_R1. fold SP. intros Ha.
    destruct (stack_valid a ltac:(unfold stack_max_size; lia)) as (H1 & H2 & H3). cbn [rg_w R1NT]. auto.
  - intros g gr Hg. rewrite ev0_1. fold SP.
    destruct (R1_find g gr Hg) as [[-> ->]|[-> ->]]; cbn [g_cells].
    + change (keyZ 0%uint63) with 0. replace (SP + 8 * 0) with SP by lia.
      apply (slot_ok_word SP _ (len_word argv)); [apply (argc_word SEGS PC PH sp argv envp uid hwcap draw Hsp Hfit) | rewrite den_VP0; apply ev0_4].
    + change (keyZ 1%uint63) with 1. replace (SP + 8 * 1) with (SP + 8 + 8 * Z.of_nat 0) by lia.
      apply (slot_ok_word _ _ (nth 0 (argv_ptrs sp argv envp) (Z_to_bv 64 0))).
      * apply (argv_ptr_word SEGS PC PH sp argv envp uid hwcap draw Hsp Hfit). pose proof Hargc. unfold argcZ in *. lia.
      * rewrite den_VP0. rewrite (argv_ptr0 sp argv envp a0 (tl argv) argv_eq). reflexivity.
  - intros g gr c i Hg Hc Hi. split; [|intros H; discriminate H]. intros _. rewrite loZ_R1, hiZ_R1.
    destruct (R1_find g gr Hg) as [[-> ->]|[-> ->]]; cbn [g_cells] in Hc; destruct Hc as [<-|[]];
      cbn [c_idx c_w] in *; change (to_Z 0%uint63) with 0 in *; change (to_Z 8%uint63) with 8 in *;
      [change (keyZ 0%uint63) with 0 | change (keyZ 1%uint63) with 1]; lia.
  - intros o Ho _ Hu. specialize (Ho eq_refl). rewrite loZ_R1, hiZ_R1 in Ho. cbn [bg_byte rg_bg R1NT]. rewrite ev0_1. fold SP.
    destruct (Z.lt_ge_cases o 0) as [Hneg|Hpos].
    + apply rb_some. apply (mem0_below SEGS PC PH sp argv envp uid hwcap draw Hsp). unfold stack_max_size. lia.
    + exfalso. destruct (Z.lt_ge_cases o 8) as [H8|H8].
      * apply (covered_not_uncovered R1NT o 0%uint63 (VP 4%uint63 (wp 0%uint63))); [change (keyZ 0%uint63) with 0; rewrite Z.div_small; lia | apply Z.mod_pos_bound; lia | reflexivity | exact Hu].
      * apply (covered_not_uncovered R1NT o 1%uint63 (VP 5%uint63 (wp 0%uint63))); [change (keyZ 1%uint63) with 1; apply (Z.div_unique_pos o 8 1 (o - 8)); lia | apply Z.mod_pos_bound; lia | reflexivity | exact Hu].
Qed.

Lemma R2_ok : region_ok SEGS [] E0 mem0 2%uint63 R2T.
Proof.
  pose proof len_BSB as HL. pose proof sstruct_val as HS.
  split.
  - exact I.
  - intros _. rewrite ev0_2, (loZ_0 R2T eq_refl), hiZ_R2. unfold envp_off, two64. lia.
  - intros _ a. rewrite ev0_2, (loZ_0 R2T eq_refl), hiZ_R2. unfold envp_off. intros Ha.
    destruct (stack_valid a ltac:(unfold stack_max_size; lia)) as (H1 & H2 & H3). cbn [rg_w R2T]. split; [exact H1|]. split; [intros H; discriminate H| exact H3].
  - intros g gr Hg. cbn in Hg. discriminate.
  - intros g gr c i Hg. cbn in Hg. discriminate.
  - intros o Ho _ _. specialize (Ho eq_refl). rewrite (loZ_0 R2T eq_refl), hiZ_R2 in Ho.
    cbn [bg_byte rg_bg R2T eb E0 eb0]. change (to_Z 0%uint63) with 0. rewrite Z.sub_0_r. rewrite ev0_2.
    pose proof (length_envp_img sp argv envp) as Hlen.
    replace (SP + envp_off argv + o) with (SP + envp_off argv + Z.of_nat (Z.to_nat o)) by lia.
    apply rb_some. rewrite (envp_img_byte SEGS PC PH sp argv envp uid hwcap draw Hsp Hfit (Z.to_nat o)) by lia. reflexivity.
Qed.

Lemma R3_ok : region_ok SEGS [] E0 mem0 3%uint63 R3T.
Proof.
  pose proof len_BSB as HL. pose proof sstruct_val as HS.
  split.
  - apply imap_of_bst.
  - intros _. rewrite ev0_3, (loZ_0 R3T eq_refl), hiZ_R3. unfold auxv_off, two64. lia.
  - intros _ a. rewrite ev0_3, (loZ_0 R3T eq_refl), hiZ_R3. unfold auxv_off. intros Ha.
    destruct (stack_valid a ltac:(unfold stack_max_size; lia)) as (H1 & H2 & H3). cbn [rg_w R3T]. split; [exact H1|]. split; [intros H; discriminate H| exact H3].
  - intros g gr Hg. rewrite ev0_3. destruct (R3_find g gr Hg) as (j & Hj & Hk & ->). cbn [g_cells]. rewrite Hk.
    apply (slot_ok_word _ _ (nth j (auxws PH sp argv envp uid hwcap) (Z_to_bv 64 0))).
    + apply (auxv_word SEGS PC PH sp argv envp uid hwcap draw Hsp Hfit). exact Hj.
    + apply auxsv_den. exact Hj.
  - intros g gr c i Hg Hc Hi. split; [|intros H; discriminate H]. intros _. rewrite (loZ_0 R3T eq_refl), hiZ_R3.
    destruct (R3_find g gr Hg) as (j & Hj & Hk & ->). cbn [g_cells] in Hc. destruct Hc as [<-|[]].
    cbn [c_idx c_w] in *. change (to_Z 0%uint63) with 0 in *. change (to_Z 8%uint63) with 8 in *. rewrite Hk. lia.
  - intros o _ _ _. cbn [bg_byte rg_bg R3T]. exact I.
Qed.

Lemma R5_ok : region_ok SEGS [] E0 mem0 5%uint63 R5T.
Proof.
  pose proof len_BSB as HL. pose proof sstruct_val as HS. pose proof total_ge_a0 as HA.
  split.
  - exact I.
  - intros _. rewrite ev0_5, (loZ_0 R5T eq_refl), hiZ_R5. unfold two64. lia.
  - intros _ a. rewrite ev0_5, (loZ_0 R5T eq_refl), hiZ_R5. intros Ha.
    destruct (stack_valid a ltac:(unfold stack_max_size; lia)) as (H1 & H2 & H3). cbn [rg_w R5T]. split; [exact H1|]. split; [intros H; discriminate H| exact H3].
  - intros g gr Hg. cbn in Hg. discriminate.
  - intros g gr c i Hg. cbn in Hg. discriminate.
  - intros o Ho _ _. specialize (Ho eq_refl). rewrite (loZ_0 R5T eq_refl), hiZ_R5 in Ho.
    cbn [bg_byte rg_bg R5T eb E0 eb0]. change (to_Z 0%uint63) with 0. rewrite Z.sub_0_r. rewrite ev0_5.
    replace (SP + Z.of_nat (sstruct argv envp) + o) with (SP + Z.of_nat (sstruct argv envp) + Z.of_nat (Z.to_nat o)) by lia.
    apply rb_some. rewrite (argv0_byte SEGS PC PH sp argv envp uid hwcap draw Hsp Hfit a0 (tl argv) (Z.to_nat o) argv_eq) by lia.
    reflexivity.
Qed.

Lemma R12_ok : region_ok SEGS [] E0 mem0 12%uint63 R12T.
Proof.
  pose proof len_BSB as HL. pose proof sstruct_val as HS. pose proof strarea_len as HA.
  split.
  - exact I.
  - intros _. rewrite ev0_12, (loZ_0 R12T eq_refl), hiZ_R12. unfold two64. lia.
  - intros _ a. rewrite ev0_12, (loZ_0 R12T eq_refl), hiZ_R12. intros Ha.
    destruct (stack_valid a ltac:(unfold stack_max_size; lia)) as (H1 & H2 & H3). cbn [rg_w R12T]. split; [exact H1|]. split; [intros H; discriminate H| exact H3].
  - intros g gr Hg. cbn in Hg. discriminate.
  - intros g gr c i Hg. cbn in Hg. discriminate.
  - intros o Ho _ _. specialize (Ho eq_refl). rewrite (loZ_0 R12T eq_refl), hiZ_R12 in Ho.
    cbn [bg_byte rg_bg R12T eb E0 eb0]. change (to_Z 0%uint63) with 0. rewrite Z.sub_0_r. rewrite ev0_12.
    replace (SP + Z.of_nat (sstruct argv envp) + o) with (SP + Z.of_nat (sstruct argv envp) + Z.of_nat (Z.to_nat o)) by lia.
    apply rb_some. rewrite (strarea_byte SEGS PC PH sp argv envp uid hwcap draw Hsp Hfit (Z.to_nat o)) by lia.
    reflexivity.
Qed.

Lemma w16 : bv_unsigned (wbv (wp 16%uint63)) = 16. Proof. reflexivity. Qed.
Lemma w0 : bv_unsigned (wbv (wp 0%uint63)) = 0. Proof. reflexivity. Qed.
Lemma sh3 : bv_unsigned (bv_and (wbv (wp 3%uint63)) (Z_to_bv 64 63)) = 3. Proof. reflexivity. Qed.

Lemma ext_Z_sx32_small : forall z, 0 <= z < 2 ^ 31 -> ext_Z true 0 4 z = z.
Proof.
  intros z Hz. unfold ext_Z. change (2 ^ (8 * 0)) with 1. change (2 ^ (8 * 4)) with (2 ^ 32). change (2 ^ (8 * 4 - 1)) with (2 ^ 31).
  rewrite Z.div_1_r, (Z.mod_small z) by lia.
  replace (2 ^ 31 <=? z) with false by (symmetry; apply Z.leb_gt; lia). unfold two64. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma fact_envp : den E0 (VP 2%uint63 (wp 0%uint63)) =
  den E0 (VAlu ALU_ADD (VP 1%uint63 (wp 16%uint63)) (VAlu ALU_SLL (VExt true 0%uint63 4%uint63 (VP 4%uint63 (wp 0%uint63))) (VL (wp 3%uint63)))).
Proof.
  pose proof len_BSB as HL. pose proof sstruct_val as HS.
  rewrite den_VP0. cbn [den alu64 alu]. rewrite ev0_1, ev0_4. unfold ext_word.
  apply bv_eq. rewrite ev0_2. rewrite !bv_add_unsigned, bv_shiftl_unsigned, sh3, w16, w0, !Z_to_bv_unsigned.
  rewrite (len_word_argv argv Hva). change (to_Z 0%uint63) with 0. change (to_Z 4%uint63) with 4. rewrite Z.add_0_r.
  rewrite (bv_wrap_small 64 (argcZ argv)) by (unfold bv_modulus; lia).
  rewrite ext_Z_sx32_small by lia.
  rewrite (bv_wrap_small 64 (argcZ argv)) by (unfold bv_modulus; lia).
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
  unfold bv_wrap, bv_modulus, envp_off. change (2 ^ Z.of_N 64) with (2 ^ 64).
  fold (SI.SP sp). rewrite (Z.mod_small (SP + 16)), (Z.mod_small (argcZ argv * 8)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma fact_envp' : den E0 (VP 2%uint63 (wp 0%uint63)) =
  den E0 (VAlu ALU_ADD (VP 1%uint63 (wp 16%uint63)) (VAlu ALU_SLL (VP 4%uint63 (wp 0%uint63)) (VL (wp 3%uint63)))).
Proof.
  pose proof len_BSB as HL. pose proof sstruct_val as HS.
  change (den E0 (VAlu ALU_ADD (VP 1%uint63 (wp 16%uint63)) (VAlu ALU_SLL (VP 4%uint63 (wp 0%uint63)) (VL (wp 3%uint63)))))
    with (bv_add (den E0 (VP 1%uint63 (wp 16%uint63))) (bv_shiftl (den E0 (VP 4%uint63 (wp 0%uint63))) (bv_and (wbv (wp 3%uint63)) (Z_to_bv 64 63)))).
  rewrite !den_VP0. cbn [den]. rewrite ev0_1, ev0_4.
  apply bv_eq. rewrite ev0_2. rewrite !bv_add_unsigned, bv_shiftl_unsigned, sh3, w16.
  rewrite (len_word_argv argv Hva).
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
  unfold bv_wrap, bv_modulus, envp_off. change (2 ^ Z.of_N 64) with (2 ^ 64).
  fold (SI.SP sp). rewrite (Z.mod_small (SP + 16)), (Z.mod_small (argcZ argv * 8)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma fact_auxv : den E0 (VP 3%uint63 (wp 0%uint63)) =
  den E0 (VAlu ALU_ADD (VP 2%uint63 (wp 0%uint63)) (VBlob false 8%uint63 (VL (wp 0%uint63)) 8%uint63)).
Proof.
  pose proof len_BSB as HL. pose proof sstruct_val as HS.
  change (den E0 (VAlu ALU_ADD (VP 2%uint63 (wp 0%uint63)) (VBlob false 8%uint63 (VL (wp 0%uint63)) 8%uint63)))
    with (bv_add (den E0 (VP 2%uint63 (wp 0%uint63))) (den E0 (VBlob false 8%uint63 (VL (wp 0%uint63)) 8%uint63))).
  rewrite !den_VP0, den_SIZE8. apply bv_eq. rewrite bv_add_unsigned, ev0_2, ev0_3, Z_to_bv64_unsigned by lia.
  unfold envp_off, auxv_off. rewrite bv_wrap_small; [lia|]. unfold bv_modulus. lia.
Qed.

Definition R1FL := Eval vm_compute in IMap.elements (rg_cells R1FT).
Lemma R1F_elements : IMap.elements (rg_cells R1FT) = R1FL. Proof. vm_compute. reflexivity. Qed.
Lemma R1F_find : forall g gr, IMap.find g (rg_cells R1FT) = Some gr ->
  (g = 0%uint63 /\ gr = Gran false [Cell 0%uint63 8%uint63 (VL (wp 2%uint63))]) \/
  (g = 1%uint63 /\ gr = Gran false [Cell 0%uint63 8%uint63 (VP 5%uint63 (wp 0%uint63))]) \/
  (g = 2%uint63 /\ gr = Gran false [Cell 0%uint63 8%uint63 (VP 10%uint63 (wp 0%uint63))]) \/
  (g = 3%uint63 /\ gr = Gran false [Cell 0%uint63 8%uint63 (VL (wp 0%uint63))]).
Proof.
  intros g gr H. apply (find_in_elements _ g gr (rg_cells R1FT) (imap_of_bst _ _)) in H. rewrite R1F_elements in H. unfold R1FL in H.
  destruct H as [H|[H|[H|[H|[]]]]]; [left|right;left|right;right;left|right;right;right]; injection H as <- <-; split; reflexivity.
Qed.
Lemma hiZ_R1F : hiZ E0 R1FT = 32. Proof. reflexivity. Qed.
Lemma loZ_R1F : loZ R1FT = - 8388608. Proof. reflexivity. Qed.
Lemma ev0_10 : bv_unsigned (ev E0 10%uint63) = SP + Z.of_nat (sstruct argv envp) + Z.of_nat (length a0) + 1.
Proof.
  change (ev E0 10%uint63) with (Z_to_bv 64 (SP + Z.of_nat (sstruct argv envp) + Z.of_nat (length a0) + 1)).
  apply Z_to_bv64_unsigned. pose proof len_BSB. pose proof sstruct_val. pose proof total_ge_a0. lia.
Qed.

Section Family2.
Hypothesis Hargc2 : length argv = 2%nat.

Lemma argv_eq2 : argv = [a0; a1].
Proof.
  pose proof argv_eq as E. unfold a1. destruct argv as [|x [|y [|z l]]]; cbn in Hargc2; try discriminate. reflexivity.
Qed.
Lemma a1_len : Z.of_nat (length a1) <= 131071.
Proof. pose proof Hva as (_ & _ & Hl & _). rewrite argv_eq2 in Hl. inversion Hl as [|? ? ? Hl']. inversion Hl'. assumption. Qed.
Lemma a1_nonul : ~ In (Z_to_bv 8 0) a1.
Proof. pose proof Hva as (_ & _ & _ & Hn & _). rewrite argv_eq2 in Hn. inversion Hn as [|? ? ? Hn']. inversion Hn'. assumption. Qed.
Lemma total2 : Z.of_nat (total_nat argv) = Z.of_nat (length a0) + 1 + Z.of_nat (length a1) + 1.
Proof. rewrite argv_eq2. cbn [total_nat]. lia. Qed.

Lemma den_SIZE10 : den E0 (VBlob false 10%uint63 (VL (wp 0%uint63)) 8%uint63) = Z_to_bv 64 (Z.of_nat (length a1) + 1).
Proof.
  cbn [den eb E0 eb0]. change (bv_unsigned (wbv (wp 0%uint63))) with 0. change (to_Z 8%uint63) with 8.
  apply bytes_val_le8. pose proof a1_len. lia.
Qed.
Lemma hiZ_R10 : hiZ E0 R10T = Z.of_nat (length a1) + 1.
Proof. unfold hiZ. change (rg_hi R10T) with (VBlob false 10%uint63 (VL (wp 0%uint63)) 8%uint63). rewrite den_SIZE10. apply Z_to_bv64_unsigned. pose proof a1_len. lia. Qed.

Lemma R1F_ok : region_ok SEGS [] E0 mem0 1%uint63 R1FT.
Proof.
  pose proof len_BSB as HL. pose proof sstruct_val as HS. pose proof total2 as HT2.
  assert (Hac2 : argcZ argv = 2) by (unfold argcZ, nargc; rewrite Hargc2; reflexivity).
  split.
  - apply imap_of_bst.
  - intros _. rewrite ev0_1, loZ_R1F, hiZ_R1F. fold SP. unfold two64. lia.
  - intros _ a. rewrite ev0_1, loZ_R1F, hiZ_R1F. fold SP. intros Ha.
    destruct (stack_valid a ltac:(unfold stack_max_size; lia)) as (H1 & H2 & H3). cbn [rg_w R1FT]. auto.
  - intros g gr Hg. rewrite ev0_1. fold SP.
    destruct (R1F_find g gr Hg) as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]; cbn [g_cells].
    + change (keyZ 0%uint63) with 0. replace (SP + 8 * 0) with SP by lia.
      apply (slot_ok_word SP _ (len_word argv)); [apply (argc_word SEGS PC PH sp argv envp uid hwcap draw Hsp Hfit) |].
      apply bv_eq. rewrite (len_word_argv argv Hva), Hac2. reflexivity.
    + change (keyZ 1%uint63) with 1. replace (SP + 8 * 1) with (SP + 8 + 8 * Z.of_nat 0) by lia.
      apply (slot_ok_word _ _ (nth 0 (argv_ptrs sp argv envp) (Z_to_bv 64 0))).
      * apply (argv_ptr_word SEGS PC PH sp argv envp uid hwcap draw Hsp Hfit). unfold nargc. rewrite Hargc2. lia.
      * rewrite den_VP0. rewrite (argv_ptr0 sp argv envp a0 (tl argv) argv_eq). reflexivity.
    + change (keyZ 2%uint63) with 2. replace (SP + 8 * 2) with (SP + 8 + 8 * Z.of_nat 1) by lia.
      apply (slot_ok_word _ _ (nth 1 (argv_ptrs sp argv envp) (Z_to_bv 64 0))).
      * apply (argv_ptr_word SEGS PC PH sp argv envp uid hwcap draw Hsp Hfit). unfold nargc. rewrite Hargc2. lia.
      * rewrite den_VP0. apply bv_eq. rewrite ev0_10, (argv_ptr1_val PH sp argv envp uid hwcap draw Hfit a0 a1 [] argv_eq2). reflexivity.
    + change (keyZ 3%uint63) with 3. replace (SP + 8 * 3) with (SP + 8 + 8 * argcZ argv) by lia.
      apply (slot_ok_word _ _ (Z_to_bv 64 0)); [apply (argv_null_word SEGS PC PH sp argv envp uid hwcap draw Hsp Hfit) | reflexivity].
  - intros g gr c i Hg Hc Hi. split; [|intros H; discriminate H]. intros _. rewrite loZ_R1F, hiZ_R1F.
    destruct (R1F_find g gr Hg) as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]; cbn [g_cells] in Hc; destruct Hc as [<-|[]];
      cbn [c_idx c_w] in *; change (to_Z 0%uint63) with 0 in *; change (to_Z 8%uint63) with 8 in *;
      [change (keyZ 0%uint63) with 0 | change (keyZ 1%uint63) with 1 | change (keyZ 2%uint63) with 2 | change (keyZ 3%uint63) with 3]; lia.
  - intros o Ho _ Hu. specialize (Ho eq_refl). rewrite loZ_R1F, hiZ_R1F in Ho. cbn [bg_byte rg_bg R1FT]. rewrite ev0_1. fold SP.
    destruct (Z.lt_ge_cases o 0) as [Hneg|Hpos].
    + apply rb_some. apply (mem0_below SEGS PC PH sp argv envp uid hwcap draw Hsp). unfold stack_max_size. lia.
    + exfalso. destruct (Z.lt_ge_cases o 8) as [H8|H8]; [|destruct (Z.lt_ge_cases o 16) as [H16|H16]; [|destruct (Z.lt_ge_cases o 24) as [H24|H24]]].
      * apply (covered_not_uncovered R1FT o 0%uint63 (VL (wp 2%uint63))); [change (keyZ 0%uint63) with 0; rewrite Z.div_small; lia | apply Z.mod_pos_bound; lia | reflexivity | exact Hu].
      * apply (covered_not_uncovered R1FT o 1%uint63 (VP 5%uint63 (wp 0%uint63))); [change (keyZ 1%uint63) with 1; apply (Z.div_unique_pos o 8 1 (o - 8)); lia | apply Z.mod_pos_bound; lia | reflexivity | exact Hu].
      * apply (covered_not_uncovered R1FT o 2%uint63 (VP 10%uint63 (wp 0%uint63))); [change (keyZ 2%uint63) with 2; apply (Z.div_unique_pos o 8 2 (o - 16)); lia | apply Z.mod_pos_bound; lia | reflexivity | exact Hu].
      * apply (covered_not_uncovered R1FT o 3%uint63 (VL (wp 0%uint63))); [change (keyZ 3%uint63) with 3; apply (Z.div_unique_pos o 8 3 (o - 24)); lia | apply Z.mod_pos_bound; lia | reflexivity | exact Hu].
Qed.

Lemma R10_ok : region_ok SEGS [] E0 mem0 10%uint63 R10T.
Proof.
  pose proof len_BSB as HL. pose proof sstruct_val as HS. pose proof total2 as HT2.
  split.
  - exact I.
  - intros _. rewrite ev0_10, (loZ_0 R10T eq_refl), hiZ_R10. unfold two64. lia.
  - intros _ a. rewrite ev0_10, (loZ_0 R10T eq_refl), hiZ_R10. intros Ha.
    destruct (stack_valid a ltac:(unfold stack_max_size; lia)) as (H1 & H2 & H3). cbn [rg_w R10T]. split; [exact H1|]. split; [intros H; discriminate H| exact H3].
  - intros g gr Hg. cbn in Hg. discriminate.
  - intros g gr c i Hg. cbn in Hg. discriminate.
  - intros o Ho _ _. specialize (Ho eq_refl). rewrite (loZ_0 R10T eq_refl), hiZ_R10 in Ho.
    cbn [bg_byte rg_bg R10T eb E0 eb0]. change (to_Z 0%uint63) with 0. rewrite Z.sub_0_r. rewrite ev0_10.
    replace (SP + Z.of_nat (sstruct argv envp) + Z.of_nat (length a0) + 1 + o)
      with (SP + Z.of_nat (sstruct argv envp) + Z.of_nat (length a0) + 1 + Z.of_nat (Z.to_nat o)) by lia.
    apply rb_some. rewrite (argv1_byte SEGS PC PH sp argv envp uid hwcap draw Hsp Hfit a0 a1 [] (Z.to_nat o) argv_eq2) by lia.
    reflexivity.
Qed.

Theorem PB1_E0 : PB_ARG1 (eb E0).
Proof.
  exists a1. cbn [eb E0]. unfold eb0.
  change (to_Z 3%uint63) with 3. change (to_Z 10%uint63) with 10. cbv iota.
  split; [reflexivity|]. split; [apply a1_nonul|]. split; [apply a1_len| reflexivity].
Qed.
End Family2.

Lemma hiZ_R6 : hiZ E0 R6T = 16. Proof. reflexivity. Qed.
Lemma R6_ok : region_ok SEGS [] E0 mem0 6%uint63 R6T.
Proof.
  pose proof len_BSB as HL. pose proof sstruct_val as HS.
  split.
  - exact I.
  - intros _. rewrite ev0_6, (loZ_0 R6T eq_refl), hiZ_R6. unfold raw_len, two64. lia.
  - intros _ a. rewrite ev0_6, (loZ_0 R6T eq_refl), hiZ_R6. unfold raw_len. intros Ha.
    destruct (stack_valid a ltac:(unfold stack_max_size; lia)) as (H1 & H2 & H3). cbn [rg_w R6T]. split; [exact H1|]. split; [intros H; discriminate H| exact H3].
  - intros g gr Hg. cbn in Hg. discriminate.
  - intros g gr c i Hg. cbn in Hg. discriminate.
  - intros o Ho _ _. specialize (Ho eq_refl). rewrite (loZ_0 R6T eq_refl), hiZ_R6 in Ho.
    cbn [bg_byte rg_bg R6T eb E0 eb0]. change (to_Z 6%uint63) with 6. change (to_Z 0%uint63) with 0. cbv iota. rewrite Z.sub_0_r, ev0_6.
    replace (SP + Z.of_nat (raw_len argv envp + pad argv envp) + o) with (SP + Z.of_nat (raw_len argv envp + pad argv envp) + Z.of_nat (Z.to_nat o)) by lia.
    apply rb_some. rewrite (random_byte SEGS PC PH sp argv envp uid hwcap draw Hsp Hfit (Z.to_nat o)) by lia. reflexivity.
Qed.

Lemma pad_spec : exists q, Z.of_nat (raw_len argv envp) + Z.of_nat (pad argv envp) = 8 * q.
Proof.
  unfold pad. set (r := Z.of_nat (raw_len argv envp)).
  pose proof (Z.mod_pos_bound r 8 ltac:(lia)) as Hr. pose proof (Z.div_mod r 8 ltac:(lia)) as Hd.
  destruct (Z.eq_dec (r mod 8) 0) as [E|E].
  - exists (r / 8). rewrite E. change ((8 - 0) mod 8) with 0. cbn [Z.to_nat]. lia.
  - exists (r / 8 + 1). rewrite (Z.mod_small (8 - r mod 8)) by lia. rewrite Z2Nat.id by lia. lia.
Qed.

Lemma wp_ok : forall i, w2Z (wp i) = to_Z i.
Proof. intros i. unfold w2Z. cbn [wt wl wp]. lia. Qed.

Lemma f_sp_range : fact_holds E0 (FRange 1%uint63 (wp 140735340871680%uint63) (wp 140737488355112%uint63)).
Proof.
  pose proof len_BSB as HL. pose proof sstruct_val as HS. pose proof total_ge_a0 as HA.
  cbn [fact_holds]. rewrite !wp_ok, ev0_1. change (to_Z 140735340871680%uint63) with 140735340871680.
  change (to_Z 140737488355112%uint63) with 140737488355112. fold (SI.SP sp).
  destruct pad_spec as [q Hq]. unfold raw_len in Hq. lia.
Qed.
Lemma f_sp_align : fact_holds E0 (FAlign 1%uint63 4%uint63).
Proof. cbn [fact_holds]. rewrite ev0_1. change (2 ^ to_Z 4%uint63) with 16. pose proof Hsp as (_ & _ & Hal). exact Hal. Qed.
Lemma f_argc_range : fact_holds E0 (FRange 4%uint63 (wp 1%uint63) (wp 1024%uint63)).
Proof. cbn [fact_holds]. rewrite !wp_ok, ev0_4, (len_word_argv argv Hva). change (to_Z 1%uint63) with 1. change (to_Z 1024%uint63) with 1024. lia. Qed.

Lemma window_fact : forall k, 140735340871680 <= bv_unsigned (ev E0 k) <= 140737488355328 ->
  fact_holds E0 (FRange k (wp 140735340871680%uint63) (wp 140737488355328%uint63)).
Proof. intros k H. cbn [fact_holds]. rewrite !wp_ok. change (to_Z 140735340871680%uint63) with 140735340871680. change (to_Z 140737488355328%uint63) with 140737488355328. exact H. Qed.
Lemma f_win2 : fact_holds E0 (FRange 2%uint63 (wp 140735340871680%uint63) (wp 140737488355328%uint63)).
Proof. apply window_fact. pose proof len_BSB. pose proof sstruct_val. rewrite ev0_2. unfold envp_off. lia. Qed.
Lemma f_win3 : fact_holds E0 (FRange 3%uint63 (wp 140735340871680%uint63) (wp 140737488355328%uint63)).
Proof. apply window_fact. pose proof len_BSB. pose proof sstruct_val. rewrite ev0_3. unfold auxv_off. lia. Qed.
Lemma f_win5 : fact_holds E0 (FRange 5%uint63 (wp 140735340871680%uint63) (wp 140737488355328%uint63)).
Proof. apply window_fact. pose proof len_BSB. pose proof sstruct_val. rewrite ev0_5. lia. Qed.
Lemma f_win6 : fact_holds E0 (FRange 6%uint63 (wp 140735340871680%uint63) (wp 140737488355328%uint63)).
Proof. apply window_fact. pose proof len_BSB. pose proof sstruct_val. rewrite ev0_6. unfold raw_len. lia. Qed.
Lemma f_win10 : fact_holds E0 (FRange 10%uint63 (wp 140735340871680%uint63) (wp 140737488355328%uint63)).
Proof. apply window_fact. pose proof len_BSB. pose proof sstruct_val. pose proof total_ge_a0. rewrite ev0_10. lia. Qed.
Lemma f_hwcap : fact_holds E0 (FRange 7%uint63 (wp 4397%uint63) (wp 2101549%uint63)).
Proof.
  cbn [fact_holds]. rewrite !wp_ok, ev0_7. change (to_Z 4397%uint63) with 4397. change (to_Z 2101549%uint63) with 2101549.
  pose proof Hhw as [-> | ->]; unfold hwcap_rv64gc, hwcap_rv64gcv; rewrite Z_to_bv64_unsigned; lia.
Qed.
Lemma f_envp : fact_holds E0 (FEq (VP 2%uint63 (wp 0%uint63))
  (VAlu ALU_ADD (VP 1%uint63 (wp 16%uint63)) (VAlu ALU_SLL (VExt true 0%uint63 4%uint63 (VP 4%uint63 (wp 0%uint63))) (VL (wp 3%uint63))))).
Proof. exact fact_envp. Qed.
Lemma f_envp' : fact_holds E0 (FEq (VP 2%uint63 (wp 0%uint63))
  (VAlu ALU_ADD (VP 1%uint63 (wp 16%uint63)) (VAlu ALU_SLL (VP 4%uint63 (wp 0%uint63)) (VL (wp 3%uint63))))).
Proof. exact fact_envp'. Qed.
Lemma f_auxv : fact_holds E0 (FEq (VP 3%uint63 (wp 0%uint63)) (VAlu ALU_ADD (VP 2%uint63 (wp 0%uint63)) (VBlob false 8%uint63 (VL (wp 0%uint63)) 8%uint63))).
Proof. exact fact_auxv. Qed.
Lemma f_size8_lo : fact_holds E0 (FULt (VL (wp 7%uint63)) (VBlob false 8%uint63 (VL (wp 0%uint63)) 8%uint63)).
Proof. cbn [fact_holds]. rewrite den_SIZE8, Z_to_bv64_unsigned by lia. change (bv_unsigned (den E0 (VL (wp 7%uint63)))) with 7. lia. Qed.
Lemma f_size8_hi : fact_holds E0 (FULe (VBlob false 8%uint63 (VL (wp 0%uint63)) 8%uint63) (VL (wp 2056%uint63))).
Proof. cbn [fact_holds]. rewrite den_SIZE8, Z_to_bv64_unsigned by lia. change (bv_unsigned (den E0 (VL (wp 2056%uint63)))) with 2056. lia. Qed.
Lemma f_size9_lo : fact_holds E0 (FULe (VL (wp 1%uint63)) (VBlob false 9%uint63 (VL (wp 0%uint63)) 8%uint63)).
Proof. pose proof a0_len. cbn [fact_holds]. rewrite den_SIZE9, Z_to_bv64_unsigned by lia. change (bv_unsigned (den E0 (VL (wp 1%uint63)))) with 1. lia. Qed.
Lemma f_size9_hi : fact_holds E0 (FULe (VBlob false 9%uint63 (VL (wp 0%uint63)) 8%uint63) (VL (wp 131072%uint63))).
Proof. pose proof a0_len. cbn [fact_holds]. rewrite den_SIZE9, Z_to_bv64_unsigned by lia. change (bv_unsigned (den E0 (VL (wp 131072%uint63)))) with 131072. lia. Qed.
Lemma f_rnd_align : fact_holds E0 (FAlign 6%uint63 3%uint63).
Proof.
  cbn [fact_holds]. change (2 ^ to_Z 3%uint63) with 8. change (ev E0 6%uint63) with (ARND sp argv envp).
  apply (proj2 (ARND_aligned PH sp argv envp uid hwcap draw Hfit)). pose proof Hsp as (_ & _ & Hal).
  unfold SI.SP. apply (proj1 (Z.mod_divide (bv_unsigned sp) 16 ltac:(lia))) in Hal. apply Z.mod_divide; [lia|]. destruct Hal as [q Hq]. exists (2 * q). lia.
Qed.

Lemma f_sp_le_auxv : fact_holds E0 (FULe (VP 1%uint63 (wp 0%uint63)) (VP 3%uint63 (wp 0%uint63))).
Proof.
  cbn [fact_holds]. rewrite !den_VP0, ev0_1, ev0_3. fold (SI.SP sp). pose proof Hargc. pose proof Henvc. unfold auxv_off. lia.
Qed.
Lemma f_sp_le_rnd8 : fact_holds E0 (FULe (VP 1%uint63 (wp 0%uint63)) (VP 6%uint63 (wp 8%uint63))).
Proof.
  cbn [fact_holds]. rewrite den_VP0, ev0_1. cbn [den]. rewrite bv_add_unsigned, ev0_6.
  change (bv_unsigned (wbv (wp 8%uint63))) with 8. fold (SI.SP sp). pose proof len_BSB. pose proof sstruct_val.
  pose proof Hlo. pose proof Htop. pose proof Hargc. pose proof Henvc.
  rewrite bv_wrap_small by (unfold bv_modulus, raw_len in *; lia). unfold raw_len in *. lia.
Qed.
Lemma f_sp_le_rnd : fact_holds E0 (FULe (VP 1%uint63 (wp 0%uint63)) (VP 6%uint63 (wp 0%uint63))).
Proof.
  cbn [fact_holds]. rewrite !den_VP0, ev0_1, ev0_6. fold (SI.SP sp). lia.
Qed.
Lemma f_sp_le_a0 : fact_holds E0 (FULe (VP 1%uint63 (wp 0%uint63)) (VP 5%uint63 (wp 0%uint63))).
Proof.
  cbn [fact_holds]. rewrite !den_VP0, ev0_1, ev0_5. fold (SI.SP sp). lia.
Qed.

Lemma f_a0_end : fact_holds E0 (FULe (VAlu ALU_ADD (VP 5%uint63 (wp 0%uint63)) (VBlob false 9%uint63 (VL (wp 0%uint63)) 8%uint63))
                                  (VL (wp 140737488355328%uint63))).
Proof.
  pose proof len_BSB. pose proof sstruct_val. pose proof total_ge_a0. pose proof Htop as HT. pose proof a0_len.
  cbn [fact_holds]. change (den E0 (VAlu _ ?a ?b)) with (bv_add (den E0 a) (den E0 b)).
  rewrite bv_add_unsigned, den_VP0, ev0_5, den_SIZE9, Z_to_bv64_unsigned by lia.
  change (bv_unsigned (den E0 (VL (wp 140737488355328%uint63)))) with 140737488355328.
  rewrite bv_wrap_small by (unfold bv_modulus; lia). lia.
Qed.
Lemma f_argc_ne2 : length argv <> 2%nat ->
  fact_holds E0 (FNe (VExt true 0%uint63 4%uint63 (VP 4%uint63 (wp 0%uint63))) (VL (wp 2%uint63))).
Proof.
  intros Hn. cbn [fact_holds]. intros X. apply (f_equal bv_unsigned) in X. revert X.
  cbn [den]. rewrite ev0_4. unfold ext_word. rewrite bv_add_unsigned, (len_word_argv argv Hva), w0, Z.add_0_r.
  change (to_Z 0%uint63) with 0. change (to_Z 4%uint63) with 4.
  rewrite (bv_wrap_small 64 (argcZ argv)) by (unfold bv_modulus; lia). rewrite ext_Z_sx32_small by lia.
  rewrite !Z_to_bv64_unsigned by lia. change (bv_unsigned (wbv (wp 2%uint63))) with 2. unfold argcZ, nargc. lia.
Qed.
Lemma f_argc_ne2' : length argv <> 2%nat -> fact_holds E0 (FNe (VP 4%uint63 (wp 0%uint63)) (VL (wp 2%uint63))).
Proof.
  intros Hn. cbn [fact_holds]. intros X. apply (f_equal bv_unsigned) in X. revert X.
  rewrite den_VP0, ev0_4, (len_word_argv argv Hva). change (bv_unsigned (den E0 (VL (wp 2%uint63)))) with 2. unfold argcZ, nargc. lia.
Qed.

Lemma f_win12 : fact_holds E0 (FRange 12%uint63 (wp 140735340871680%uint63) (wp 140737488355328%uint63)).
Proof. apply window_fact. pose proof len_BSB. pose proof sstruct_val. rewrite ev0_12. lia. Qed.
Lemma f_align12 : fact_holds E0 (FAlign 12%uint63 3%uint63).
Proof.
  cbn [fact_holds]. change (2 ^ to_Z 3%uint63) with 8. rewrite ev0_12, sstruct_val. pose proof Hsp as (_ & _ & Hal). fold (SI.SP sp) in Hal.
  apply Z.mod_divide; [lia|]. apply (proj1 (Z.mod_divide (SI.SP sp) 16 ltac:(lia))) in Hal. destruct Hal as [q Hq].
  exists (2 * q + 23 + argcZ argv + envcZ envp). lia.
Qed.
Lemma f_12_le_5 : fact_holds E0 (FULe (VP 12%uint63 (wp 0%uint63)) (VP 5%uint63 (wp 0%uint63))).
Proof. cbn [fact_holds]. rewrite !den_VP0, ev0_12, ev0_5. lia. Qed.
Lemma f_sp_le_12 : fact_holds E0 (FULe (VP 1%uint63 (wp 0%uint63)) (VP 12%uint63 (wp 0%uint63))).
Proof. cbn [fact_holds]. rewrite !den_VP0, ev0_1, ev0_12. fold (SI.SP sp). lia. Qed.
Lemma f_end5_12 : fact_holds E0 (FULe (VAlu ALU_ADD (VP 5%uint63 (wp 0%uint63)) (VBlob false 9%uint63 (VL (wp 0%uint63)) 8%uint63))
                                   (VAlu ALU_ADD (VP 12%uint63 (wp 0%uint63)) (VBlob false 15%uint63 (VL (wp 0%uint63)) 8%uint63))).
Proof.
  pose proof len_BSB. pose proof sstruct_val. pose proof total_ge_a0. pose proof Htop as HT. pose proof a0_len. pose proof strarea_len.
  cbn [fact_holds]. change (den E0 (VAlu ALU_ADD ?a ?b)) with (bv_add (den E0 a) (den E0 b)) at 1.
  change (den E0 (VAlu ALU_ADD (VP 12%uint63 ?o) ?b)) with (bv_add (den E0 (VP 12%uint63 o)) (den E0 b)).
  rewrite !bv_add_unsigned, !den_VP0, ev0_5, ev0_12, den_SIZE9, den_SIZE15, !Z_to_bv64_unsigned by lia.
  rewrite !bv_wrap_small by (unfold bv_modulus; lia). lia.
Qed.
Lemma f_end12 : fact_holds E0 (FULe (VAlu ALU_ADD (VP 12%uint63 (wp 0%uint63)) (VBlob false 15%uint63 (VL (wp 0%uint63)) 8%uint63))
                                 (VL (wp 140737488355328%uint63))).
Proof.
  pose proof len_BSB. pose proof sstruct_val. pose proof Htop as HT. pose proof strarea_len.
  cbn [fact_holds]. change (den E0 (VAlu _ ?a ?b)) with (bv_add (den E0 a) (den E0 b)).
  rewrite bv_add_unsigned, den_VP0, ev0_12, den_SIZE15, Z_to_bv64_unsigned by lia.
  change (bv_unsigned (den E0 (VL (wp 140737488355328%uint63)))) with 140737488355328.
  rewrite bv_wrap_small by (unfold bv_modulus; lia). lia.
Qed.

Lemma f_end2 : fact_holds E0 (FULe (VAlu ALU_ADD (VP 2%uint63 (wp 0%uint63)) (VBlob false 8%uint63 (VL (wp 0%uint63)) 8%uint63))
                                (VL (wp 140737488355328%uint63))).
Proof.
  pose proof len_BSB. pose proof sstruct_val. pose proof Htop as HT.
  cbn [fact_holds]. change (den E0 (VAlu _ ?a ?b)) with (bv_add (den E0 a) (den E0 b)).
  rewrite bv_add_unsigned, den_VP0, ev0_2, den_SIZE8, Z_to_bv64_unsigned by lia.
  change (bv_unsigned (den E0 (VL (wp 140737488355328%uint63)))) with 140737488355328.
  unfold envp_off in *. rewrite bv_wrap_small by (unfold bv_modulus; lia). lia.
Qed.
Lemma f_end3 : fact_holds E0 (FULe (VP 3%uint63 (wp 160%uint63)) (VL (wp 140737488355328%uint63))).
Proof.
  pose proof len_BSB. pose proof sstruct_val. pose proof Htop as HT.
  cbn [fact_holds]. change (den E0 (VP 3%uint63 (wp 160%uint63))) with (bv_add (ev E0 3%uint63) (wbv (wp 160%uint63))).
  rewrite bv_add_unsigned, ev0_3. change (bv_unsigned (wbv (wp 160%uint63))) with 160.
  change (bv_unsigned (den E0 (VL (wp 140737488355328%uint63)))) with 140737488355328.
  unfold auxv_off in *. rewrite bv_wrap_small by (unfold bv_modulus; lia). lia.
Qed.

Lemma f_a0_end16 : fact_holds E0 (FULe (VAlu ALU_ADD (VP 5%uint63 (wp 0%uint63)) (VBlob false 9%uint63 (VL (wp 0%uint63)) 8%uint63))
                                    (VL (wp 140737488355312%uint63))).
Proof.
  pose proof len_BSB. pose proof sstruct_val. pose proof total_ge_a0. pose proof Htop as HT. pose proof a0_len.
  cbn [fact_holds]. change (den E0 (VAlu _ ?a ?b)) with (bv_add (den E0 a) (den E0 b)).
  rewrite bv_add_unsigned, den_VP0, ev0_5, den_SIZE9, Z_to_bv64_unsigned by lia.
  change (bv_unsigned (den E0 (VL (wp 140737488355312%uint63)))) with 140737488355312.
  rewrite bv_wrap_small by (unfold bv_modulus; lia). lia.
Qed.
Lemma f_a0_base96 : fact_holds E0 (FULe (VP 1%uint63 (wp 96%uint63)) (VP 5%uint63 (wp 0%uint63))).
Proof.
  cbn [fact_holds]. rewrite (den_VP0 5%uint63), ev0_5. cbn [den]. rewrite bv_add_unsigned, ev0_1. change (bv_unsigned (wbv (wp 96%uint63))) with 96.
  fold (SI.SP sp). pose proof len_BSB. pose proof sstruct_val. pose proof Hlo. pose proof Htop. pose proof Hargc. pose proof Henvc.
  rewrite bv_wrap_small by (unfold bv_modulus; lia). lia.
Qed.
Lemma f_a0_base88 : fact_holds E0 (FULe (VP 1%uint63 (wp 88%uint63)) (VP 5%uint63 (wp 0%uint63))).
Proof.
  cbn [fact_holds]. rewrite (den_VP0 5%uint63), ev0_5. cbn [den]. rewrite bv_add_unsigned, ev0_1. change (bv_unsigned (wbv (wp 88%uint63))) with 88.
  fold (SI.SP sp). pose proof len_BSB. pose proof sstruct_val. pose proof Hlo. pose proof Htop. pose proof Hargc. pose proof Henvc.
  rewrite bv_wrap_small by (unfold bv_modulus; lia). lia.
Qed.
Section F2.
Hypothesis Hargc2 : length argv = 2%nat.
Lemma f_envp2 : fact_holds E0 (FEq (VP 2%uint63 (wp 0%uint63)) (VP 1%uint63 (wp 32%uint63))).
Proof.
  pose proof len_BSB. pose proof sstruct_val.
  cbn [fact_holds den]. rewrite ev0_1. apply bv_eq. rewrite !bv_add_unsigned, ev0_2, w0. fold (SI.SP sp).
  change (bv_unsigned (wbv (wp 32%uint63))) with 32. unfold envp_off. unfold argcZ, nargc. rewrite Hargc2.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite !Z.mod_small; lia.
Qed.
Lemma f_sp_le_a1 : fact_holds E0 (FULe (VP 1%uint63 (wp 0%uint63)) (VP 10%uint63 (wp 0%uint63))).
Proof.
  cbn [fact_holds]. rewrite !den_VP0, ev0_1, ev0_10. fold (SI.SP sp). lia.
Qed.
Lemma f_size10_lo : fact_holds E0 (FULe (VL (wp 1%uint63)) (VBlob false 10%uint63 (VL (wp 0%uint63)) 8%uint63)).
Proof. pose proof (a1_len Hargc2). cbn [fact_holds]. rewrite (den_SIZE10 Hargc2), Z_to_bv64_unsigned by lia. change (bv_unsigned (den E0 (VL (wp 1%uint63)))) with 1. lia. Qed.
Lemma f_size10_hi : fact_holds E0 (FULe (VBlob false 10%uint63 (VL (wp 0%uint63)) 8%uint63) (VL (wp 131072%uint63))).
Proof. pose proof (a1_len Hargc2). cbn [fact_holds]. rewrite (den_SIZE10 Hargc2), Z_to_bv64_unsigned by lia. change (bv_unsigned (den E0 (VL (wp 131072%uint63)))) with 131072. lia. Qed.
Lemma total_ge_a0a1 : Z.of_nat (length a0) + 1 + Z.of_nat (length a1) + 1 <= Z.of_nat (total_nat argv).
Proof.
  unfold a0, a1. destruct argv as [|x [|y l]]; try discriminate Hargc2. cbn [hd tl total_nat]. lia.
Qed.
Lemma f_a1_end : fact_holds E0 (FULe (VAlu ALU_ADD (VP 10%uint63 (wp 0%uint63)) (VBlob false 10%uint63 (VL (wp 0%uint63)) 8%uint63))
                                  (VL (wp 140737488355328%uint63))).
Proof.
  pose proof len_BSB. pose proof sstruct_val. pose proof total_ge_a0a1. pose proof Htop as HT. pose proof (a1_len Hargc2).
  cbn [fact_holds]. change (den E0 (VAlu _ ?a ?b)) with (bv_add (den E0 a) (den E0 b)).
  rewrite bv_add_unsigned, den_VP0, ev0_10, (den_SIZE10 Hargc2), Z_to_bv64_unsigned by lia.
  change (bv_unsigned (den E0 (VL (wp 140737488355328%uint63)))) with 140737488355328.
  rewrite bv_wrap_small by (unfold bv_modulus; lia). lia.
Qed.

Lemma f_a1_end16 : fact_holds E0 (FULe (VAlu ALU_ADD (VP 10%uint63 (wp 0%uint63)) (VBlob false 10%uint63 (VL (wp 0%uint63)) 8%uint63))
                                    (VL (wp 140737488355312%uint63))).
Proof.
  pose proof len_BSB. pose proof sstruct_val. pose proof total_ge_a0a1. pose proof Htop as HT. pose proof (a1_len Hargc2).
  cbn [fact_holds]. change (den E0 (VAlu _ ?a ?b)) with (bv_add (den E0 a) (den E0 b)).
  rewrite bv_add_unsigned, den_VP0, ev0_10, (den_SIZE10 Hargc2), Z_to_bv64_unsigned by lia.
  change (bv_unsigned (den E0 (VL (wp 140737488355312%uint63)))) with 140737488355312.
  rewrite bv_wrap_small by (unfold bv_modulus; lia). lia.
Qed.
Lemma f_a1_base96 : fact_holds E0 (FULe (VP 1%uint63 (wp 96%uint63)) (VP 10%uint63 (wp 0%uint63))).
Proof.
  cbn [fact_holds]. rewrite (den_VP0 10%uint63), ev0_10. cbn [den]. rewrite bv_add_unsigned, ev0_1. change (bv_unsigned (wbv (wp 96%uint63))) with 96.
  fold (SI.SP sp). pose proof len_BSB. pose proof sstruct_val. pose proof Hlo. pose proof Htop. pose proof Hargc. pose proof Henvc.
  rewrite bv_wrap_small by (unfold bv_modulus; lia). lia.
Qed.
Lemma f_12_le_10 : fact_holds E0 (FULe (VP 12%uint63 (wp 0%uint63)) (VP 10%uint63 (wp 0%uint63))).
Proof. cbn [fact_holds]. rewrite !den_VP0, ev0_12, ev0_10. lia. Qed.
Lemma f_end10_12 : fact_holds E0 (FULe (VAlu ALU_ADD (VP 10%uint63 (wp 0%uint63)) (VBlob false 10%uint63 (VL (wp 0%uint63)) 8%uint63))
                                    (VAlu ALU_ADD (VP 12%uint63 (wp 0%uint63)) (VBlob false 15%uint63 (VL (wp 0%uint63)) 8%uint63))).
Proof.
  pose proof len_BSB. pose proof sstruct_val. pose proof total_ge_a0a1. pose proof Htop as HT. pose proof (a1_len Hargc2). pose proof strarea_len.
  cbn [fact_holds]. change (den E0 (VAlu ALU_ADD ?a ?b)) with (bv_add (den E0 a) (den E0 b)) at 1.
  change (den E0 (VAlu ALU_ADD (VP 12%uint63 ?o) ?b)) with (bv_add (den E0 (VP 12%uint63 o)) (den E0 b)).
  rewrite !bv_add_unsigned, !den_VP0, ev0_10, ev0_12, (den_SIZE10 Hargc2), den_SIZE15, !Z_to_bv64_unsigned by lia.
  rewrite !bv_wrap_small by (unfold bv_modulus; lia). lia.
Qed.
End F2.

Theorem PB_E0 : PB_STD (eb E0).
Proof.
  exists a0, (envp_ptrs sp argv envp). cbn [eb E0]. unfold eb0.
  change (to_Z 1%uint63) with 1. change (to_Z 2%uint63) with 2. change (to_Z 8%uint63) with 8. change (to_Z 9%uint63) with 9.
  change (to_Z 6%uint63) with 6. cbv iota.
  rewrite length_envp_ptrs. fold (envcZ envp).
  split; [reflexivity|]. split; [apply a0_nonul|]. split; [apply a0_len|]. split; [reflexivity|].
  split; [pose proof Henvc as H; unfold envcZ in H; lia|]. split; [|split; [reflexivity|]; split; [reflexivity | apply length_at_random_bytes]].
  apply Forall_nth. intros k d Hk. rewrite length_envp_ptrs in Hk.
  rewrite (nth_indep _ d (Z_to_bv 64 0)) by (rewrite length_envp_ptrs; exact Hk).
  pose proof (envp_ptr_val PH sp argv envp uid hwcap draw Hfit k Hk). lia.
Qed.

Lemma so_regs0 : forall r,
  rget (Core (ms_regs ms0) (ms_fregs ms0) (ms_pc_val ms0) (ms_fcsr ms0) (ms_resv ms0)) (reg_of_r5 r)
  = den E0 (rf_get (rf_of Z0 [Z0; Z0; VP 1%uint63 (wp 0%uint63); Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0;
                           Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0]) r).
Proof.
  intros r. destruct r; try reflexivity.
  change (den E0 _) with (bv_add sp (wbv (wp 0%uint63))). rewrite bv_add_0_r by reflexivity. reflexivity.
Qed.
Lemma so_fregs0 : forall r, reg_get (ms_fregs ms0) (reg_of_r5 r) = den E0 (rf_get (rf_init Z0) r).
Proof. intros r. destruct r; reflexivity. Qed.
Lemma so_fcsr0 : bv_unsigned (ms_fcsr ms0) < 32.
Proof. change (bv_unsigned (Z_to_bv 32 0) < 32). rewrite Z_to_bv_small; [lia|]. unfold bv_modulus. lia. Qed.

Definition RFc : rf sv := rf_of Z0 [Z0; Z0; VP 1%uint63 (wp 0%uint63); Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0;
                                    Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0].
Definition FFc : rf sv := rf_of Z0 [Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0;
                                    Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0; Z0].
Definition REGS_N : IMap.t region :=
  imap_of [(0%uint63, R0T); (1%uint63, R1NT); (2%uint63, R2T); (3%uint63, R3T); (5%uint63, R5T); (6%uint63, R6T); (12%uint63, R12T)].
Definition REGS_F : IMap.t region :=
  imap_of [(0%uint63, R0T); (1%uint63, R1FT); (2%uint63, R2T); (3%uint63, R3T); (5%uint63, R5T); (6%uint63, R6T); (10%uint63, R10T); (12%uint63, R12T)].

Lemma REGS_N_elements : IMap.elements REGS_N = [(0%uint63, R0T); (1%uint63, R1NT); (2%uint63, R2T); (3%uint63, R3T); (5%uint63, R5T); (6%uint63, R6T); (12%uint63, R12T)].
Proof. vm_compute. reflexivity. Qed.
Lemma REGS_F_elements : IMap.elements REGS_F = [(0%uint63, R0T); (1%uint63, R1FT); (2%uint63, R2T); (3%uint63, R3T); (5%uint63, R5T); (6%uint63, R6T); (10%uint63, R10T); (12%uint63, R12T)].
Proof. vm_compute. reflexivity. Qed.

Lemma regs_N_cases : forall k r, IMap.find k REGS_N = Some r ->
  (k = 0%uint63 /\ r = R0T) \/ (k = 1%uint63 /\ r = R1NT) \/ (k = 2%uint63 /\ r = R2T) \/ (k = 3%uint63 /\ r = R3T)
  \/ (k = 5%uint63 /\ r = R5T) \/ (k = 6%uint63 /\ r = R6T) \/ (k = 12%uint63 /\ r = R12T).
Proof.
  intros k r H. apply (find_in_elements _ k r REGS_N (imap_of_bst _ _)) in H. rewrite REGS_N_elements in H.
  cbn [In] in H. intuition congruence.
Qed.
Lemma regs_F_cases : forall k r, IMap.find k REGS_F = Some r ->
  (k = 0%uint63 /\ r = R0T) \/ (k = 1%uint63 /\ r = R1FT) \/ (k = 2%uint63 /\ r = R2T) \/ (k = 3%uint63 /\ r = R3T)
  \/ (k = 5%uint63 /\ r = R5T) \/ (k = 6%uint63 /\ r = R6T) \/ (k = 10%uint63 /\ r = R10T) \/ (k = 12%uint63 /\ r = R12T).
Proof.
  intros k r H. apply (find_in_elements _ k r REGS_F (imap_of_bst _ _)) in H. rewrite REGS_F_elements in H.
  cbn [In] in H. intuition congruence.
Qed.

Lemma hiZ_R6' : hiZ E0 R6T = 16. Proof. reflexivity. Qed.

Ltac ranges Ha :=
  rewrite ?ev0_1 in Ha;
  rewrite ?ev0_2, ?ev0_3, ?ev0_5, ?ev0_6, ?ev0_10, ?ev0_12 in Ha;
  rewrite ?loZ_R1, ?hiZ_R1, ?loZ_R1F, ?hiZ_R1F, ?hiZ_R2, ?hiZ_R3, ?hiZ_R5, ?hiZ_R6, ?hiZ_R12,
          ?(loZ_0 R2T eq_refl), ?(loZ_0 R3T eq_refl), ?(loZ_0 R5T eq_refl), ?(loZ_0 R6T eq_refl), ?(loZ_0 R10T eq_refl), ?(loZ_0 R12T eq_refl) in Ha;
  fold (SI.SP sp) in Ha.

Lemma ms0_minv : forall a b, ms_mem ms0 a = Some b -> forall seg, find_segment SEGS (bv_unsigned a) 1 = Some seg -> seg_writable seg = true.
Proof.
  intros a b Hb seg Hseg. exfalso. pose proof (u64_range a) as Ha. pose proof Hlo as Hlo'.
  destruct (Z_lt_le_dec (bv_unsigned a) (SI.SP sp - stack_max_size)) as [Hlt|Hge].
  - rewrite ms0_mem, <- (Z_to_bv_bv_unsigned 64 a) in Hb. rewrite (mem0_none_low SEGS PC PH sp argv envp uid hwcap draw Hsp) in Hb by lia. discriminate Hb.
  - rewrite (find_segment_none SEGS (bv_unsigned a) 1 SEGTOP segs_below_top) in Hseg; [discriminate Hseg | | lia].
    unfold stack_max_size in Hge. unfold SI.SP in *. lia.
Qed.

Theorem st_ok_N : forall (OPS : optable) (pc0 : int) (FACTS : list fact) model,
  Z_to_bv 64 (Z.of_N PC) = Z_to_bv 64 (to_Z pc0) -> facts_hold E0 FACTS -> plain_table OPS -> mfacts model ->
  st_ok SEGS OPS E0 (SS pc0 RFc FFc RNone REGS_N FACTS [] [] 64%uint63) ms0 model.
Proof.
  intros OPS pc0 FACTS model Hpc HF PL Hmf.
  pose proof len_BSB as HL. pose proof sstruct_val as HS. pose proof total_ge_a0 as HA.
  split; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv].
  - exact Hpc.
  - reflexivity.
  - apply so_regs0.
  - apply so_fregs0.
  - reflexivity.
  - reflexivity.
  - apply so_fcsr0.
  - reflexivity.
  - reflexivity.
  - apply imap_of_bst.
  - intros k r Hk. rewrite ms0_mem.
    destruct (regs_N_cases k r Hk) as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]]]];
      [apply R0_ok | apply R1_ok | apply R2_ok | apply R3_ok | apply R5_ok | apply R6_ok | apply R12_ok].
  - intros k1 r1 k2 r2 H1 H2 Hne Hk1 Hk2 Hw a [Ha1 Ha2].
    destruct (regs_N_cases k1 r1 H1) as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]]]]; try discriminate Hk1;
    destruct (regs_N_cases k2 r2 H2) as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]]]]; try discriminate Hk2;
    try (exfalso; apply Hne; reflexivity);
    cbn [rg_w R1NT R2T R3T R5T R6T R12T] in Hw; try (exfalso; destruct Hw as [Hw|Hw]; discriminate Hw);
    ranges Ha1; ranges Ha2; unfold envp_off, auxv_off, raw_len in *; lia.
  - intros r g gr c Hr Hg.
    destruct (regs_N_cases _ r Hr) as [[_ ->]|[[H _]|[[H _]|[[H _]|[[H _]|[[H _]|[H _]]]]]]]; try discriminate H. cbn in Hg. discriminate.
  - exact HF.
  - constructor.
  - constructor.
  - exact (plain_minv OPS _ PL Hmf).
  - intros a _. exact (plain_cover OPS _ a PL).
  - exact ms0_minv.
Qed.

Theorem st_ok_F : forall (OPS : optable) (pc0 : int) (FACTS : list fact) model,
  length argv = 2%nat ->
  Z_to_bv 64 (Z.of_N PC) = Z_to_bv 64 (to_Z pc0) -> facts_hold E0 FACTS -> plain_table OPS -> mfacts model ->
  st_ok SEGS OPS E0 (SS pc0 RFc FFc RNone REGS_F FACTS [] [] 64%uint63) ms0 model.
Proof.
  intros OPS pc0 FACTS model Hargc2 Hpc HF PL Hmf.
  pose proof len_BSB as HL. pose proof sstruct_val as HS. pose proof total_ge_a0 as HA. pose proof (total2 Hargc2) as HT2.
  pose proof (hiZ_R10 Hargc2) as H10. assert (Hac2 : argcZ argv = 2) by (unfold argcZ, nargc; rewrite Hargc2; reflexivity).
  split; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv].
  - exact Hpc.
  - reflexivity.
  - apply so_regs0.
  - apply so_fregs0.
  - reflexivity.
  - reflexivity.
  - apply so_fcsr0.
  - reflexivity.
  - reflexivity.
  - apply imap_of_bst.
  - intros k r Hk. rewrite ms0_mem.
    destruct (regs_F_cases k r Hk) as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]]]]];
      [apply R0_ok | apply R1F_ok; exact Hargc2 | apply R2_ok | apply R3_ok | apply R5_ok | apply R6_ok | apply R10_ok; exact Hargc2 | apply R12_ok].
  - intros k1 r1 k2 r2 H1 H2 Hne Hk1 Hk2 Hw a [Ha1 Ha2].
    destruct (regs_F_cases k1 r1 H1) as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]]]]]; try discriminate Hk1;
    destruct (regs_F_cases k2 r2 H2) as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]]]]]; try discriminate Hk2;
    try (exfalso; apply Hne; reflexivity);
    cbn [rg_w R1FT R2T R3T R5T R6T R10T R12T] in Hw; try (exfalso; destruct Hw as [Hw|Hw]; discriminate Hw);
    ranges Ha1; ranges Ha2; rewrite ?H10 in Ha1; rewrite ?H10 in Ha2; unfold envp_off, auxv_off, raw_len in *; lia.
  - intros r g gr c Hr Hg.
    destruct (regs_F_cases _ r Hr) as [[_ ->]|[[H _]|[[H _]|[[H _]|[[H _]|[[H _]|[[H _]|[H _]]]]]]]]; try discriminate H. cbn in Hg. discriminate.
  - exact HF.
  - constructor.
  - constructor.
  - exact (plain_minv OPS _ PL Hmf).
  - intros a _. exact (plain_cover OPS _ a PL).
  - exact ms0_minv.
Qed.

End Entry.
End Image.
End InitLib.
