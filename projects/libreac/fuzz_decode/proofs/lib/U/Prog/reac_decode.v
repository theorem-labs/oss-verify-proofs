From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Prog Require Import reac_frame_inspect_c reac_decode_c ReacDecodeLib.
Import ListNotations.
Open Scope Z_scope.

Lemma decode_ok_spec : forall len bs nch ns,
  decode_ok len bs nch ns = true <->
  inspect_wf len bs = true /\ 0 < nch /\ nch mod 2 = 0 /\ 0 < ns /\ nch * ns <= 480.
Proof.
  intros. unfold decode_ok. rewrite !andb_true_iff, !Z.ltb_lt, Z.eqb_eq, Z.leb_le. tauto.
Qed.

Lemma braid_byte_at : forall bs nch ns ch s k, 0 <= ch -> 0 <= s < ns -> 0 <= k < 3 ->
  braid_byte bs nch ns (3 * (ch * ns + s) + k) = nth (Z.to_nat (50 + braid_pos s ch nch k)) bs (Z_to_bv 8 0).
Proof.
  intros bs nch ns ch s k Hch Hs Hk. unfold braid_byte.
  destruct (braid_div ch s k ns Hch Hs Hk) as (D1 & D2 & D3 & D4). rewrite D1, D2, D3, D4. reflexivity.
Qed.

Definition boff (p k : Z) : Z :=
  if p =? 0 then (if k =? 0 then 3 else if k =? 1 then 0 else 1)
  else (if k =? 0 then 4 else if k =? 1 then 5 else 2).

Section RD.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a1 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (raw mode out nch ns lo : Z).

Definition PostD : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1
                  (Z_to_bv 64 (if decode_ok (bv_unsigned a1) bs nch ns then ns else -1))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    wmono rsegs m m' /\ stk rsegs m' lo (bv_unsigned sp) /\
    (if decode_ok (bv_unsigned a1) bs nch ns
     then munch [(bv_unsigned sp - 80, bv_unsigned sp); (out, out + 3 * nch * ns)] m m' /\
          bytes_at rsegs m' out (braid_out bs nch ns)
     else munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m').

Local Notation SP := (bv_unsigned sp).
Local Notation FRD mk junk :=
  (rw_cells rsegs mk (bv_unsigned sp + -80) [CB 32 junk; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
Local Notation N := (3 * nch * ns).
Local Notation STATE pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 :=
  (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp x5 x6 x7 x8 x9
        x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
      F (Z_to_bv 64 pc) fc None mm (seg_rom rsegs)).

Hypothesis Hsp : lo + 80 <= SP.
Hypothesis Hlo : 0 <= lo.

Lemma rd_exit : forall (m1 : word -> option byte) (r : Z) (junk : list byte)
    (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 : word),
  FRD m1 junk -> stk rsegs m1 lo (SP + -80) -> wmono rsegs m m1 ->
  r = (if decode_ok (bv_unsigned a1) bs nch ns then ns else -1) ->
  (if decode_ok (bv_unsigned a1) bs nch ns
   then munch [(SP + -80, SP); (out, out + N)] m m1 /\ bytes_at rsegs m1 out (braid_out bs nch ns)
   else munch [(SP + -80, SP)] m m1) ->
  evt rsegs PostD (MS (mkR x1 (Z_to_bv 64 (SP + -80)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16
      x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31) F (Z_to_bv 64 0x13b78) fc None m1 (seg_rom rsegs)).
Proof.
  intros m1 r junk x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 HF ST WM Er HM.
  pose proof (u64_range sp) as Rsp.
  do 8 step.
  apply evt_done. unfold PostD. exists x5, x6, x7, x11, x12, x13, x14, x15, x16, x17, x28, x29, x30, x31, m1.
  split; [subst r; reflexivity|]. split; [exact WM|]. split.
  - pose proof (stk_release rsegs m1 lo (SP + -80) _ ST HF ltac:(lia)) as ST2.
    cbn [cells_size csize Nat.add] in ST2. replace (SP + -80 + Z.of_nat 80) with SP in ST2 by lia. exact ST2.
  - replace (SP - 80) with (SP + -80) by lia. exact HM.
Qed.

Hypothesis Hlen : length bs = 1492%nat.
Hypothesis Hraw : 0 <= raw.
Hypothesis Hraw2 : raw + 1492 <= 2^64.
Hypothesis Hout : 0 < out.
Hypothesis HoutN : out + N < 2^64.
Hypothesis Hnch : 0 < nch.
Hypothesis Hev : nch mod 2 = 0.
Hypothesis Hns : 0 < ns.
Hypothesis H480 : nch * ns <= 480.
Definition SEP : Prop :=
  (out + N <= raw \/ raw + 1492 <= out) /\ (out + N <= SP + -80 \/ SP <= out) /\
  (raw + 1492 <= SP + -80 \/ SP <= raw).
Hypothesis HSEP : SEP.
Hypothesis OK : decode_ok (bv_unsigned a1) bs nch ns = true.

Definition bpre (j : Z) : list byte := map (braid_byte bs nch ns) (map Z.of_nat (seq 0 (Z.to_nat j))).

Lemma bpre_len : forall j, 0 <= j -> Z.of_nat (length (bpre j)) = j.
Proof. intros j Hj. unfold bpre. rewrite length_mapseq. lia. Qed.

Lemma bpre_S : forall j, 0 <= j -> bpre (j + 1) = bpre j ++ [braid_byte bs nch ns j].
Proof.
  intros j Hj. unfold bpre. replace (Z.to_nat (j + 1)) with (Z.to_nat j + 1)%nat by lia.
  rewrite seq_app, !map_app. cbn [seq map Nat.add]. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma bw_ext : forall mk q0 q, bytes_at rsegs mk out (bpre q0) -> q0 = q -> 0 <= q -> out + q + 1 <= 2^64 ->
  bytes_at rsegs (write_to_mem mk (wa (out + q)) [braid_byte bs nch ns q]) out (bpre (q + 1)).
Proof.
  intros mk q0 q HB E Hq Hb. subst q0. pose proof (bpre_len q Hq) as L.
  rewrite bpre_S by lia. apply bytes_at_app. split.
  - apply bytes_at_write_other; [exact HB | lia | cbn [length]; lia | cbn [length]; lia].
  - rewrite L. apply bytes_at_write_same; cbn [length]; lia.
Qed.

Definition INVD (mk : word -> option byte) (j : Z) : Prop :=
  bytes_at rsegs mk raw bs /\ (exists junk, FRD mk junk) /\ stk rsegs mk lo (SP + -80) /\ wr_at rsegs mk out N /\
  munch [(SP + -80, SP); (out, out + N)] m mk /\ wmono rsegs m mk /\ bytes_at rsegs mk out (bpre j).

Lemma INVD_idx : forall mk j j', INVD mk j -> j = j' -> INVD mk j'.
Proof. intros; subst; assumption. Qed.

Lemma BR_rd : forall mk ch s k o, bytes_at rsegs mk raw bs -> 0 <= ch < nch -> 0 <= s < ns -> 0 <= k < 3 ->
  o = boff (ch mod 2) k ->
  ov_read_bytes rsegs mk (Z_to_bv 64 (raw + (50 + (3 * (s * nch + (ch - ch mod 2)) + o)))) 1 =
  Some [braid_byte bs nch ns (3 * (ch * ns + s) + k)].
Proof.
  intros mk ch s k o HB Hch Hs Hk Ho. rewrite braid_byte_at by lia.
  assert (Ep : braid_pos s ch nch k = 3 * (s * nch + (ch - ch mod 2)) + o).
  { unfold braid_pos, boff in *. cbv zeta. subst o. destruct (ch mod 2 =? 0), (k =? 0), (k =? 1); lia. }
  rewrite Ep.
  pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hm.
  assert (s * nch <= (ns - 1) * nch) by nia.
  assert (ch - ch mod 2 <= nch - 2) by (Z.div_mod_to_equations; lia).
  assert (0 <= ch - ch mod 2) by (Z.div_mod_to_equations; lia).
  assert (0 <= o <= 5) by (unfold boff in Ho; subst o; destruct (ch mod 2 =? 0), (k =? 0), (k =? 1); lia).
  apply rd1; [exact HB|]. rewrite Hlen. nia.
Qed.

Ltac stf :=
  let D1 := fresh "D" in let D2 := fresh "D" in let D3 := fresh "D" in
  pose proof HSEP as [D1 [D2 D3]]; st; clear D1 D2 D3.

Ltac ostore :=
  rewrite ?le1_zxb;
  lazymatch goal with
  | |- evt ?sg ?Q (MS ?R ?Fr ?pc ?f ?rv (write_to_mem ?mk ?w [?b]) ?ro) =>
      let a := addr_expr w in
      lazymatch a with
      | out + ?q =>
          change (evt sg Q (MS R Fr pc f rv (write_to_mem mk (wa (out + q)) [b]) ro));
          match goal with BW : bytes_at _ mk out (bpre ?q0) |- _ =>
            apply (bw_ext mk q0 q) in BW; [ | lia | lia | lia ]
          end;
          match goal with H : Z.of_nat (length (bpre _)) = _ |- _ => clear H end;
          assert (LB : Z.of_nat (length (bpre (q + 1))) = q + 1) by (apply bpre_len; lia);
          let D1 := fresh "D" in let D2 := fresh "D" in let D3 := fresh "D" in
          pose proof HSEP as [D1 [D2 D3]];
          transport_chunks sg mk (out + q) [b]; footprint_after_store sg mk (out + q) [b];
          clear D1 D2 D3;
          let m2 := fresh "m" in set (m2 := write_to_mem mk (wa (out + q)) [b]) in *; clearbody m2
      end
  end.

Ltac rebundle :=
  lazymatch goal with H : rw_cells _ ?mm ?A (?c1 :: ?c2 :: ?c3 :: ?c4 :: ?post) |- _ =>
    apply (rw_cells_merge rsegs mm A [] [c1; c2; c3; c4] post) in H; cbn [app cells_size csize Nat.add] in H;
    split; [assumption|]; split; [eexists; exact H|]; split; [assumption|]; split; [assumption|];
    split; [assumption|]; split; [assumption|]; eassumption
  end.

Lemma rd_inner : forall (ch : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x30 x31 : word),
  0 <= ch < nch ->
  bv_unsigned x5 = 18446744073709551615 -> bv_unsigned x6 = 18446744073709551615 - (raw + 50) ->
  bv_unsigned x7 = 2147483646 -> bv_unsigned x10 = ch -> bv_unsigned x11 = nch -> bv_unsigned x12 = ns ->
  bv_unsigned x13 = raw + 50 -> bv_unsigned x14 = 18446744073709551608 -> bv_unsigned x15 = SP + -80 + 8 ->
  bv_unsigned x16 = 18446744073709551599 -> bv_unsigned x17 = 2 -> bv_unsigned x28 = 18446744073709551607 ->
  bv_unsigned x30 = ch - ch mod 2 -> bv_unsigned x31 = ch mod 2 ->
  (forall (m2 : word -> option byte) (y8 y9 y18 y19 y20 y29 : word),
     bv_unsigned y9 = out + 3 * (ch * ns + ns) - 3 -> INVD m2 (3 * (ch * ns + ns)) ->
     evt rsegs PostD (STATE 0x13b68 m2 x1 x5 x6 x7 y8 y9 x10 x11 x12 x13 x14 x15 x16 x17 y18 y19 y20 x28 y29 x30 x31)) ->
  forall (K : nat) (s : Z) (m1 : word -> option byte) (x8 x9 x18 x19 x20 x29 : word),
  Z.to_nat (ns - s) = K -> 0 <= s < ns ->
  bv_unsigned x29 = s -> bv_unsigned x8 = out + 3 * (ch * ns + s) -> bv_unsigned x18 = out + 3 * (ch * ns + s) ->
  INVD m1 (3 * (ch * ns + s)) ->
  evt rsegs PostD (STATE 0x13a9c m1 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31).
Proof.
  intros ch x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x30 x31
    Hch H5 H6 H7 H10 H11 H12 H13 H14 H15 H16 H17 H28 H30 H31 CONT K.
  apply wv in H5, H6, H7, H10, H11, H12, H13, H14, H15, H16, H17, H28, H30, H31.
  subst x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x30 x31.
  pose proof (geom_bounds nch ns ltac:(lia) ltac:(lia) H480) as GB.
  pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hm.
  assert (ch - ch mod 2 <= nch - 2) by (Z.div_mod_to_equations; lia).
  assert (0 <= ch - ch mod 2) by (Z.div_mod_to_equations; lia).
  pose proof (u64_range sp) as Rsp.
  induction K as [K IH] using lt_wf_ind.
  intros s m1 x8 x9 x18 x19 x20 x29 HK Hs H29 H8 H18 I0.
  pose proof (row_bounds s ns nch Hs ltac:(lia)) as RB1.
  pose proof (row_bounds ch nch ns Hch ltac:(lia)) as RB2.
  apply wv in H29, H8, H18. subst x29 x8 x18.
  destruct I0 as (BR & (junk & FR) & ST & WA & MU & WM & BW).
  assert (LB : Z.of_nat (length (bpre (3 * (ch * ns + s)))) = 3 * (ch * ns + s)) by (apply bpre_len; lia).
  st. st. st. cnd false.
  st. st. st. st. st. cnd false.
  st. st. st.
  st.
  destruct (Z.eqb_spec (ch mod 2) 0) as [EP|EP].
  - cnd false.
    st. stf. st. cnd false.
    stf. st. cnd false.
    st. st.
    stf. st. cnd false.
    st. st. cnd false.
    st.
    pose proof (BR_rd _ ch s 0 3 BR Hch Hs ltac:(lia) ltac:(rewrite EP; reflexivity)) as HR.
    pose proof (wr_at_store_ok rsegs _ out N (3 * (ch * ns + s) + 0) 1 WA ltac:(lia) ltac:(lia)) as HS.
    st. st. clear HR HS. ostore.
    st. st. cnd false.
    st. st. cnd false.
    st.
    pose proof (BR_rd _ ch s 1 0 BR Hch Hs ltac:(lia) ltac:(rewrite EP; reflexivity)) as HR.
    pose proof (wr_at_store_ok rsegs _ out N (3 * (ch * ns + s) + 1) 1 WA ltac:(lia) ltac:(lia)) as HS.
    st. st. clear HR HS. ostore.
    st. st. cnd false.
    st. st. cnd false.
    st.
    pose proof (BR_rd _ ch s 2 1 BR Hch Hs ltac:(lia) ltac:(rewrite EP; reflexivity)) as HR.
    pose proof (wr_at_store_ok rsegs _ out N (3 * (ch * ns + s) + 2) 1 WA ltac:(lia) ltac:(lia)) as HS.
    st. st. st. st. clear HR HS. ostore.
    st. st.
    replace (SP + -72) with (SP + -80 + 8) by lia.
    brq BR'.
    + eapply CONT; [rewrite unsigned_lit by lia; lia | eapply INVD_idx; [rebundle | lia]].
    + eapply (IH (Z.to_nat (ns - (s + 1))) ltac:(lia) (s + 1));
        [ reflexivity | lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
        | rewrite unsigned_lit by lia; lia | eapply INVD_idx; [rebundle | lia] ].
  - assert (E1 : ch mod 2 = 1) by lia. clear EP.
    cnd true.
    st. stf. st. cnd false.
    st. stf. st. cnd false.
    st.
    stf. st. cnd false.
    st. st. cnd false.
    st.
    pose proof (BR_rd _ ch s 0 4 BR Hch Hs ltac:(lia) ltac:(rewrite E1; reflexivity)) as HR.
    pose proof (wr_at_store_ok rsegs _ out N (3 * (ch * ns + s) + 0) 1 WA ltac:(lia) ltac:(lia)) as HS.
    st. st. clear HR HS. ostore.
    st. st. cnd false.
    st. st. cnd false.
    st.
    pose proof (BR_rd _ ch s 1 5 BR Hch Hs ltac:(lia) ltac:(rewrite E1; reflexivity)) as HR.
    pose proof (wr_at_store_ok rsegs _ out N (3 * (ch * ns + s) + 1) 1 WA ltac:(lia) ltac:(lia)) as HS.
    st. st. clear HR HS. ostore.
    st. st. cnd false.
    st. st. cnd false.
    st.
    pose proof (BR_rd _ ch s 2 2 BR Hch Hs ltac:(lia) ltac:(rewrite E1; reflexivity)) as HR.
    pose proof (wr_at_store_ok rsegs _ out N (3 * (ch * ns + s) + 2) 1 WA ltac:(lia) ltac:(lia)) as HS.
    st. st. st. st. clear HR HS. ostore.
    st. st.
    replace (SP + -72) with (SP + -80 + 8) by lia.
    brq BR'.
    + eapply CONT; [rewrite unsigned_lit by lia; lia | eapply INVD_idx; [rebundle | lia]].
    + eapply (IH (Z.to_nat (ns - (s + 1))) ltac:(lia) (s + 1));
        [ reflexivity | lia | rewrite unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia
        | rewrite unsigned_lit by lia; lia | eapply INVD_idx; [rebundle | lia] ].
Qed.

Lemma rd_outer : forall (K : nat) (ch : Z) (m1 : word -> option byte)
    (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 : word),
  Z.to_nat (nch - ch) = K -> 0 <= ch < nch ->
  bv_unsigned x5 = 18446744073709551615 -> bv_unsigned x6 = 18446744073709551615 - (raw + 50) ->
  bv_unsigned x7 = 2147483646 -> bv_unsigned x8 = out + 3 * (ch * ns) -> bv_unsigned x10 = ch ->
  bv_unsigned x11 = nch -> bv_unsigned x12 = ns -> bv_unsigned x13 = raw + 50 ->
  bv_unsigned x14 = 18446744073709551608 -> bv_unsigned x15 = SP + -80 + 8 ->
  bv_unsigned x16 = 18446744073709551599 -> bv_unsigned x17 = 2 -> bv_unsigned x28 = 18446744073709551607 ->
  INVD m1 (3 * (ch * ns)) ->
  evt rsegs PostD (STATE 0x13a8c m1 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31).
Proof.
  induction K as [K IH] using lt_wf_ind.
  intros ch m1 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31
    HK Hch H5 H6 H7 H8 H10 H11 H12 H13 H14 H15 H16 H17 H28 I0.
  pose proof (row_bounds ch nch ns Hch ltac:(lia)) as RB2.
  pose proof (geom_bounds nch ns ltac:(lia) ltac:(lia) H480) as GB.
  pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hm.
  assert (0 <= ch - ch mod 2) by (Z.div_mod_to_equations; lia).
  pose proof (u64_range sp) as Rsp.
  apply wv in H5, H6, H7, H8, H10, H11, H12, H13, H14, H15, H16, H17, H28.
  subst x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28.
  st. st. rewrite (land_2m2 ch) by lia. st. rewrite land1. st.
  eapply (rd_inner ch) with (K := Z.to_nat (ns - 0)) (s := 0).
  all: lazymatch goal with
       | |- forall _ : word -> option byte, _ => idtac
       | |- INVD _ _ => eapply INVD_idx; [exact I0 | lia]
       | _ => first [ lia | reflexivity | ufin ]
       end.
  intros m2 y8 y9 y18 y19 y20 y29 H9 I2. apply wv in H9. subst y9.
  st. st. st.
  brq BR.
  - assert (EN : nch * ns = ch * ns + ns) by (replace nch with (ch + 1) by lia; ring).
    st.
    destruct I2 as (BR2 & (junk2 & FR2) & ST2 & WA2 & MU2 & WM2 & BW2).
    eapply rd_exit with (r := ns); [exact FR2 | exact ST2 | exact WM2 | rewrite OK; reflexivity | ].
    rewrite OK. split; [exact MU2|].
    replace (braid_out bs nch ns) with (bpre (3 * (ch * ns + ns))) by (unfold bpre, braid_out; do 3 f_equal; lia).
    exact BW2.
  - assert (EQ1 : (ch + 1) * ns = ch * ns + ns) by ring.
    eapply (IH (Z.to_nat (nch - (ch + 1))) ltac:(lia) (ch + 1)).
    all: lazymatch goal with
         | |- INVD _ _ => eapply INVD_idx; [exact I2 | lia]
         | _ => first [ reflexivity | lia | (rewrite unsigned_lit by lia; lia) | ufin ]
         end.
Qed.

End RD.

Theorem reac_decode_holds : reac_frame_inspect_contract -> reac_decode_contract.
Proof.
  intros HI. unfold reac_decode_contract, REAC_DECODE.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m bs raw mode out nch ns lo E0 E2 E3 Rraw Rmode Rout HB Rnch Rns HM ST LO DR DM HO NR NM NO.
  subst a0 a2 a3.
  pose proof (u64_range sp) as Rsp.
  assert (Hlo : 0 <= lo) by (destruct ST as [? _]; lia).
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 80%nat ST.
  do 11 step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
    eapply evt_cut; [eapply (HI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m1 bs) |] end.
  { intros L. destruct (HB L) as [LEN BB]. split; [exact LEN|]. rewrite unsigned_lit by lia. split.
    - eapply bytes_at_transport; [exact BB | exact MU |]. cbn [disjoint_from]. rewrite LEN.
      specialize (DR L). split; [lia | exact I].
    - exact (NR L). }
  intros ms' (a1' & a2' & ->).
  replace (ret_pc (Z_to_bv 64 0x13a18)) with (Z_to_bv 64 0x13a18) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  step. rewrite inspect_valid_bit. step. step.
  destruct (inspect_wf (bv_unsigned a1) bs) eqn:W.
  2:{ if_true.
      assert (PO : decode_ok (bv_unsigned a1) bs nch ns = false) by (unfold decode_ok; rewrite W; reflexivity).
      eapply rd_exit with (r := -1).
      all: first [ exact FR | exact ST | exact WM | lia | rewrite PO; first [reflexivity | exact MU] ]. }
  if_false.
  assert (L : bv_unsigned a1 = 1492) by (unfold inspect_wf in W; rewrite !andb_true_iff, !Z.eqb_eq in W; tauto).
  destruct (HB L) as [LEN BB]. specialize (DR L). specialize (NR L). destruct (NM eq_refl) as [NM0 NM4].
  assert (NR' : 0 < raw) by lia. assert (NM0' : 0 < mode) by lia. clear NR NM0 NM.
  pose proof (bytes_at_bound _ _ _ _ BB) as BBB. rewrite LEN in BBB.
  apply bytes_at_app in HM. destruct HM as [HM1 HM2]. rewrite length_le4 in HM2.
  replace (mode + 4 + Z.of_nat 4) with (mode + 8) in HM2 by lia.
  pose proof (rd_all _ _ _ HM1) as HR1. rewrite length_le4 in HR1.
  pose proof (rd_all _ _ _ HM2) as HR2. rewrite length_le4 in HR2.
  step. cnd false.
  step. step. cnd false.
  step. cnd false.
  st. rewrite (land3_0 mode) by lia.
  step. cnd false.
  step. rewrite sx32_lit by lia.
  step. rewrite lts0_lit by lia. brq BN.
  2:{ assert (PO : decode_ok (bv_unsigned a1) bs nch ns = false)
        by (apply not_true_iff_false; rewrite decode_ok_spec; lia).
      eapply rd_exit with (r := -1).
      all: first [ exact FR | exact ST | exact WM | lia | rewrite PO; first [reflexivity | exact MU] ]. }
  step. rewrite (unsigned_lit nch) by lia. rewrite land1.
  step. brq BE.
  2:{ assert (PO : decode_ok (bv_unsigned a1) bs nch ns = false)
        by (apply not_true_iff_false; rewrite decode_ok_spec; lia).
      eapply rd_exit with (r := -1).
      all: first [ exact FR | exact ST | exact WM | lia | rewrite PO; first [reflexivity | exact MU] ]. }
  step. rewrite sx32_lit by lia.
  step. rewrite lts0_lit by lia. brq BS.
  2:{ assert (PO : decode_ok (bv_unsigned a1) bs nch ns = false)
        by (apply not_true_iff_false; rewrite decode_ok_spec; lia).
      eapply rd_exit with (r := -1).
      all: first [ exact FR | exact ST | exact WM | lia | rewrite PO; first [reflexivity | exact MU] ]. }
  pose proof (prod_bound62 ns nch ltac:(lia) ltac:(lia)).
  step. rewrite (unsigned_lit ns), (unsigned_lit nch) by lia.
  step. step. brq BM.
  { assert (PO : decode_ok (bv_unsigned a1) bs nch ns = false)
        by (apply not_true_iff_false; rewrite decode_ok_spec; lia).
      eapply rd_exit with (r := -1).
      all: first [ exact FR | exact ST | exact WM | lia | rewrite PO; first [reflexivity | exact MU] ]. }
  assert (PO : decode_ok (bv_unsigned a1) bs nch ns = true)
    by (rewrite decode_ok_spec; split; [exact W|]; repeat split; lia).
  destruct (HO PO) as (HW & HoutN & DOR & DOS). specialize (NO PO).
  assert (NO' : 0 < out) by lia. clear NO.
  do 11 step.
  eapply rd_outer with (K := Z.to_nat (nch - 0)) (ch := 0) (ra := ra) (sp := sp) (s0 := s0) (s1 := s1) (s2 := s2)
    (s3 := s3) (s4 := s4) (a1 := a1) (m := m) (bs := bs) (raw := raw) (out := out) (nch := nch) (ns := ns) (lo := lo).
  all: lazymatch goal with
       | |- context [INVD] => idtac
       | |- context [SEP] => unfold SEP; split; [|split]; lia
       | _ => first [ assumption | reflexivity | lia | ufin ]
       end.
  replace (3 * (0 * ns)) with 0 by lia.
  split; [|split; [eexists; exact FR|split; [exact ST|split; [|split; [|split; [exact WM|]]]]]].
  - eapply bytes_at_transport; [exact BB | exact MU |]. cbn [disjoint_from]. rewrite LEN. split; [lia | exact I].
  - eapply wr_at_transport; [exact HW | exact WM].
  - apply munch_extend. exact MU.
  - unfold bpre. change (Z.to_nat 0) with 0%nat. cbn [seq map].
    split; [lia|]. split; [cbn [length Z.of_nat]; lia|]. intros i Hi. cbn [length] in Hi. lia.
Qed.
