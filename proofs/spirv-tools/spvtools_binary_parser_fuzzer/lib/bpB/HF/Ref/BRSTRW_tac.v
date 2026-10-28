(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BBytes.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BStrFun.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BRSTRW_merge.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BtoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac reg_val r :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
    eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end)
  end.
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.

Ltac name_list xs L :=
  lazymatch type of L with
  | length _ = O => destruct xs; [clear L | cbn in L; discriminate]
  | length _ = S _ => let x := fresh "x" in let xs' := fresh "xs" in
      destruct xs as [|x xs']; [cbn in L; discriminate | cbn in L; apply Nat.succ_inj in L; name_list xs' L]
  end.

Ltac window base k HW :=
  lazymatch goal with SRC : bytes_at ?segs ?m ?S ?src |- _ =>
    let xs := fresh "xs" in let L := fresh "L" in
    destruct (window_ex src base k ltac:(lia)) as [xs [HW L]]; name_list xs L
  end.

Ltac woff base c :=
  let cz := eval vm_compute in (Z.of_nat c) in
  lazymatch cz with 0%Z => base | _ => constr:((base + cz)%Z) end.

Ltac anorm REG imm :=
  lazymatch REG with
  | Z_to_bv 64 ?E =>
      let E' :=
        lazymatch imm with
        | 0%Z => E
        | _ => lazymatch E with
               | Z.add ?x ?a =>
                   let isl := lazymatch a with Z0 => true | Zpos _ => true | Zneg _ => true | _ => false end in
                   lazymatch isl with
                   | true => let s := eval vm_compute in (a + imm)%Z in
                             lazymatch s with 0%Z => x | _ => constr:(Z.add x s) end
                   | false => constr:(Z.add E imm)
                   end
               | _ => constr:(Z.add E imm)
               end
        end in
      constr:(Z_to_bv 64 E')
  | _ => lazymatch imm with 0%Z => REG | _ => constr:(Z_to_bv 64 (bv_unsigned REG + imm)%Z) end
  end.

Ltac cur_mem_addr :=
  lazymatch goal with |- evt ?segs _ (MS ?R _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with
    | Some (Load _ _ _ ?rs ?imm, _) =>
        let rz := eval vm_compute in (bv_unsigned rs) in
        let immz := eval vm_compute in (bv_signed imm) in
        let REG := reg_val rz in anorm REG immz
    | Some (Store _ ?rs _ ?imm, _) =>
        let rz := eval vm_compute in (bv_unsigned rs) in
        let immz := eval vm_compute in (bv_signed imm) in
        let REG := reg_val rz in anorm REG immz
    end end end.

Ltac addr_tac :=
  unfold wa;
  first [ reflexivity
        | f_equal; lia
        | lazymatch goal with |- ?v = Z_to_bv 64 ?e =>
            replace e with (bv_unsigned v) by lia; symmetry; apply Z_to_bv_bv_unsigned end ].

Definition ld_facts (base : Z) (c j kw : nat) (i : Z) : Prop :=
  (0 <= base)%Z /\ (c + j <= kw)%nat /\ (i = base + Z.of_nat c)%Z.

Lemma mc_read1 : forall segs m S src kw base xsw c i a b,
  bytes_at segs m S src -> firstn kw (skipn (Z.to_nat base) src) = xsw ->
  ld_facts base c 1 kw i -> nth_error xsw c = Some b -> a = wa (S + i) ->
  ov_read_bytes segs m a 1 = Some [b].
Proof.
  intros segs m S src kw base xsw c i a b SRC HW (Hb & Hc & Hi) Hn Ha.
  eapply (u8ro_read segs m S src i b a SRC); [ | lia | exact Ha ].
  rewrite <- Hn. eapply window_nth; eauto; lia.
Qed.

Lemma mc_read4 : forall segs m S src kw base xsw c i a,
  bytes_at segs m S src -> firstn kw (skipn (Z.to_nat base) src) = xsw -> length xsw = kw ->
  ld_facts base c 4 kw i -> a = wa (S + i) ->
  exists w, ov_read_bytes segs m a 4 = Some w /\ w = firstn 4 (skipn c xsw) /\ length w = 4%nat.
Proof.
  intros segs m S src kw base xsw c i a SRC HW HL (Hb & Hc & Hi) ->.
  assert (L : (Z.to_nat base + kw <= length src)%nat).
  { apply (f_equal (@length byte)) in HW. rewrite length_firstn, length_skipn, HL in HW. lia. }
  exists (firstn 4 (skipn (Z.to_nat i) src)). split; [|split].
  - apply (bytes_at_read segs m S src i 4 SRC); lia.
  - eapply window_sub; eauto; lia.
  - rewrite length_firstn, length_skipn. lia.
Qed.

Definition st_facts (S D n base : Z) (c k kw : nat) (P : Z) : Prop :=
  ((0 <= base)%Z /\ (c + k <= kw)%nat /\ P = base + Z.of_nat c /\ 0 <= P /\ P + Z.of_nat k <= n /\
   (S + n <= D \/ D + n <= S) /\ 0 <= D /\ D + n <= 2^64)%Z.

Lemma mc_store_ok : forall segs m1 S D n src kw base xsw c k P bs a,
  u8arr segs m1 D bs -> copied src bs (Z.to_nat P) -> length src = Z.to_nat n ->
  firstn kw (skipn (Z.to_nat base) src) = xsw ->
  st_facts S D n base c k kw P -> a = wa (D + P) -> store_ok segs m1 a k = true.
Proof.
  intros segs m1 S D n src kw base xsw c k P bs a DST [L _] LEN _ (_ & _ & _ & HP & Hk & _) Ha.
  eapply (u8arr_store_ok_n segs m1 D bs P k a DST); [lia | | exact Ha]. rewrite L, LEN. lia.
Qed.

Lemma mc_store : forall segs m0 m1 S D n src kw base xsw c k P bs xs a,
  bytes_at segs m1 S src -> u8arr segs m1 D bs -> copied src bs (Z.to_nat P) ->
  mem_inv segs m1 -> munch [(D, D + n)]%Z m0 m1 -> wmono segs m0 m1 ->
  length src = Z.to_nat n -> firstn kw (skipn (Z.to_nat base) src) = xsw ->
  st_facts S D n base c k kw P ->
  xs = firstn k (skipn c xsw) -> length xs = k -> a = wa (D + P) ->
  bytes_at segs (write_to_mem m1 a xs) S src /\
  u8arr segs (write_to_mem m1 a xs) D (upd_bytes bs (Z.to_nat P) xs) /\
  copied src (upd_bytes bs (Z.to_nat P) xs) (Z.to_nat (P + Z.of_nat k)) /\
  mem_inv segs (write_to_mem m1 a xs) /\ munch [(D, D + n)]%Z m0 (write_to_mem m1 a xs) /\
  wmono segs m0 (write_to_mem m1 a xs).
Proof.
  intros segs m0 m1 S D n src kw base xsw c k P bs xs a SRC DST CP MI MU WM LEN HW
         (Hb & Hc & HPb & HP & Hk & SEP & D0 & Dn) Hxs Hl Ha.
  pose proof (proj1 CP) as Lbs.
  assert (SOK : store_ok segs m1 a (length xs) = true).
  { rewrite Hl. eapply mc_store_ok; eauto. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]; eauto; lia. }
  subst a. split; [|split; [|split; [|split; [|split]]]].
  - apply bytes_at_write_other; [exact SRC | lia | lia | rewrite LEN; lia].
  - apply (u8arr_write_bytes segs m1 D bs P xs DST); [lia|]. rewrite Lbs, LEN. lia.
  - apply (f_equal (@length byte)) in CP || idtac.
    rewrite <- Hl. apply copied_updZ; [exact CP | lia | | rewrite LEN; lia].
    rewrite Hl, Hxs. eapply window_sub; eauto; lia.
  - apply mem_inv_store; assumption.
  - apply munch_write; [exact MU | lia | lia |]. cbn [inside]. left. lia.
  - apply wmono_write. exact WM.
Qed.

Ltac ld1 HW c :=
  lazymatch type of HW with firstn ?k (skipn (Z.to_nat ?base) ?src) = ?xs =>
  lazymatch goal with SRC : bytes_at ?segs ?m ?S src |- _ =>
    let i := woff base c in
    let a := cur_mem_addr in
    let RD := fresh "RD" in
    pose proof (mc_read1 segs m S src k base xs c i a _ SRC HW
                  ltac:(unfold ld_facts; lia) ltac:(reflexivity) ltac:(addr_tac)) as RD;
    zstep; try clear RD;
    lazymatch goal with |- evt _ _ ?ms => let ms' := eval cbv beta in ms in change ms with ms' end
  end end.

Ltac ld4 HW c w :=
  lazymatch type of HW with firstn ?k (skipn (Z.to_nat ?base) ?src) = ?xs =>
  lazymatch goal with SRC : bytes_at ?segs ?m ?S src |- _ =>
    let i := woff base c in
    let a := cur_mem_addr in
    let RD := fresh "RD" in let Ew := fresh "E" w in let Lw := fresh "L" w in
    destruct (mc_read4 segs m S src k base xs c i a SRC HW ltac:(reflexivity) ltac:(unfold ld_facts; lia) ltac:(addr_tac))
      as [w [RD [Ew Lw]]];
    cbn [firstn skipn] in Ew;
    zstep; try clear RD
  end end.

Ltac zify_bytes :=
  repeat match goal with
  | |- context [bv_unsigned ?b] =>
      lazymatch type of b with
      | byte => pose proof (byte_range b); generalize dependent (bv_unsigned b); intros
      end
  end.
Ltac solve_le K :=
  repeat match goal with H : ?w = _ :: _ |- _ => is_var w; subst w end;
  first [ apply le4_of_mod32; [reflexivity|] | apply le1_of_mod8 ];
  cbn [map le_val]; rewrite ?unsigned_lit_wrap; rewrite ?lw_unsigned4;
  zify_bytes;
  rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2, ?bv_swrap32_eq, ?bv_wrap32_eq by lia;
  lazymatch K with
  | 0%Z => idtac
  | _ => first [ rewrite (lor_add _ _ K); [ | lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia ]
               | rewrite (lor_add' _ _ K); [ | lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia ] ]
  end;
  Z.div_mod_to_equations; lia.

Ltac by_byte := symmetry; apply le1_zxb.
Ltac by_lw := symmetry; lazymatch goal with |- le4 (sext 64 (bv_extract 0 32 (le_bytes_to_word ?w))) = _ =>
                lazymatch goal with L : length w = 4%nat, E : w = _ |- _ => rewrite (le4_lw w L); exact E end end.

Ltac by_le K :=
  symmetry;
  repeat match goal with H : ?w = _ :: _ |- _ => is_var w; subst w end;
  first
    [ lazymatch goal with
      | |- le4 (Z_to_bv 64 (Z.lor (Z.modulo (bv_swrap 32 (Z.shiftr _ ?k)) _) _)) = _ =>
          lazymatch k with 24%Z => apply merge_a24 | 16%Z => apply merge_a16 | 8%Z => apply merge_a8 end
      | |- le4 (Z_to_bv 64 (Z.lor _ (Z.modulo (bv_swrap 32 (Z.shiftr _ ?k)) _))) = _ =>
          lazymatch k with 24%Z => apply merge_r24 | 16%Z => apply merge_r16 | 8%Z => apply merge_r8 end
      | |- le1 (Z_to_bv 64 (Z.shiftr _ ?k)) = _ =>
          lazymatch k with 8%Z => apply lwb1 | 16%Z => apply lwb2 end
      | |- le1 (sext _ _) = _ => apply lwb0
      end
    | solve_le K ].

Ltac cst_core HW c k bytes_tac SF :=
  lazymatch type of HW with firstn ?kw (skipn (Z.to_nat ?base) ?src) = ?xsw =>
  let xs := eval cbv beta iota delta [firstn skipn] in (firstn k (skipn c xsw)) in
  let kz := eval vm_compute in (Z.of_nat k) in
  lazymatch goal with
  | SRC : bytes_at ?segs ?m ?S src, DST : u8arr ?segs ?m ?D ?bs, CP : copied src ?bs (Z.to_nat ?P),
    MI : mem_inv ?segs ?m, MU : munch _ ?m0 ?m, WM : wmono ?segs ?m0 ?m, LEN : length src = Z.to_nat _
    |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs0) _) =>
     replace bs0 with xs by bytes_tac;
     let SRC' := fresh "SRC" in let DST' := fresh "DST" in let CP' := fresh "CP" in
     let MI' := fresh "MI" in let MU' := fresh "MU" in let WM' := fresh "WM" in
     destruct (mc_store segs m0 m S D _ src kw base xsw c k P bs xs a SRC DST CP MI MU WM LEN HW SF
                 ltac:(reflexivity) ltac:(reflexivity) ltac:(addr_tac))
       as (SRC' & DST' & CP' & MI' & MU' & WM');
     change (Z.of_nat k) with kz in CP';
     clear SRC DST CP MI MU WM SF;
     repeat match goal with
     | H : store_ok segs m _ _ = true |- _ => clear H
     | H : ov_read_bytes segs m _ _ = Some _ |- _ => clear H
     end;
     let m' := fresh "m" in remember (write_to_mem m a xs) as m' eqn:Heqm; clear Heqm; try clear m;
     let bs' := fresh "bs" in remember (upd_bytes bs (Z.to_nat P) xs) as bs' eqn:Heqbs; clear Heqbs; try clear bs;
     rename SRC' into SRC; rename DST' into DST; rename CP' into CP;
     rename MI' into MI; rename MU' into MU; rename WM' into WM
  end end.

Ltac cst HW c k bytes_tac :=
  lazymatch goal with SF : st_facts _ _ _ _ c k _ _ |- _ => cst_core HW c k bytes_tac SF end.

Ltac st HW c k bytes_tac :=
  lazymatch type of HW with firstn ?kw (skipn (Z.to_nat ?base) ?src) = ?xsw =>
  lazymatch goal with
  | SRC : bytes_at ?segs ?m ?S src, DST : u8arr ?segs ?m ?D ?bs, CP : copied src ?bs (Z.to_nat ?P),
    MU : munch [(_, _ + ?n)%Z] _ ?m, LEN : length src = Z.to_nat _ |- _ =>
    let a := cur_mem_addr in
    let SF := fresh "SF" in let SOK := fresh "SOK" in
    assert (SF : st_facts S D n base c k kw P) by (unfold st_facts; lia);
    pose proof (mc_store_ok segs m S D n src kw base xsw c k P bs a DST CP LEN HW SF ltac:(addr_tac)) as SOK;
    zstep; [ cst_core HW c k bytes_tac SF | .. ]
  end end.
Ltac st1 HW c := st HW c 1%nat by_byte.
Ltac st4 HW c := st HW c 4%nat by_lw.

Ltac by_win HW c :=
  lazymatch type of HW with firstn ?k (skipn (Z.to_nat ?base) ?src) = ?xs =>
    first [ rewrite (window_sub src xs base k c 4 _ HW) by lia
          | symmetry; rewrite (window_sub src xs base k c 4 _ HW) by lia ];
    cbn [firstn skipn]; first [ assumption | symmetry; assumption | reflexivity ]
  end.

Ltac cp_norm P' :=
  lazymatch goal with CP : copied ?src ?bs (Z.to_nat ?P) |- _ => replace (Z.to_nat P) with (Z.to_nat P') in CP by lia end.

Definition mc_inv (segs : list MemImageType.Segment) (S D : Z) (src : list byte) (W : list ivl)
    (m0 m1 : word -> option byte) (bs : list byte) (P : Z) : Prop :=
  bytes_at segs m1 S src /\ u8arr segs m1 D bs /\ copied src bs (Z.to_nat P) /\
  mem_inv segs m1 /\ munch W m0 m1 /\ wmono segs m0 m1.

Ltac open_inv H := destruct H as (SRC & DST & CP & MI & MU & WM).

Ltac inv_tac :=
  lazymatch goal with
  | |- mc_inv _ _ _ _ _ _ _ _ _ =>
      split; [eassumption | split; [eassumption | split; [ | repeat split; eassumption ]]];
      lazymatch goal with CP : copied _ _ (Z.to_nat ?P) |- copied _ _ (Z.to_nat ?P') =>
        first [ exact CP | replace (Z.to_nat P') with (Z.to_nat P) by lia; exact CP ] end
  end.

Ltac use_side :=
  first [ inv_tac | idtac ]; try assumption; try (f_equal; lia); try lia;
  try (rewrite ?unsigned_lit by lia; Z.div_mod_to_equations; lia);
  try (rewrite ?Z.add_0_r, ?Z.sub_0_r; symmetry; apply Z_to_bv_bv_unsigned).
Tactic Notation "use" uconstr(L) := eapply L; use_side.

Ltac finish2 :=
  apply evt_done;
  lazymatch goal with |- ?P ?ms => try unfold P | _ => idtac end;
  hnf;
  repeat (lazymatch goal with |- ex _ => eexists end);
  lazymatch goal with
  | |- _ = _ /\ _ => split; [ cbv delta [mkR]; reflexivity | ]
  | |- _ = _ => cbv delta [mkR]; reflexivity
  end;
  repeat match goal with |- _ /\ _ => split end; try assumption.

Ltac mc_fin :=
  lazymatch goal with
  | DST : u8arr _ ?m1 _ ?bs, CP : copied ?src ?bs (Z.to_nat ?P), L : length ?src = _ |- _ =>
      let E := fresh "E" in
      pose proof (copied_all _ _ _ CP ltac:(lia)) as E; rewrite E in DST; clear E CP;
      apply rw_cells_of_u8arr in DST; rewrite L in DST
  end;
  finish2.

Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
           change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).
Ltac lstep := zstep; fix_lit_store.
