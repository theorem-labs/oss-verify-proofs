(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require RefU0Gc5. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import STRW_merge.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import StoreDj.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes03nat37Corelib7Numbers7BinNumshd1Z37Corelib4Init5Logicja3andja2eq37Corelib4Init3Natl93add37Corelib4Init5Peanon12le46Stdlib6ZArith6BinInt1Zoa3addoa2leoa6of_nathd4Npos35stdpp9bitvectorbdefinitionsrd2bv04list06option04Some04cons03nil37Corelib5Lists7ListDefve6firstnve5skipn3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypehi67Segment3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshm6dov_read_bytes79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~hqe8bytes_athqe2wa79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU8STRW_tac~~~~~~hva8ld_facts36Stdlib5Lists4Listik69nth_erroroa6to_nat06lengthja2exja2oroa3pow04bool04truehm68store_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~ipf5u8arrhva8st_facts79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6StrFun~~~~~~iue6copiedhm6cwrite_to_mem04prod04pair79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~jl25munchjl25wmonohqe7mem_invhqe9upd_bytesjl23ivl" s.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac reg_val r :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let p := eval vm_compute in (bv_key (Z_to_bv 5 r)) in
    eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end)
  end.

(* [comment removed for export] *)
Ltac name_list xs L :=
  lazymatch type of L with
  | length _ = O => destruct xs; [clear L | cbn in L; discriminate]
  | length _ = S _ => let x := fresh "x" in let xs' := fresh "xs" in
      destruct xs as [|x xs']; [cbn in L; discriminate | cbn in L; apply Nat.succ_inj in L; name_list xs' L]
  end.

(* [comment removed for export] *)
Ltac window base k HW :=
  lazymatch goal with SRC : bytes_at ?segs ?m ?S ?src |- _ =>
    let xs := fresh "xs" in let L := fresh "L" in
    destruct (window_ex src base k ltac:(lia)) as [xs [HW L]]; name_list xs L
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac woff base c :=
  let cz := eval vm_compute in (Z.of_nat c) in
  lazymatch cz with 0%Z => base | _ => constr:((base + cz)%Z) end.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Ltac addr_tac :=
  unfold wa;
  first [ reflexivity
        | f_equal; lia
        | lazymatch goal with |- ?v = Z_to_bv 64 ?e =>
            replace e with (bv_unsigned v) by lia; symmetry; apply Z_to_bv_bv_unsigned end ].

(* [comment removed for export] *)
Definition ld_facts : ltac2:(zQ "20!h8!j6>4base$1>1c$0>1j$0>2kw$0>1i$1P") := ltac2:(zQ "90!h8!j6!ke!l4!mb!o5!q2!q8!qd\4base$1\1c$0\1j$0\2kw$0\1i$1@2$2@2$7Z^5@2$2@2$5@2$4^4^3^2@3$3$1^1@2$6^5@1$8^4").

Lemma mc_read1 : ltac2:(zQ "h40!r6!ta!tf!l4!u5!j6!ud!h8!v3!v9!hh5!hhe!hlb!hpd!hu8!hv4!ija!il9!q2!im6>4segs@1$2$c>1m>0@1$1@1$0#k0@1$4@1$1@1$0#8>1S$5>3src@1$2@1$1@1$0#8>2kw$7>4base$5>3xsw@1$2@1$1@1$0#8>1c$7>1i$5>1a@1$1@1$0#k0>1b@1$1@1$0#8>0@4$e^b^a^9^8>0@3$3@1$2@1$1@1$0#8@3$a@1$1@1$0#8^8@3$b@1$1@1$0#8@1$h3^7^9^6>0@5$h0^8^6N1^9^5>0@3$3@1$4@1$1@1$0#8@3$h1@1$1@1$0#8^8^7@2$6@1$1@1$0#8^4>0@3$3@1$1@1$0#k0^6@1$f@2$h2^d^7@3$3@1$4@1$2@1$1@1$0#8@4$d^h0^f^7N1@2$6@1$2@1$1@1$0#8@3$8@1$1@1$0#8^6@1$9@1$1@1$0#8").
Proof.
  (intros segs m S src kw base xsw c i a b SRC HW nd_i1 Hn Ha; ndestruct nd_i1 as (Hb & Hc & Hi)).
  eapply (u8ro_read segs m S src i b a SRC); [ | lia | exact Ha ].
  rewrite <- Hn. eapply window_nth; eauto; lia.
Qed.

Lemma mc_read4 : ltac2:(zQ "h40!r6!ta!tf!l4!h8!j6!imf!u5!ke!hh5!hhe!ud!in7!hlb!hpd!hu8!hv4!ija!q2!im6>4segs@1$2$d>1m>0@1$1@1$0#k0@1$7@1$1@1$0#8>1S$5>3src@1$2@1$1@1$0#8>2kw$4>4base$5>3xsw@1$2@1$1@1$0#8>1c$4>1i$5>1a@1$1@1$0#k0>0@4$f^a^9^8^7>0@3$3@1$2@1$1@1$0#8@3$9@1$1@1$0#8^7@3$a@1$1@1$0#8@1$h3^6^8^5>0@3$3$4@2$6@1$1@1$0#8^6^8>0@5$h1^8^6N4^9^5>0@3$3@1$1@1$0#k0^5@1$h0@2$h2^c^6@2$c@1$2@1$1@1$0#8\1w@1$2@1$1@1$0#8@2$8@3$3@1$7@1$2@1$1@1$0#8@4$e^h0^f^7N4@2$b@1$2@1$1@1$0#8^1@2$8@3$3@1$2@1$1@1$0#8^1@3$9@1$1@1$0#8N4@3$a@1$1@1$0#8^9^a@3$3$4@2$6@1$1@1$0#8^1N4").
Proof.
  (intros segs m S src kw base xsw c i a SRC HW HL nd_i2 ->; ndestruct nd_i2 as (Hb & Hc & Hi)).
  assert (L : (Z.to_nat base + kw <= length src)%nat).
  { apply (f_equal (@length byte)) in HW. rewrite length_firstn, length_skipn, HL in HW. lia. }
  exists (firstn 4 (skipn (Z.to_nat i) src)). split; [|split].
  - apply (bytes_at_read segs m S src i 4 SRC); lia.
  - eapply window_sub; eauto; lia.
  - rewrite length_firstn, length_skipn. lia.
Qed.

Definition st_facts : ltac2:(zQ "20!j6!h8>1S$0>1D$0>1n$0>4base$0>1c$1>1k$1>2kw$1>1P$0P") := ltac2:(zQ "b0!ke!q8!j6!q2!h8!qd!l4!inc!mb!o5!io1\1S$2\1D$2\1n$2\4base$2\1c$4\1k$4\2kw$4\1P$2@2$0@2$1Z^5@2$0@2$9@2$8^4^3^2@2$0@3$6$2^1@2$3^5@1$5^4@2$0@2$1Z^1@2$0@2$1@2$3^1@1$5^3^6@2$0@2$7@2$1@2$3^8^6^7@2$1@2$3^7^6^8@2$0@2$1Z^7@2$1@2$3^7^6@2$a+2+k0").

Lemma mc_store_ok : ltac2:(zQ "h40!r6!ta!tf!j6!h8!l4!im6!io7!imf!u5!iod!hh5!hhe!hlb!ip3!it9!hv4!iu2!jic!q2>4segs@1$2$d>2m1>0@1$1@1$0#k0@1$9@1$1@1$0#8>1S$3>1D$3>1n$3>3src@1$2@1$1@1$0#8>2kw$4>4base$3>3xsw@1$2@1$1@1$0#8>1c$4>1k$4>1P$3>2bs@1$2@1$1@1$0#8>1a@1$1@1$0#k0>0@4$f^e^d^b^2>0@3$h2^a^3@1$6^4>0@3$5$4@2$8@1$1@1$0#8^b@1$6^c>0@3$5@1$2@1$1@1$0#8@3$b@1$1@1$0#8^b@3$c@1$1@1$0#8@1$6^a^c^9>0@8$h1^h0^f^e^b^9^8^c^7>0@3$5@1$1@1$0#k0^6@1$h0@2$h3^h0^8@3$5$7@4$e^h4^h3^7^a$a").
Proof.
  (intros segs m1 S D n src kw base xsw c k P bs a DST [L _] LEN _ nd_i3 Ha; ndestruct nd_i3 as (_ & _ & _ & HP & Hk & _)).
  eapply (u8arr_store_ok_n segs m1 D bs P k a DST); [lia | | exact Ha]. rewrite L, LEN. lia.
Qed.

Lemma mc_store : ltac2:(zQ "hd1!r6!ta!j6!tf!im6!h8!ke!l4!jj6!jk6!q2!v3!imf!v9!u5!jkc!hh5!hhe!it9!joe!jp7!hu8!jq0!jqb!jic!hlb!hv4!iu2!qd&>0@1$1@1$0#k0@1$e@1$1@1$0#8>4segs@1$3$h9>2m0~0>2m1~0>1S$2>1D$2>1n$2>3src@1$3@1$1@1$0#8>2kw$5>4base$2>3xsw@1$3@1$1@1$0#8>1c$5>1k$5>1P$2>2bs@1$3@1$1@1$0#8>2xs@1$3@1$1@1$0#8>1a@1$1@1$0#k0>0@4$h5^h0^e^d^a>0@4$h2^h1^f^d^4>0@3$h8^c^5@1$4^6>0@2$h6^h3^h1>0@3$h3@3$b@2$9$2$2@4$f$2$2^h0@2$a^h0^f@1$d@2$9$2$2^h3^h2>0@3$h4^h5^h4^h3>0@3$7$5@2$c@1$1@1$0#8^h0@1$4^h1>0@3$7@1$3@1$1@1$0#8@3$h0@1$1@1$0#8^h0@3$h1@1$1@1$0#8@1$4^f^h1^e>0@8$hb^h5^h4^h3^h0^e^d^h1^c>0@3$7@1$3@1$1@1$0#8^b@3$h0@1$1@1$0#8^e@3$h1@1$1@1$0#8^f^h0>0@3$7$5@2$c@1$1@1$0#8^c^f>0@3$7@1$1@1$0#k0^c@1$ha@2$a^h7^f@2$6@4$h5^hc@3$8^ha^d^e^h9^h6@2$6@4$h2^hc@3$8^ha^d^e^h8@3$h7^f@1$4^h0^e@2$6@3$h8^h6@3$h7^f@1$4^h0^e@1$4@2$a^h0@1$hc^h1@2$6@2$h6^hc@3$8^ha^d^e@2$6@3$h3@3$b@2$9$2$2@4$f$2$2^h8@2$a^h8^h7@1$d@2$9$2$2^hb@3$8^ha^d^e@3$h4^hc^hb@3$8^ha^d^e").
Proof.
  (intros segs m0 m1 S D n src kw base xsw c k P bs xs a SRC DST CP MI MU WM LEN HW nd_i4 Hxs Hl Ha; ndestruct nd_i4 as (Hb & Hc & HPb & HP & Hk & SEP & D0 & Dn)).
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Ltac by_byte := symmetry; apply le1_zxb.
Ltac by_lw := symmetry; lazymatch goal with |- le4 (sext 64 (bv_extract 0 32 (le_bytes_to_word ?w))) = _ =>
                lazymatch goal with L : length w = 4%nat, E : w = _ |- _ => rewrite (le4_lw w L); exact E end end.
(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Ltac by_win HW c :=
  lazymatch type of HW with firstn ?k (skipn (Z.to_nat ?base) ?src) = ?xs =>
    first [ rewrite (window_sub src xs base k c 4 _ HW) by lia
          | symmetry; rewrite (window_sub src xs base k c 4 _ HW) by lia ];
    cbn [firstn skipn]; first [ assumption | symmetry; assumption | reflexivity ]
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mc_inv : ltac2:(zQ "71!r6!ta!tf!j6!u5!hlb!jr8&>0@1$1@1$0#k0@1$4@1$1@1$0#8>4segs@1$2$5>1S$3>1D$3>3src@1$2@1$1@1$0#8>1W@1$2$6>2m0~0>2m1~0>2bs@1$2@1$1@1$0#8>1P$3P") := ltac2:(zQ "f1!r6!ta!ke!tf!j6!u5!hlb!it9!jr8!joe!jp7!hu8!jq0!jic!im6&>0@1$1@1$0#k0@1$5@1$1@1$0#8\4segs@1$3$6\1S$4\1D$4\3src@1$3@1$1@1$0#8\1W@1$3$8\2m0~0\2m1~0\2bs@1$3@1$1@1$0#8\1P$4@2$2@4$b^9^3^8^6@2$2@4$7^9^3^7^2@2$2@3$d^6^2@1$e^1@2$2@2$c^9^3@2$2@3$9^5^4^3@3$a^9^4^3").

Ltac open_inv H := destruct H as (SRC & DST & CP & MI & MU & WM).

(* [comment removed for export] *)
Ltac inv_tac :=
  lazymatch goal with
  | |- mc_inv _ _ _ _ _ _ _ _ _ =>
      split; [eassumption | split; [eassumption | split; [ | repeat split; eassumption ]]];
      lazymatch goal with CP : copied _ _ (Z.to_nat ?P) |- copied _ _ (Z.to_nat ?P') =>
        first [ exact CP | replace (Z.to_nat P') with (Z.to_nat P) by lia; exact CP ] end
  end.

(* [comment removed for export] *)
Ltac use_side :=
  first [ inv_tac | idtac ]; try assumption; try (f_equal; lia); try lia;
  try (rewrite ?unsigned_lit by lia; Z.div_mod_to_equations; lia);
  try (rewrite ?Z.add_0_r, ?Z.sub_0_r; symmetry; apply Z_to_bv_bv_unsigned).
Tactic Notation "use" uconstr(L) := eapply L; use_side.

(* [comment removed for export] *)
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

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
