(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep CellsX TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AsConst AsIface CXXRep.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z46Stdlib6ZArith6BinInt1Zhc3addhc3mul37Corelib4Init9Datatypesk04bool79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJA5BJRep~~~~~~lfcBJ_SMALL_OBJhc3lebk04list04Npos35stdpp9bitvectorbdefinitionsrd2bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~tf4cellk04constf2C8k03niltf2C1tf2CB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~hje2b8hje2wz79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AsIface~~~~~~ho53memlf2jv37Corelib4Init5Logichse3andk06lengthk03nathse2eqhse2ex79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~ig45asegs89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJA5BJRep3HCW~~~~~~ik85vdeepik84vhdr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~ip98rw_cellsho55blockik85kdeepik84khdrik86vsitemik89item_deepik88item_hdrlf8blocks_vlf7jheightk05falsek04true37Corelib4Init3Natjk13mulik86ideepsik85ihdrsik86vstackk04prodho54bptrk06optionik86vs_bufik88vs_beginik84vs_ntf2C4lfaBJ_DR_VTBLik8eBJ_ERRCAT_VTBLlfcBJ_ARR_EMPTYlfbBJ_DO_ALLOClfdBJ_DO_DEALLOClfaBJ_DO_ISEQlf8BJ_DR_D0lf8BJ_DR_D1lfbBJ_INSTANCElfcBJ_OBJ_EMPTYik89BJ_ERRCATik8cBJ_ERRCAT_IDik8cBJ_FAILED_FNlfcblocks_itemslf6vsitemk03app" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition BJ_INSTANCE   : Z := 0x1b9da0.   (* [comment removed for export] *)
Definition BJ_DR_VTBL    : Z := 0x1adcf0.   (* [comment removed for export] *)
Definition BJ_DR_D1      : Z := 0xf5958.
Definition BJ_DR_D0      : Z := 0xf595c.
Definition BJ_DO_ALLOC   : Z := 0xf5964.   (* [comment removed for export] *)
Definition BJ_DO_DEALLOC : Z := 0xf596c.   (* [comment removed for export] *)
Definition BJ_DO_ISEQ    : Z := 0xf5974.
Definition BJ_ARR_EMPTY  : Z := 0x6f28c0.  (* [comment removed for export] *)
Definition BJ_OBJ_EMPTY  : Z := 0x6f28e0.  (* [comment removed for export] *)
Definition BJ_KVP_EMPTY  : Z := 0x26fc0.   (* [comment removed for export] *)
Definition BJ_SMALL_OBJ  : Z := 18.        (* [comment removed for export] *)

Definition KIND_STRING : Z := 5.
Definition KIND_ARRAY  : Z := 6.
Definition KIND_OBJECT : Z := 7.
Definition KIND_SSTR   : Z := 133.  (* [comment removed for export] *)
Definition KIND_KEY    : Z := 69.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive jv : Type :=
| Jsca  (k : Z)                                   (* [comment removed for export] *)
| Jsstr (n : Z)                                   (* [comment removed for export] *)
| Jlstr (b : block) (n : Z)                       (* [comment removed for export] *)
| Jarr  (t : option block) (cap : Z) (es : jvs)   (* [comment removed for export] *)
| Jobj  (t : option block) (cap : Z) (ss : kvs)   (* [comment removed for export] *)
with jvs : Type :=
| JVnil : jvs
| JVcons : jv -> jvs -> jvs
with kvs : Type :=
| KVnil : kvs
| KVcons : block -> jv -> kvs -> kvs.             (* [comment removed for export] *)

Scheme jv_mind := Induction for jv Sort Prop
  with jvs_mind := Induction for jvs Sort Prop
  with kvs_mind := Induction for kvs Sort Prop.
Combined Scheme jv_mutind from jv_mind, jvs_mind, kvs_mind.

Fixpoint jvs_len (l : jvs) : nat := match l with JVnil => O | JVcons _ r => S (jvs_len r) end.
Fixpoint kvs_len (l : kvs) : nat := match l with KVnil => O | KVcons _ _ r => S (kvs_len r) end.
Fixpoint jvs_of_list (l : list jv) : jvs := match l with [] => JVnil | v :: r => JVcons v (jvs_of_list r) end.
Fixpoint list_of_jvs (l : jvs) : list jv := match l with JVnil => [] | JVcons v r => v :: list_of_jvs r end.

(* [comment removed for export] *)
Fixpoint jheight (v : jv) : nat :=
  match v with
  | Jsca _ | Jsstr _ | Jlstr _ _ => 1
  | Jarr _ _ es => S (jvs_height es)
  | Jobj _ _ ss => S (kvs_height ss)
  end
with jvs_height (l : jvs) : nat :=
  match l with JVnil => O | JVcons v r => Nat.max (jheight v) (jvs_height r) end
with kvs_height (l : kvs) : nat :=
  match l with KVnil => O | KVcons _ v r => Nat.max (jheight v) (kvs_height r) end.

(* [comment removed for export] *)
Fixpoint blocks_v (v : jv) : list block :=
  match v with
  | Jsca _ | Jsstr _ => []
  | Jlstr b _ => [b]
  | Jarr t _ es => match t with Some b => [b] | None => [] end ++ blocks_jvs es
  | Jobj t _ ss => match t with Some b => [b] | None => [] end ++ blocks_kvs ss
  end
with blocks_jvs (l : jvs) : list block :=
  match l with JVnil => [] | JVcons v r => blocks_v v ++ blocks_jvs r end
with blocks_kvs (l : kvs) : list block :=
  match l with KVnil => [] | KVcons k v r => k :: blocks_v v ++ blocks_kvs r end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition arr_tbl_size : ltac2:(zQ "10!h9>3cap$0$0") := ltac2:(zQ "30!h9!j4!ja\3cap$0@2$1+8@2$2+h8^1").
Definition obj_tbl_size : ltac2:(zQ "10!h9>3cap$0$0") := ltac2:(zQ "60!l8!h9!j4!ja!pb!qa\3cap$1M0\0$0$1@2$5^1$4@2$2+h0@2$3+i8^1@2$2+h0@2$3+ic^1").
Definition lstr_tbl_size : ltac2:(zQ "10!h9>3cap$0$0") := ltac2:(zQ "20!h9!j4\3cap$0@2$1^1+9").

(* [comment removed for export] *)
Definition val_hdr : ltac2:(zQ "50!r0!r7!ta!h9!hhb>4kind$3>5junk7@1$0@1$2@1$1#8>1w@1$2@1$1#k0@1$0$4") := ltac2:(zQ "c0!hhb!hi2!r7!hi9!ta!r0!hie!h9!hj4!hj9!hn9!hnf\4kind$7\5junk7@1$5@1$4@1$2#8\1w@1$4@1$2#k0@3$1$0@1$3@1$bZ@3$1$0@1$8@1$a^3@3$1$0@2$9N7^2@3$1$0@1$3^1@1$6$0").

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint vhdr (v : jv) (hb : list byte) {struct v} : Prop :=
  match v with
  | Jsca k => 0 <= k <= 4 /\ exists junk7 pay, length junk7 = 7%nat /\ length pay = 8%nat /\
              hb = cells_bytes [C8 (wz 0); C1 (b8 k); CB 7 junk7; CB 8 pay]   (* [comment removed for export] *)
  | Jsstr n => 0 <= n <= 14 /\ exists bs, length bs = 14%nat /\
               hb = cells_bytes [C8 (wz 0); C1 (b8 KIND_SSTR); CB 14 bs; C1 (b8 (14 - n))]
  | Jlstr (p, T, sz) n => exists junk7, length junk7 = 7%nat /\ hb = cells_bytes (val_hdr KIND_STRING junk7 (wz T))
  | Jarr None cap es => cap = 0 /\ es = JVnil /\ exists junk7, length junk7 = 7%nat /\ hb = cells_bytes (val_hdr KIND_ARRAY junk7 (wz BJ_ARR_EMPTY))
  | Jarr (Some (p, T, sz)) cap es => exists junk7, length junk7 = 7%nat /\ hb = cells_bytes (val_hdr KIND_ARRAY junk7 (wz T))
  | Jobj None cap ss => cap = 0 /\ ss = KVnil /\ exists junk7, length junk7 = 7%nat /\ hb = cells_bytes (val_hdr KIND_OBJECT junk7 (wz BJ_OBJ_EMPTY))
  | Jobj (Some (p, T, sz)) cap ss => exists junk7, length junk7 = 7%nat /\ hb = cells_bytes (val_hdr KIND_OBJECT junk7 (wz T))
  end.

(* [comment removed for export] *)
Fixpoint vhdrs (l : jvs) (bs : list byte) {struct l} : Prop :=
  match l with
  | JVnil => bs = []
  | JVcons v r => exists hb rest, bs = hb ++ rest /\ length hb = 24%nat /\ vhdr v hb /\ vhdrs r rest
  end.
Fixpoint shdrs (l : kvs) (bs : list byte) {struct l} : Prop :=
  match l with
  | KVnil => bs = []
  | KVcons (p, K, ksz) v r => exists hb (nx : word) j4 rest,
      bs = hb ++ cells_bytes [C8 (wz K); C4 (wz (ksz - 1)); CB 4 j4] ++ rest /\ length hb = 24%nat /\ length j4 = 4%nat /\
      vhdr v hb /\ shdrs r rest
  end.

(* [comment removed for export] *)
Fixpoint vdeep (m : mem) (v : jv) {struct v} : Prop :=
  match v with
  | Jsca _ | Jsstr _ => True
  | Jlstr (p, T, sz) n =>
      exists cap junk, sz = lstr_tbl_size cap /\ 0 <= n <= cap /\ 30 <= cap < 2^31 - 1 /\ rblock_range T sz /\ addressable m T sz /\   (* [comment removed for export] *)
      rw_cells asegs m T [C4 (wz n); C4 (wz cap); CB (Z.to_nat (cap + 1)) junk]
  | Jarr None _ _ => True
  | Jarr (Some (p, T, sz)) cap es =>
      exists ebs junk, sz = arr_tbl_size cap /\ 1 <= Z.of_nat (jvs_len es) <= cap /\ cap < 2^31 - 1 /\ rblock_range T sz /\ addressable m T sz /\   (* [comment removed for export] *)
      rw_cells asegs m T [C4 (wz (Z.of_nat (jvs_len es))); C4 (wz cap);
                          CB (24 * jvs_len es)%nat ebs; CB (Z.to_nat (24 * (cap - Z.of_nat (jvs_len es)))) junk] /\
      vhdrs es ebs /\ vdeeps m es
  | Jobj None _ _ => True
  | Jobj (Some (p, T, sz)) cap ss =>
      exists salt sbs junk jbk, sz = obj_tbl_size cap /\ 1 <= Z.of_nat (kvs_len ss) <= cap /\ cap < 2^31 - 1 /\ rblock_range T sz /\ addressable m T sz /\   (* [comment removed for export] *)
      rw_cells asegs m T [C4 (wz (Z.of_nat (kvs_len ss))); C4 (wz cap); C8 salt;
                          CB (40 * kvs_len ss)%nat sbs; CB (Z.to_nat (40 * (cap - Z.of_nat (kvs_len ss)))) junk] /\
      (BJ_SMALL_OBJ < cap -> rw_cells asegs m (T + 16 + 40 * cap) [CB (Z.to_nat (4 * cap)) jbk]) /\
      shdrs ss sbs /\ sdeeps m ss
  end
with vdeeps (m : mem) (l : jvs) {struct l} : Prop :=
  match l with JVnil => True | JVcons v r => vdeep m v /\ vdeeps m r end
with sdeeps (m : mem) (l : kvs) {struct l} : Prop :=
  match l with
  | KVnil => True
  | KVcons (p, K, ksz) v r =>
      (1 <= ksz < 2^31 /\ rblock_range K ksz /\ addressable m K ksz /\ exists kb, rw_cells asegs m K [CB (Z.to_nat ksz) kb]) /\ vdeep m v /\ sdeeps m r   (* [comment removed for export] *)
  end.

(* [comment removed for export] *)
Definition val_at : ltac2:(zQ "30!h9!hs2!hs9>1m$1>1a$0>1v$2P") := ltac2:(zQ "h30!hu2!r7!ta!r0!hhb!hi2!hu9!hv2!hie!hv8!hve!h9!ijf!hs2!io8!ip1!hs9!hj9!it4\1m$d\1a$b\1v$h0@2$a@1$3@1$2@1$1#8\2hb@1$3@1$2@1$1#8@2$0@3$9$7@2$6@1$2@1$1#8^1Nh8@2$0@4$h2$c^4^3@3$5$4@2$h1Nh8^1@1$8$4@2$0@2$f^2^1@2$e^4^2").

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition khdr (b : block) (hb : list byte) : Prop :=
  let '(p, K, ksz) := b in
  exists junk3, length junk3 = 3%nat /\ hb = cells_bytes [C8 (wz 0); C1 (b8 KIND_KEY); CB 3 junk3; C4 (wz (ksz - 1)); C8 (wz K)].
Definition kdeep (m : mem) (b : block) : Prop :=
  let '(p, K, ksz) := b in
  1 <= ksz < 2^31 /\ rblock_range K ksz /\ addressable m K ksz /\ exists kb, rw_cells asegs m K [CB (Z.to_nat ksz) kb].   (* [comment removed for export] *)
Definition key_at : ltac2:(zQ "30!h9!iu0!hs2>1m$2>1a$0>1b$1P") := ltac2:(zQ "h30!hu2!r7!ta!r0!hhb!hi2!hu9!hv2!hie!hv8!hve!h9!ijf!iu0!hs2!iu9!iv2!hj9!it4\1m$e\1a$b\1b$d@2$a@1$3@1$2@1$1#8\2hb@1$3@1$2@1$1#8@2$0@3$9$7@2$6@1$2@1$1#8^1Nh8@2$0@4$h2$c^4^3@3$5$4@2$h1Nh8^1@1$8$4@2$0@2$h0^2^1@2$f^4^2").

(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive vsitem : Type := VSval (v : jv) | VSkey (b : block).

Definition item_hdr : ltac2:(zQ "40!r0!r7!iva!ta>2it$2>2hb@1$0@1$3@1$1#8P") := ltac2:(zQ "80!iva!r0!r7!iu0!iv2!ip1!hs9!ta\2it$0\2hb@1$1@1$7@1$2#8M0\2it$0P^2\1v$6@2$5^1^2\1b$3@2$4^1^2").
Definition item_deep : ltac2:(zQ "20!hs2!iva>1m$0>2it$1P") := ltac2:(zQ "60!iva!iu0!hs2!iu9!io8!hs9\1m$2\2it$0M0\2it$0P^1\1v$5@2$4^3^1\1b$1@2$3^3^1").
Definition item_at : ltac2:(zQ "30!h9!hs2!iva>1m$1>1a$0>2it$2P") := ltac2:(zQ "h30!hu2!r7!ta!r0!hhb!hi2!hu9!hv2!hie!hv8!hve!h9!ijf!hs2!jg4!jh1!iva!hj9!it4\1m$d\1a$b\2it$h0@2$a@1$3@1$2@1$1#8\2hb@1$3@1$2@1$1#8@2$0@3$9$7@2$6@1$2@1$1#8^1Nh8@2$0@4$h2$c^4^3@3$5$4@2$h1Nh8^1@1$8$4@2$0@2$f^2^1@2$e^4^2").
Definition blocks_item : ltac2:(zQ "30!r0!iu0!iva>2it$2@1$0$1") := ltac2:(zQ "70!iu0!iva!hi2!r0!hie!jhd!hs9\2it$1M1\2it$1@1$3$0^1\1v$6@1$5^1\1b$0@3$2$0^1@1$4$0").
Definition item_height : ltac2:(zQ "20!hv2!iva>2it$1$0") := ltac2:(zQ "50!iva!hv2!iu0!ji8!hs9\2it$0M0\2it$0$1^1\1v$4@1$3^1\1b$2N1").
Definition is_val : ltac2:(zQ "20!l8!iva>2it$1$0") := ltac2:(zQ "60!iva!l8!jj2!jja!iu0!hs9\2it$0M0\2it$0$1^1\1v$5$3\1b$4$2").

Fixpoint ihdrs (l : list vsitem) (bs : list byte) : Prop :=
  match l with
  | [] => bs = []
  | it :: r => exists hb rest, bs = hb ++ rest /\ length hb = 24%nat /\ item_hdr it hb /\ ihdrs r rest
  end.
Fixpoint ideeps (m : mem) (l : list vsitem) : Prop :=
  match l with [] => True | it :: r => item_deep m it /\ ideeps m r end.
(* [comment removed for export] *)
Definition items_at : ltac2:(zQ "40!r0!h9!hs2!iva>1m$2>1a$1>1l@1$0$3P") := ltac2:(zQ "h20!r0!hu2!r7!iva!hhb!ta!hi2!hu9!hie!hve!jl3!h9!ijf!hs2!jla!jm4!hj9!it4\1m$d\1a$b\1l@1$0$3@2$9@1$0@1$5@1$2#8\2bs@1$0@1$5@1$2#8@2$1@4$h1$c^4^3@3$6$4@2$h0@2$aNh8@2$7$3^2^1@1$8$4@2$1@2$f^2^1@2$e^4^2").
Fixpoint blocks_items (l : list vsitem) : list block :=
  match l with [] => [] | it :: r => blocks_item it ++ blocks_items r end.

(* [comment removed for export] *)
Record vstack := mkVS {
  vs_buf   : option block ;   (* [comment removed for export] *)
  vs_cap   : Z ;              (* [comment removed for export] *)
  vs_items : list vsitem ;
  vs_chars : Z ;              (* [comment removed for export] *)
  vs_temp  : Z                (* [comment removed for export] *)
}.

Definition vs_n (st : vstack) : Z := Z.of_nat (length (vs_items st)).
Definition vs_begin : ltac2:(zQ "20!h9!jmd>2st$1$0") := ltac2:(zQ "70!h9!jn7!jne!jo6!iu0!jof!jmd\2st$6M3\1x@1$3$4$0@1$5^1\1b$4M1\1b@2$1@2$1$2$0$0$0^1\1p@2$1$2$0\1z$0M1\1p@2$1$2$0$0^2\2b0$2\1B$0^1Z").
Definition vs_top : ltac2:(zQ "20!h9!jmd>2st$1$0") := ltac2:(zQ "50!jp9!jq5!jmd!j4!ja\2st$2@2$3@1$0^1@2$4+h8@1$1^1").
Definition vs_end (st : vstack) : Z := vs_begin st + 24 * vs_cap st.
Definition blocks_vs (st : vstack) : list block :=
  match vs_buf st with None => [] | Some b => [b] end ++ blocks_items (vs_items st).

(* [comment removed for export] *)
Definition vs_hdr (st : vstack) (junk7 : list byte) : list cell :=
  [C8 (wz 0); C8 (wz (vs_temp st)); C8 (wz (vs_begin st)); C8 (wz (vs_top st)); C8 (wz (vs_end st));
   C8 (wz (vs_chars st)); C1 (b8 1); CB 7 junk7; C8 (wz 0)].

Definition vs_at (m : mem) (a : Z) (st : vstack) : Prop :=
  0 <= vs_chars st /\
  (exists junk7, rw_cells asegs m a (vs_hdr st junk7)) /\
  match vs_buf st with
  | None => vs_cap st = 0 /\ vs_items st = [] /\ vs_chars st = 0
  | Some (p, B, sz) =>
      sz = 24 * vs_cap st /\ 16 <= vs_cap st /\ vs_n st <= vs_cap st /\ 24 * vs_cap st < 2^32 /\
      rblock_range B sz /\ B <> vs_temp st /\ addressable m B sz /\   (* [comment removed for export] *)
      items_at m B (vs_items st) /\
      (* [comment removed for export] *)
      (0 < vs_chars st -> 24 * (vs_n st + 1) + vs_chars st <= 24 * vs_cap st) /\
      (* [comment removed for export] *)
      (exists junk, rw_cells asegs m (vs_top st) [CB (Z.to_nat (24 * (vs_cap st - vs_n st))) junk])
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition BJ_ERRCAT      : Z := 0x1b9ce0.  (* [comment removed for export] *)
Definition BJ_ERRCAT_VTBL : Z := 0x1ad8b0.  (* [comment removed for export] *)
Definition BJ_FAILED_FN   : Z := 0xf6dc8.
Definition BJ_ERRCAT_ID   : Z := 0xb9a9b9922177c772.  (* [comment removed for export] *)

Definition bj_statics : ltac2:(zQ "10!hs2>1m$0P") := ltac2:(zQ "hb0!hhb!hi2!hnf!hi9!hie!ijf!it4!hu2!jqd!r7!jr2!jrf!ta!hve!hs2!jt1!ju0!jue!jve!kgb!kh6!ki1!kif!kje!kkb!klb!j4\1m$e@2$7@4$6$5^1$h5@3$1$0@1$3@1$2$a@1$4$0@2$7@4$6$5^1$a@3$1$0@1$3@1$2$h4@3$1$0@1$3@1$2$h3@3$1$0@1$3@1$2$h0@3$1$0@1$3@1$2$h1@3$1$0@1$3@1$2$h2@1$4$0@2$7@4$6$5^1$f@3$1$0@1$8@1$2Z@3$1$0@1$8@1$2Z@1$4$0@2$7@2$d@1$c@1$9#k0\4salt@1$c@1$9#k0@4$6$5^2$h6@3$1$0@1$8@1$2Z@3$1$0@1$8@1$2Z@3$1$0@1$3^1@1$4$0@2$7@4$6$5^1$h7@3$1$0@1$3@1$2$b@3$1$0@1$3@1$2$h8@1$4$0@4$6$5^1@2$ha$b+j0@3$1$0@1$3@1$2$h9@1$4$0").
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Record pstate := mkPS {
  ps_vs     : vstack ;   (* [comment removed for export] *)
  ps_end    : Z ;        (* [comment removed for export] *)
  ps_depth  : Z ;        (* [comment removed for export] *)
  ps_ecset  : bool ;     (* [comment removed for export] *)
  ps_more   : bool ;     (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition parser_at (m : mem) (a : Z) (ps : pstate) : Prop :=
     vs_at m a (ps_vs ps)
  /\ (exists num : list byte, length num = 24%nat /\ rw_cells asegs m (a + 64) [CB 24 num])
  /\ (exists (ecval eccat lcf : word),
        rw_cells asegs m (a + 88) [C8 ecval; C8 eccat; C8 lcf] /\
        (ps_ecset ps = false <-> lcf = wz 0) /\ bv_unsigned lcf <> 1)
     (* [comment removed for export] *)
  /\ rw_cells asegs m (a + 112) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)]
  /\ (exists scratch : list byte, length scratch = 16%nat /\ rw_cells asegs m (a + 160) [CB 16 scratch])
  /\ (exists done clean pad5, (length pad5 = 5%nat /\ bv_unsigned done <= 1 /\ bv_unsigned clean <= 1) /\   (* [comment removed for export] *)
        rw_cells asegs m (a + 176) [C1 (b8 (if ps_more ps then 1 else 0)); C1 done; C1 clean; CB 5 pad5])
  /\ rw_cells asegs m (a + 184) [C8 (wz (ps_end ps))]
  /\ (exists nb : list byte, length nb = 40%nat /\ rw_cells asegs m (a + 192) [CB 40 nb])
  /\ rw_cells asegs m (a + 232) [C8 (wz (a + 192)); C8 (wz 0)]
  /\ (exists pad2 : list byte, rw_cells asegs m (a + 248) [C8 (wz 32); C1 (b8 0); C1 (b8 0); C1 (b8 0); C1 (b8 0); C1 (b8 0); C1 (b8 0); CB 2 pad2])
     (* [comment removed for export] *)
  /\ rw_cells asegs m (a + 264) [C8 (wz (ps_depth ps))]
  /\ (exists j8 : list byte, length j8 = 8%nat /\ rw_cells asegs m (a + 272) [CB 8 j8])   (* [comment removed for export] *)
  /\ 0 <= ps_depth ps <= 32.

End HCW.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma blocks_items_app : ltac2:(zQ "60!r0!kmb!kna!ko3!iu0!hv8>1a@1$0$2>1b@1$0$2@3$5@1$0$4@1$1@3$3$2^2^1@3$3$4@1$1^2@1$1^1").
Proof. induction a; intros; cbn; [reflexivity|]. rewrite IHa, app_assoc. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma bj_statics_unfold {HCEIL : HeapCeil} : forall m, bj_statics m ->
     rw_cells asegs m 0x1b9da0 [C8 (wz 0x1adcf0)]
  /\ rw_cells asegs m 0x1adcf0 [C8 (wz 0xf5958); C8 (wz 0xf595c); C8 (wz 0xf5964); C8 (wz 0xf596c); C8 (wz 0xf5974)]
  /\ rw_cells asegs m 0x6f28c0 [C4 (wz 0); C4 (wz 0)]
  /\ (exists salt, rw_cells asegs m 0x6f28e0 [C4 (wz 0); C4 (wz 0); C8 salt])
  /\ rw_cells asegs m 0x1b9ce0 [C8 (wz 0x1ad8b0); C8 (wz 0xb9a9b9922177c772)]
  /\ rw_cells asegs m 0x1ad8e0 [C8 (wz 0xf6dc8)].
Proof. intros m H. exact H. Qed.

Lemma bj_statics_fold {HCEIL : HeapCeil} : forall m salt,
  rw_cells asegs m 0x1b9da0 [C8 (wz 0x1adcf0)] ->
  rw_cells asegs m 0x1adcf0 [C8 (wz 0xf5958); C8 (wz 0xf595c); C8 (wz 0xf5964); C8 (wz 0xf596c); C8 (wz 0xf5974)] ->
  rw_cells asegs m 0x6f28c0 [C4 (wz 0); C4 (wz 0)] ->
  rw_cells asegs m 0x6f28e0 [C4 (wz 0); C4 (wz 0); C8 salt] ->
  rw_cells asegs m 0x1b9ce0 [C8 (wz 0x1ad8b0); C8 (wz 0xb9a9b9922177c772)] ->
  rw_cells asegs m 0x1ad8e0 [C8 (wz 0xf6dc8)] ->
  bj_statics m.
Proof. intros. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [eexists; eassumption|]. split; assumption. Qed.

Ltac bj_statics_open BS :=
  let B1 := fresh "BS1" in let B2 := fresh "BS2" in let B3 := fresh "BS3" in
  let B4 := fresh "BS4" in let B5 := fresh "BS5" in let B6 := fresh "BS6" in let salt := fresh "salt" in
  destruct (bj_statics_unfold _ BS) as (B1 & B2 & B3 & (salt & B4) & B5 & B6); clear BS.
(* [comment removed for export] *)
