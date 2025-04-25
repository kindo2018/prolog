# prologを用いた抽象的社会選択関数における耐戦略性の実験

[このリポジトリ](https://github.com/kindo2018/prolog/)には犬童(2025)内に掲載されている実験を再現するソースコードが含まれています。このコードは論文内でも記述されており，論文内のほぼすべての結果を再現するために使用できます．
このREADMEは、GitHubリポジトリに掲載する論文[1]のソースコードとその使い方を簡単に説明し、読者が手軽に試せるように設計されています。
なおgraphvizを使った視覚化の部分（fig8(G), fig10(G)など）はSWISH上で再現できます．

[1]犬童 健良(2025). 論理プログラミングを用いた抽象的社会選択関数における耐戦略性の実験的研究.関東学園大学経済学紀要,51,1-64. KENRYO INDO(2025). Experimental Study of Strategy-Proofness in Abstract Social Choice Functions Using Logic Programming. Research Bulletin of Economics, Kanto Gakuen University, 51, 1-64. (Japanese) DOI:
[https://doi.org/10.20589/kantogakueneconomics.51.0_1](https://doi.org/10.20589/kantogakueneconomics.51.0_1)

## 概要

本リポジトリには以下の内容が含まれています：
- **論文に記載された完全なコード（サンプル実行のデモを含む）**: logical_scf.pl
- **実行環境の設定手順**: SWI-Prologを活用した実行環境の簡単なセットアップ:本ファイル
- **[SWISHノートブック](https://swish.swi-prolog.org/p/MQQYngUl.swinb)のコピーのコピー**:MQQYngUl.swinb.txt. 

---
## 使い方

- **[SWISH上ですぐ実行](https://swish.swi-prolog.org/p/saPQDdZf.pl).**
- logical_scf.plをダウンロードしてローカルインストールされたswi-prologで実行できます．
- あるいは以下の手順に従ってCodespace上（あるいはColaboratoryのターミナルでもほぼ同様に）でコードを試すことができます。

### 1. **リポジトリをクローン**
まず、このリポジトリをローカル環境またはCodespaceにクローンしてください：
```bash
git clone https://github.com/kindo2018/prolog
```

### 2. **Codespacesでのセットアップ**
GitHub Codespacesを使用してクラウド環境で試す場合、以下の手順を参考にしてください：
1. リポジトリページで「+」をクリックし、`Codespaces`タブを選択。
2. 「Create codespace on main」をクリックして、新しいCodespaceを作成。
3. 作成されたCodespaces内で、以下のコマンドを実行してSWI-Prologをセットアップ：
   ```bash
   sudo apt update
   sudo apt install swi-prolog
   swipl --version  # インストール確認
   ```

### 3. **コードの実行**
1. Prologファイルをエディタで開きます
2. 次のようにターミナルからコードを実行します：
   ```bash
   swipl -s logical_scf.pl
   ```

### 4. **クエリを実行**
対話モードでPrologクエリを試してください：
```prolog
?- fig1.
```

---

## ライセンス

このコードは[MITライセンス](LICENSE)のもとで提供されています。詳細はLICENSEファイルをご確認ください。
