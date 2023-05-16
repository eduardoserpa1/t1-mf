class CircularQueue {
    var tamanho: int;
    var inicio: int;
    var fim: int;
    var elementos: array<int>;
    ghost var filaAbstrata: seq<int>;

    predicate valido() reads this, elementos {
        0 <= inicio < elementos.Length &&
        0 <= fim < elementos.Length &&
        0 <= tamanho <= elementos.Length 
    }

    constructor (cap: int)
    requires cap > 0
    ensures valido() && tamanho == 0
    {
        var newElementos := new int[cap];
        tamanho := 0;
        inicio := 0;
        fim := 0;
        elementos := newElementos;
        filaAbstrata := [];
    }

    method vazia() returns (vazia: bool)
    requires valido()
    ensures vazia <==> tamanho == 0
    {
        vazia := tamanho == 0;
    }

    method numero_elementos() returns (n: int)
        requires valido()
        ensures n == tamanho
    {
        n := tamanho;
    }

    method Contem(element: int) returns (contains: bool)
    requires valido()
    ensures elementos == old(elementos)
    ensures valido()
    {
        var i := 0;

        var pertence := false;

        while(i < tamanho)
        invariant 0 <= i <= tamanho <= elementos.Length; 
        invariant elementos == old(elementos)
        {
            if(elementos[(inicio + i) % elementos.Length] == element){
                pertence := true;
            }
            i := i + 1;
        }
        contains := pertence;
    }


    method adicionar(element: int)
    requires valido()
    modifies this
    ensures valido()
    ensures tamanho == old(tamanho) + 1
    {   
        var novoArray := new int[2 * elementos.Length];
        if (tamanho == elementos.Length) {
            var i := 0;
            while(i < tamanho) 
            invariant tamanho == old(tamanho);
            invariant 0 <= i <= tamanho <= elementos.Length < novoArray.Length; 
            {
                var index := inicio + i;

                novoArray[i] := elementos[index % elementos.Length];
                
                i := i + 1;
            }
            elementos := novoArray;
            inicio := 0;
            fim := tamanho;
            novoArray[fim] := element;
            fim := (fim + 1) % elementos.Length;
            tamanho := tamanho + 1;
            filaAbstrata := filaAbstrata + [element];
            elementos := novoArray;
        } else {
            var novoArray_igual := new int[elementos.Length];
            var i := 0;

            while(i < tamanho) 
            invariant tamanho == old(tamanho);
            invariant 0 <= i <= tamanho <= novoArray_igual.Length == elementos.Length;
            invariant 0 <= inicio < elementos.Length;
            invariant 0 <= fim < elementos.Length; 
            invariant tamanho < elementos.Length; 
            {
                novoArray_igual[i] := elementos[i];
                i := i + 1;
            }
           
            novoArray_igual[fim] := element;
            fim := (fim + 1) % novoArray_igual.Length;
            tamanho := tamanho + 1;  
            filaAbstrata := filaAbstrata + [element];
            elementos := novoArray_igual;
        }
        
    }

    method remover() returns (valorRemovido: int)
    requires valido()
    requires tamanho > 0
    modifies this
    ensures valido()
    ensures tamanho == old(tamanho) - 1
    ensures 0 <= old(inicio) < elementos.Length
    {
        var novoArray_igual := new int[elementos.Length];
        var i := 0;

        valorRemovido := elementos[inicio];

        while(i < tamanho) 
        invariant tamanho == old(tamanho);
        invariant 0 <= i <= tamanho <= novoArray_igual.Length == elementos.Length;
        invariant 0 <= inicio < elementos.Length;
        invariant 0 <= fim < elementos.Length; 
        {
            if(i != inicio){
                novoArray_igual[i] := elementos[i];
            }
            i := i + 1;
        }

        //filaAbstrata := filaAbstrata - [elementos[inicio]];
        inicio := (inicio + 1) % elementos.Length;
        tamanho := tamanho - 1;
        elementos := novoArray_igual;
    }    
}

method main()
{
    var fila := new CircularQueue(5);
    var tamanho := fila.numero_elementos();
    var vazia := fila.vazia();

    assert tamanho == 0;
   
    assert vazia;
    
    fila.adicionar(1);
    fila.adicionar(2);
    fila.adicionar(3);

    var tamanho_depois_de_adicionar := fila.numero_elementos();
    var vazia_depois_de_adicionar := fila.vazia();
    var contem := fila.Contem(2);

    assert tamanho_depois_de_adicionar == 3;
    assert !vazia_depois_de_adicionar;
    //assert contem;

    var valor_removido := fila.remover();
    valor_removido := fila.remover();
    var tamanho_depois_de_remover := fila.numero_elementos();

    assert tamanho_depois_de_remover == 1;
    //assert valor_removido == 2;
}

/*

x Realizar a concatenação de duas filas, retornando uma nova fila como resultado, sem 
alterar as filas originais.

(funcionando) Retornar o número de elementos da fila.
(funcionando) Adicionar um novo elemento na fila.
(funcionando) Verificar se a fila é vazia ou não.
(funcionando) Construtor deve instanciar uma fila vazia.

x(funcionando, porém não prova o elemento removido) Remover um elemento da fila e retornar seu valor caso a fila contenha elementos.
x(testar, fazer pós condição) Verificar se um determinado elemento pertence o não a fila.


*/